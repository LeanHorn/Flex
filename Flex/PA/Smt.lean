import Flex.PA.Check
import Flex.CHC.Export
import Flex.CHC.Process

namespace Flex.PA

open Lean Meta Elab Term

private def unknowns (count : Nat) (reason : String) : Array PASynthResult :=
  Array.replicate count (.unknown reason)

private structure Batch where
  script : String
  indices : Array Nat
  results : Array PASynthResult
  omittedAssumptions : Bool

private def buildBatch (queries : Array Expr) (timeoutMs : Nat) : MetaM Batch := do
  let mut assumptions := #[]
  let mut omittedAssumptions := false
  for declaration in (← getLCtx) do
    if ← isProp declaration.type then
      try
        let assumption ← CHC.Prepare.atom (← zetaReduce (← instantiateMVars declaration.type)) true
        for id in (collectFVars {} assumption).fvarIds do
          discard <| CHC.Fragment.valueSort (← inferType (mkFVar id))
        assumptions := assumptions.push assumption
      catch error =>
        if error.isInterrupt then throw error
        omittedAssumptions := true
    else
      try discard <| CHC.Fragment.valueSort declaration.type
      catch error =>
        if error.isInterrupt then throw error
        -- A local value of an unsupported type may witness an empty type.
        omittedAssumptions := true
  let mut results := unknowns queries.size "unsupported query"
  let mut supported := #[]
  for query in queries, i in [:queries.size] do
    try
      for id in (collectFVars {} query).fvarIds do
        discard <| CHC.Fragment.valueSort (← inferType (mkFVar id))
      supported := supported.push (i, query)
    catch error =>
      if error.isInterrupt then throw error
      results := results.set! i (.unknown (← error.toMessageData.toString))
  let mut variables := #[]
  for expression in supported.map (·.2) ++ assumptions do
    for id in (collectFVars {} expression).fvarIds do
      let input := mkFVar id
      unless variables.contains input do variables := variables.push input
  let mut names : Std.HashMap FVarId String := {}
  let mut script := s!"(set-option :print-success false)\n(set-option :produce-models false)\n(set-option :produce-proofs false)\n(set-option :produce-unsat-cores false)\n(set-option :timeout {timeoutMs})\n(set-logic ALL)\n"
  for input in variables, i in [:variables.size] do
    let sort ← CHC.Fragment.valueSort (← inferType input)
    let name := s!"pa_{i}"
    names := names.insert input.fvarId! name
    let sort := match sort with | .int => "Int" | .bool => "Bool"
    script := script ++ s!"(declare-const {name} {sort})\n"
  let symbols := variables.map fun input => names[input.fvarId!]!
  let translate (expression : Expr) : MetaM Smt.Term := do
    let expression ← CHC.Prepare.atom expression true
    unless ← isProp expression do throwError "PA SMT: expected a proposition"
    let ((term, constants, freeVariables), _) ←
      (Smt.Translator.translateExpr expression).run { uniqueFVarNames := names }
    unless constants.isEmpty && freeVariables.toArray.all names.contains do
      throwError "PA SMT: unsupported constant or free-input dependencies"
    CHC.Fragment.checkTerm term symbols true
    return term
  for assumption in assumptions do
    try script := script ++ s!"(assert {← translate assumption})\n"
    catch error =>
      if error.isInterrupt then throw error
      omittedAssumptions := true
  let mut indices := #[]
  for (i, query) in supported do
    try
      let term ← translate query
      script := script ++ s!"(push 1)\n(assert (not {term}))\n(check-sat)\n(pop 1)\n"
      indices := indices.push i
    catch error =>
      if error.isInterrupt then throw error
      results := results.set! i (.unknown (← error.toMessageData.toString))
  return { script := script ++ "(exit)\n", indices, results, omittedAssumptions }

/-- Reject extra, missing, or malformed responses rather than guessing their query positions. -/
private def parseResponses (output : String) (count : Nat) : Except String (Array PASynthResult) := do
  let lines := (output.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  unless lines.length == count do throw "unexpected number of SMT responses"
  lines.toArray.mapM fun line => match line with
    | "unsat" => pure .valid
    | "sat" => pure .invalid
    | "unknown" => pure (.unknown "solver returned unknown")
    | _ => throw s!"unexpected SMT response: {line}"

/-- Check a batch using one bounded Z3 process. Results guide synthesis only;
the selected predicates still require independent Lean certification. -/
def smtOracle (timeoutMs : Nat := 2000) : PASynthOracle := fun queries => do
  if queries.isEmpty then return #[]
  if timeoutMs == 0 then return unknowns queries.size "SMT timeout must be positive"
  withNewMCtxDepth do
    let saved ← saveState
    try
      let queries ← queries.mapM fun query => do zetaReduce (← instantiateMVars query)
      if queries.any (fun q => q.hasMVar || q.hasLooseBVars) then
        return unknowns queries.size "unresolved metavariable or loose binder"
      let batch ← CHC.Fragment.withTranslators (buildBatch queries timeoutMs) true
      if batch.indices.isEmpty then return batch.results
      Core.checkInterrupted
      let response ← CHC.Process.run {
        executable := "z3", args := #["-in", "-smt2"], timeoutMs } batch.script
      Core.checkInterrupted
      let answers := match response.completion with
        | .exited 0 => parseResponses response.stdout batch.indices.size
        | .timedOut => .error "SMT batch timed out"
        | .spawnError message | .ioError message => .error message
        | .exited code => .error s!"SMT process exited with code {code}"
      let mut results := batch.results
      match answers with
      | .ok answers =>
        for i in [:batch.indices.size] do
          let answer := match answers[i]! with
            | .invalid => if batch.omittedAssumptions then
                .unknown "SMT omitted unsupported local assumptions" else .invalid
            | answer => answer
          results := results.set! batch.indices[i]! answer
      | .error reason =>
        for index in batch.indices do results := results.set! index (.unknown reason)
      return results
    catch error =>
      if error.isInterrupt then throw error
      return unknowns queries.size (← error.toMessageData.toString)
    finally
      set saved.elab
      CHC.restoreMetaState saved.meta

end Flex.PA
