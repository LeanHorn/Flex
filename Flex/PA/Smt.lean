import Flex.PA.Check
import Flex.CHC.Process
import Flex.CHC.Export
import Flex.SMT.Encode
import Flex.Fusion.Flatten

register_option flex.automation.sourcePredicates : Bool := {
  defValue := false
  descr := "Expose nonrecursive source predicates and pointwise function equalities in PA proofs."
}

namespace Flex.PA

open Lean Meta Elab Term

private def unknowns (count : Nat) (reason : String) : Array PASynthResult :=
  Array.replicate count (.unknown reason)

/-- Reject extra, missing, or malformed responses rather than guessing their query positions. -/
private def parseResponses (output : String) (count : Nat) : Except String (Array PASynthResult) := do
  let lines := (output.splitOn "\n").map (·.trimAscii.toString) |>.filter (!·.isEmpty)
  unless lines.length == count do throw "unexpected number of SMT responses"
  lines.toArray.mapM fun line => match line with
    | "unsat" => pure .valid
    | "sat" => pure .invalid
    | "unknown" => pure (.unknown "solver returned unknown")
    | line =>
      if line.startsWith "unknown (" && line.endsWith ")" then
        pure (.unknown "solver returned unknown")
      else throw s!"unexpected SMT response: {line}"

/-- On timeout, preserve complete responses and leave unfinished queries unknown. -/
def decodeSmtResponses (response : CHC.Process.Result) (count : Nat)
    : Except String (Array PASynthResult) := do
  match response.completion with
  | .exited 0 => parseResponses response.stdout count
  | .timedOut =>
    unless response.stderr.trimAscii.isEmpty do throw "SMT timeout with diagnostics"
    let lines := response.stdout.splitOn "\n"
    let tail := (lines.getLast?.getD "").trimAscii.toString
    unless ["sat", "unsat", "unknown"].any (·.startsWith tail) do
      throw "malformed incomplete SMT response"
    let complete := lines.dropLast |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty)
    if complete.length > count || (complete.length == count && !tail.isEmpty) then
      throw "extra SMT responses"
    let answers ← parseResponses ("\n".intercalate complete) complete.length
    return answers ++ unknowns (count - answers.size) "SMT batch timed out"
  | .spawnError message | .ioError message => throw message
  | .exited code => throw s!"SMT process exited with code {code}"

/-- Open binders and premises shared by every query in the batch. Proof-dependent or
diverging prefixes are left in the queries for the encoder. -/
private partial def withSharedPrefix (queries : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → MetaM α) : MetaM α :=
  go queries #[] #[]
where
  go (queries inputs premises : Array Expr) : MetaM α := do
    let queries ← queries.mapM fun q => do return (← instantiateMVars q).consumeMData.headBeta
    let some (Expr.forallE name domain _ bi) := queries[0]? | k inputs premises queries
    unless queries.all (fun e => e.isForall && e.bindingDomain! == domain) do
      return ← k inputs premises queries
    if ← isProp domain then
      if queries.any (fun e => e.bindingBody!.hasLooseBVar 0) then
        return ← k inputs premises queries
      withLocalDecl name bi domain fun proof =>
        go (queries.map (·.bindingBody!.instantiate1 proof)) inputs (premises.push domain)
    else
      withLocalDecl name bi domain fun input =>
        go (queries.map (·.bindingBody!.instantiate1 input)) (inputs.push input) premises

private structure Batch where
  script : String
  /-- Queries sent to the solver, in order. -/
  indices : Array Nat
  /-- Whether each sent query's encoding abstracts, so that `sat` is inconclusive. -/
  abstracted : Array Bool
  results : Array PASynthResult
  deriving Inhabited

/-- Encode the batch: shared facts once, then one `push`/`pop` block per query. Facts that
cannot be encoded are omitted, which keeps `unsat` valid but makes `sat` inconclusive. -/
private def buildBatch (queries : Array Expr) (timeoutMs : Nat) (config : SMT.Config)
    : MetaM Batch := do
  let mut facts := #[]
  let mut dataTypes := #[]
  let mut incomplete := false
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isProp decl.type then
      let type ← zetaReduce (← instantiateMVars decl.type)
      if type.hasMVar then incomplete := true else facts := facts.push type
    else if decl.value?.isNone then
      dataTypes := dataTypes.push decl.type
  withSharedPrefix queries fun inputs premises conclusions => SMT.EncodeM.run' config do
    -- The shared part abstracts when anything in it does: a fact with metavariables, a variable
    -- of an unencodable (possibly empty) type that could make every query vacuous, an omitted
    -- fact, or an abstraction inside an encoded one.
    if incomplete then modify fun s => { s with abstracted := true }
    for type in dataTypes ++ (← inputs.mapM fun x => inferType x) do
      try discard <| SMT.encodeSort type
      catch error =>
        if error.isInterrupt then throw error
        modify fun s => { s with abstracted := true }
    let mut assertions := #[]
    for fact in facts ++ premises do
      for conjunct in SMT.conjuncts fact do
        try
          let encoded ← SMT.withPolarity .pos (SMT.encode conjunct)
          assertions := assertions.push s!"(assert {encoded})"
        catch error =>
          if error.isInterrupt then throw error
          trace[flex.smt] "omitted fact: {error.toMessageData}"
          modify fun s => { s with abstracted := true }
    let abstracted := (← get).abstracted
    let mut results := unknowns queries.size "unsupported query"
    let mut blocks := #[]
    let mut indices := #[]
    let mut queryAbstracted := #[]
    for conclusion in conclusions, i in [:conclusions.size] do
      modify fun s => { s with abstracted := false }
      try
        -- The rest of the clause: its own variables, premises and head.
        let (clausePremises, head) ← SMT.encodeClause conclusion
        let commands := clausePremises.map (s!"(assert {·})") |>.push s!"(assert (not {head}))"
        blocks := blocks.push s!"(push 1)\n{"\n".intercalate commands.toList}\n(check-sat)\n(pop 1)"
        indices := indices.push i
        queryAbstracted := queryAbstracted.push (abstracted || (← get).abstracted)
      catch error =>
        if error.isInterrupt then throw error
        results := results.set! i (.unknown (← error.toMessageData.toString))
    let state ← get
    let header := s!"(set-option :print-success false)\n(set-option :produce-models false)\n\
      (set-option :timeout {timeoutMs})\n(set-logic ALL)"
    let script := "\n".intercalate
      ([header] ++ state.declarations.toList ++ state.axioms.toList ++ assertions.toList ++
        blocks.toList ++ ["(exit)\n"])
    return { script, indices, abstracted := queryAbstracted, results }

/-- Check a batch of clauses with one bounded z3 process. -/
private def clauseOracle (timeoutMs : Nat) : PASynthOracle := fun queries => do
  if queries.isEmpty then return #[]
  if timeoutMs == 0 then return unknowns queries.size "SMT timeout must be positive"
  let config := SMT.Config.ofOptions (← getOptions)
  withNewMCtxDepth do
    let saved ← saveState
    try
      let queries ← queries.mapM fun query => do zetaReduce (← instantiateMVars query)
      if queries.any (fun q => q.hasMVar || q.hasLooseBVars) then
        return unknowns queries.size "unresolved metavariable or loose binder"
      let batch ← buildBatch queries timeoutMs config
      if batch.indices.isEmpty then return batch.results
      trace[flex.smt] "script:\n{batch.script}"
      Core.checkInterrupted
      let response ← CHC.Process.run {
        executable := "z3", args := #["-in", "-smt2"], timeoutMs } batch.script
      Core.checkInterrupted
      let mut results := batch.results
      match decodeSmtResponses response batch.indices.size with
      | .ok answers =>
        for answer in answers, index in batch.indices, abstracted in batch.abstracted do
          let answer := match answer with
            | .invalid => if abstracted then .unknown "SMT encoding abstracted the query" else .invalid
            | answer => answer
          results := results.set! index answer
      | .error reason =>
        trace[flex.smt] "solver failed: {reason}\n{response.stderr}"
        for index in batch.indices do results := results.set! index (.unknown reason)
      return results
    catch error =>
      if error.isInterrupt then throw error
      return unknowns queries.size (← error.toMessageData.toString)
    finally
      set saved.elab
      CHC.restoreMetaState saved.meta

/-- Check a batch with one bounded z3 process and the exact encoding of `Flex.SMT`.
Each query is first flattened into clauses (conjunctions of conclusions split, universals
distributed): a query is valid when all its clauses are, and invalid when one of them has an
exact counterexample. Results guide synthesis only; selected predicates still
require Lean certification. -/
def smtOracle (timeoutMs : Nat := 2000) : PASynthOracle := fun queries => do
  if queries.isEmpty then return #[]
  let mut clauses := #[]
  let mut owners : Array (Array Nat) := #[]
  for query in queries do
    let flat? ← try
        let flat ← (exprFlat (← instantiateMVars query) pure).run { kvars := {} }
        pure (some flat.toArray)
      catch error =>
        if error.isInterrupt then throw error
        pure none
    match flat? with
    | some flat =>
      owners := owners.push (Array.range' clauses.size flat.size)
      clauses := clauses ++ flat
    | none =>
      -- Unflattenable queries are checked as they are.
      owners := owners.push #[clauses.size]
      clauses := clauses.push query
  let answers ← clauseOracle timeoutMs clauses
  return owners.map fun indices => Id.run do
    let parts := indices.map (answers[·]!)
    if parts.any (· == .invalid) then return .invalid
    if let some unknown := parts.find? (· != .valid) then return unknown
    return .valid

private partial def isFirstOrderInput (type : Expr) : MetaM Bool := do
  let type ← whnf type
  if type.isConstOf ``Int || type.isConstOf ``Bool || type == mkSort .zero then return true
  if let .forallE _ domain body _ := type then
    if body.hasLooseBVars then return false
    return (← isFirstOrderInput domain) && (← isFirstOrderInput body)
  return false

/-- Scalar and function-valued record fields occurring outside local binders. -/
def recordFields (expressions : Array Expr) : MetaM (Array Expr) := do
  let fields ← IO.mkRef (#[] : Array Expr)
  for expression in expressions do
    expression.forEach fun e => do
      if e.hasLooseBVars || !e.hasFVar then return
      let projection ← match e with
        | .proj name _ _ => pure (!(isClass (← getEnv) name))
        | _ => match e.getAppFn with
          | .const name _ =>
            pure ((← getProjectionFnInfo? name).any fun info =>
              !info.fromClass && e.getAppNumArgs == info.numParams + 1)
          | _ => pure false
      if projection && (← isFirstOrderInput (← inferType e)) then
        unless (← fields.get).contains e do fields.modify (·.push e)
  fields.get

/-- Expose nonrecursive source predicates, preserving theory operations and recursive calls. -/
def unfoldSourcePredicates (expression : Expr) : MetaM Expr := do
  let fuel ← IO.mkRef 64
  Meta.transform expression (pre := fun e => do
    if (← fuel.get) == 0 then return .done e
    let .const name _ := e.getAppFn | return .continue
    let .defnInfo _ ← getConstInfo name | return .continue
    let env ← getEnv
    if let some index := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[index.toNat]!
      if #[`Init, `Lean, `Std, `Mathlib, `Auto, `Smt, `Aesop, `Flex].any (·.isPrefixOf mod) then
        return .continue
    unless ← isProp e do return .continue
    if ← isRecursiveDefinition name then return .continue
    if let some unfolded ← unfoldDefinition? e then
      fuel.modify (· - 1)
      return .visit unfolded
    return .continue)

end Flex.PA
