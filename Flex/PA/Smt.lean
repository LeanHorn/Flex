import Flex.PA.Check
import Flex.CHC.Export
import Flex.CHC.Process
import Smt

namespace Flex.PA

open Lean Meta Elab Term

private def unknowns (count : Nat) (reason : String) : Array PASynthResult :=
  Array.replicate count (.unknown reason)

/-- Open only binders and premises shared by every query in the batch. -/
private partial def withSharedPrefix (queries : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → MetaM α) (scalars : Bool := true) : MetaM α :=
  go queries #[] #[]
where
  go (queries variables premises : Array Expr) : MetaM α := do
    let queries ← queries.mapM CHC.Prepare.expose
    let some (Expr.forallE name domain _ bi) := queries[0]?
      | k variables premises queries
    unless queries.all (fun e => e.isForall && e.bindingDomain! == domain) do
      return ← k variables premises queries
    if ← isProp domain then
      if queries.any (fun e => e.bindingBody!.hasLooseBVar 0) then
        throwError "PA SMT: proof-dependent premises are unsupported"
      withLocalDecl name bi domain fun proof =>
        go (queries.map (·.bindingBody!.instantiate1 proof)) variables (premises.push domain)
    else
      if scalars then discard <| CHC.Fragment.valueSort domain
      let domain ← if scalars then pure domain else whnf domain
      withLocalDecl name bi domain fun input =>
        go (queries.map (·.bindingBody!.instantiate1 input)) (variables.push input) premises

private structure Batch where
  script : String
  indices : Array Nat
  results : Array PASynthResult
  omittedAssumptions : Bool
  deriving Inhabited

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
  withSharedPrefix queries fun variables premises conclusions => do
    let mut omittedAssumptions := omittedAssumptions
    let mut results := unknowns queries.size "unsupported query"
    let mut supported := #[]
    for conclusion in conclusions, i in [:conclusions.size] do
      try
        for id in (collectFVars {} conclusion).fvarIds do
          discard <| CHC.Fragment.valueSort (← inferType (mkFVar id))
        supported := supported.push (i, conclusion)
      catch error =>
        if error.isInterrupt then throw error
        results := results.set! i (.unknown (← error.toMessageData.toString))
    let mut variables := variables
    for expression in premises ++ supported.map (·.2) ++ assumptions do
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
    -- The context and symbol mapping stay fixed for this batch. Commit only
    -- checked translations, so a rejected candidate cannot contaminate the cache.
    let translation ← IO.mkRef ({ uniqueFVarNames := names } : Smt.TranslationM.State)
    let terms ← IO.mkRef ({} : ExprMap Smt.Term)
    let translate (input : Expr) : MetaM Smt.Term := do
      if let some term := (← terms.get)[input]? then return term
      let expression ← CHC.Prepare.atom input true
      unless ← isProp expression do throwError "PA SMT: expected a proposition"
      let ((term, constants, freeVariables), next) ←
        (Smt.Translator.translateExpr expression).run (← translation.get)
      unless constants.isEmpty && freeVariables.toArray.all names.contains do
        throwError "PA SMT: unsupported constant or free-input dependencies"
      CHC.Fragment.checkTerm term symbols true
      translation.set next
      terms.modify (·.insert input term)
      return term
    for premise in premises do
      script := script ++ s!"(assert {← translate premise})\n"
    for assumption in assumptions do
      try script := script ++ s!"(assert {← translate assumption})\n"
      catch error =>
        if error.isInterrupt then throw error
        omittedAssumptions := true
    let mut indices := #[]
    for (i, conclusion) in supported do
      try
        let term ← translate conclusion
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

/-- Expose definitional wrappers without unfolding arithmetic operations. -/
def unfoldAbbreviations (expression : Expr) : MetaM Expr :=
  Meta.transform expression (pre := fun e => do
    if let .const name _ := e.getAppFn then
      if (← getProjectionFnInfo? name).isSome then return .continue
      if let .defnInfo info ← getConstInfo name then
        if info.hints == .abbrev then
          if let some unfolded ← unfoldDefinition? e then return .visit unfolded
    return .continue)

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

/-- Record fields become shared free inputs, an overapproximation used only for synthesis. -/
private def withRecordFields [Inhabited α] (expressions : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  let fields ← recordFields expressions
  let declarations ← fields.mapIdxM fun i e =>
    return (Name.mkSimple s!"pa_field_{i}", ← whnf (← inferType e))
  withLocalDeclsDND declarations fun inputs => do
    let replacements := (fields.zip inputs).foldl (init := ({} : ExprMap Expr)) fun m (e, input) =>
      m.insert e input
    k (expressions.map fun e => e.replace replacements.get?)

private partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg!
  else #[e]

/-- Simplify shared assumptions once and name each conclusion with a Boolean flag.
The ordinary lean-smt translator supplies declarations for functions and datatypes. -/
private def buildRichBatch (queries : Array Expr) (timeoutMs : Nat) : MetaM Batch := do
  withSharedPrefix queries (fun _ premises conclusions => do
    let context ← Simp.mkContext { maxSteps := 10000, failIfUnchanged := false }
      #[← getSimpTheorems] (← getSimpCongrTheorems)
    let simprocs := #[← Simp.getSimprocs]
    let simplify (e : Expr) : MetaM Expr := do
      unfoldAbbreviations (← Meta.simp (← instantiateMVars e) context simprocs).1.expr
    let mut assumptions := premises
    for declaration in ← getLCtx do
      if !declaration.isImplementationDetail && (← isProp declaration.type) then
        let type ← instantiateMVars declaration.type
        unless type.hasMVar || assumptions.contains type do
          assumptions := assumptions.push type
    assumptions ← assumptions.mapM simplify
    assumptions := assumptions.flatMap conjuncts
    let conclusions ← conclusions.mapM simplify
    withRecordFields (assumptions ++ conclusions) fun expressions => do
    let assumptions := expressions.extract 0 assumptions.size
    let conclusions := expressions.extract assumptions.size expressions.size
    let flags := conclusions.mapIdx fun i _ => (Name.mkSimple s!"pa_answer_{i}", mkSort .zero)
    withLocalDeclsDND flags fun flags => do
      let equations ← flags.zipWithM mkEq conclusions
      let facts := (assumptions ++ equations).mapIdx fun i p =>
        (Name.mkSimple s!"pa_fact_{i}", p)
      withLocalDeclsDND facts fun facts => do
        let (names, _) ← Smt.genUniqueFVarNames
        let mut graph : Smt.Translate.Query.QueryBuilderM.State := {}
        let mut translation : Smt.TranslationM.State := { uniqueFVarNames := names }
        let mut roots := #[]
        let mut indices := #[]
        let mut results := unknowns queries.size "simplified SMT query inconclusive"
        -- Commit complete dependency closures only; a rejected fact cannot poison its neighbours.
        for fact in facts, i in [:facts.size] do
          let saved ← Meta.saveState
          try
            let ((_, nextGraph), nextTranslation) ←
              Smt.Translate.Query.QueryBuilderM.buildDependencyGraph
                |>.run { toProcess := [fact] }
                |>.run graph
                |>.run translation
            graph := nextGraph
            translation := nextTranslation
            roots := roots.push fact
            if i >= assumptions.size then indices := indices.push (i - assumptions.size)
          catch error =>
            if error.isInterrupt then throw error
            let reason ← error.toMessageData.toString
            CHC.restoreMetaState saved
            if i >= assumptions.size then
              results := results.set! (i - assumptions.size) (.unknown reason)
        let (_, commands) ← StateT.run
          (graph.graph.orderedDfs roots.toList (Smt.Translate.Query.emitVertex graph.commands)) []
        let mut script := s!"(set-option :print-success false)\n(set-option :produce-proofs false)\n(set-option :timeout {timeoutMs})\n(set-logic ALL)\n"
        script := script ++ Smt.Translate.Command.cmdsAsQuery commands.reverse ++ "\n"
        for index in indices do
          let name := Smt.Term.quoteSymbol names[flags[index]!.fvarId!]!
          script := script ++ s!"(push 1)\n(assert (not {name}))\n(check-sat)\n(pop 1)\n"
        return {
          script := script ++ "(exit)\n"
          indices, results
          omittedAssumptions := true })
    (scalars := false)

/-- A bounded, decision-only retry after simplification. SAT remains inconclusive:
unfolding may leave fixed Lean functions uninterpreted in the SMT approximation. -/
def simplifiedSmtOracle (timeoutMs : Nat := 2000) : PASynthOracle := fun queries => do
  if queries.isEmpty then return #[]
  if timeoutMs == 0 then return unknowns queries.size "SMT timeout must be positive"
  withNewMCtxDepth do
    let saved ← saveState
    try
      let queries ← queries.mapM fun query => do zetaReduce (← instantiateMVars query)
      if queries.any (fun q => q.hasMVar || q.hasLooseBVars) then
        return unknowns queries.size "unresolved metavariable or loose binder"
      let batch ← buildRichBatch queries timeoutMs
      if batch.indices.isEmpty then return batch.results
      Core.checkInterrupted
      let response ← CHC.Process.run {
        executable := "z3", args := #["-in", "-smt2"], timeoutMs } batch.script
      Core.checkInterrupted
      let answers := match response.completion with
        | .exited 0 => parseResponses response.stdout batch.indices.size
        | .timedOut => .error "simplified SMT batch timed out"
        | .spawnError message | .ioError message => .error message
        | .exited code => .error s!"simplified SMT exited with code {code}: {response.stdout} {response.stderr}"
      let mut results := batch.results
      match answers with
      | .ok answers =>
          for answer in answers, index in batch.indices do
            if answer == .valid then results := results.set! index .valid
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
