import Flex.PA.Check
import Flex.CHC.Export
import Flex.PA.Observation
import Flex.CHC.Process
import Smt
import Flex.Simproc.ExistsAndEq

register_option flex.automation.sourcePredicates : Bool := {
  defValue := false
  descr := "Expose nonrecursive source predicates and pointwise function equalities in PA queries."
}

namespace Flex.PA

open Lean Meta Elab Term

private def unknowns (count : Nat) (reason : String) : Array PASynthResult :=
  Array.replicate count (.unknown reason)

/-- Open only binders and premises shared by every query in the batch. -/
private partial def withSharedPrefix (queries : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → MetaM α) (scalars : Bool := true) : MetaM α :=
  go queries #[] #[]
where
  go (queries inputs premises : Array Expr) : MetaM α := do
    let queries ← queries.mapM CHC.Prepare.expose
    let some (Expr.forallE name domain _ bi) := queries[0]?
      | k inputs premises queries
    unless queries.all (fun e => e.isForall && e.bindingDomain! == domain) do
      return ← k inputs premises queries
    if ← isProp domain then
      if queries.any (fun e => e.bindingBody!.hasLooseBVar 0) then
        throwError "PA SMT: proof-dependent premises are unsupported"
      withLocalDecl name bi domain fun proof =>
        go (queries.map (·.bindingBody!.instantiate1 proof)) inputs (premises.push domain)
    else
      if scalars then discard <| CHC.Fragment.valueSort domain
      let domain ← if scalars then pure domain else whnf domain
      withLocalDecl name bi domain fun input =>
        go (queries.map (·.bindingBody!.instantiate1 input)) (inputs.push input) premises

private structure Batch where
  script : String
  indices : Array Nat
  results : Array PASynthResult
  omittedAssumptions : Bool
  deriving Inhabited

/-- SMT signature of a free input: a scalar constant, or a first-order uninterpreted function
over scalars such as Liquid Fixpoint's defunctionalized `apply`. Lean's function space is
exactly an SMT uninterpreted function, so declaring it keeps `sat` answers conclusive. -/
private def inputSignature (type : Expr) : MetaM (Array CHC.ValueSort × CHC.ValueSort) :=
  forallTelescopeReducing type fun parameters result => do
    let arguments ← parameters.mapM fun parameter => do
      CHC.Fragment.valueSort (← inferType parameter)
    return (arguments, ← CHC.Fragment.valueSort result)

private def sortName : CHC.ValueSort → String
  | .int => "Int" | .bool => "Bool"

/-- Declared functions must be applied to exactly their declared arguments. A partial
application (e.g. `f x : SmtMap Int Int` for `f : Int → SmtMap Int Int`) or a function used
as a value is not first-order SMT: z3 rejects the command and the batch's exit status. -/
private partial def fullyApplied (arities : Std.HashMap String Nat) : Smt.Term → Bool
  | .symbolT name => arities.getD name 0 == 0
  | .appT f x =>
    let rec spine : Smt.Term → Nat → Option (String × Nat)
      | .appT g _, n => spine g (n + 1)
      | .symbolT name, n => some (name, n)
      | _, _ => none
    let rec args : Smt.Term → Array Smt.Term → Array Smt.Term
      | .appT g y, acc => args g (#[y] ++ acc)
      | _, acc => acc
    let headOk := match spine (.appT f x) 0 with
      | some (name, n) => arities.getD name n == n
      | none => fullyApplied arities f
    headOk && (args (.appT f x) #[]).all (fullyApplied arities)
  | .forallT _ _ body | .existsT _ _ body => fullyApplied arities body
  | .letT _ value body => fullyApplied arities value && fullyApplied arities body
  | _ => true

private def buildBatch (queries : Array Expr) (timeoutMs : Nat) : MetaM Batch := do
  let mut assumptions := #[]
  let mut omittedAssumptions := false
  for declaration in (← getLCtx) do
    -- Auxiliary declarations (e.g. an `example`'s recursive reference) are not hypotheses.
    if declaration.isImplementationDetail then continue
    if ← isProp declaration.type then
      try
        let assumption ← zetaReduce (← instantiateMVars declaration.type)
        for id in (collectFVars {} assumption).fvarIds do
          discard <| inputSignature (← inferType (mkFVar id))
        assumptions := assumptions.push (← CHC.Prepare.atom assumption true)
      catch error =>
        if error.isInterrupt then throw error
        omittedAssumptions := true
    else
      try discard <| inputSignature declaration.type
      catch error =>
        if error.isInterrupt then throw error
        -- A local value of an unsupported type may witness an empty type.
        omittedAssumptions := true
  withSharedPrefix queries fun inputs premises conclusions => do
    let mut omittedAssumptions := omittedAssumptions
    let mut results := unknowns queries.size "unsupported query"
    let mut supported := #[]
    for conclusion in conclusions, i in [:conclusions.size] do
      try
        for id in (collectFVars {} conclusion).fvarIds do
          discard <| inputSignature (← inferType (mkFVar id))
        supported := supported.push (i, conclusion)
      catch error =>
        if error.isInterrupt then throw error
        results := results.set! i (.unknown (← error.toMessageData.toString))
    let mut inputs := inputs
    for expression in premises ++ supported.map (·.2) ++ assumptions do
      for id in (collectFVars {} expression).fvarIds do
        let input := mkFVar id
        unless inputs.contains input do inputs := inputs.push input
    let mut names : Std.HashMap FVarId String := {}
    let mut arities : Std.HashMap String Nat := {}
    let mut script := s!"(set-option :print-success false)\n(set-option :produce-models false)\n(set-option :produce-proofs false)\n(set-option :produce-unsat-cores false)\n(set-option :timeout {timeoutMs})\n(set-logic ALL)\n"
    for input in inputs, i in [:inputs.size] do
      let (arguments, result) ← inputSignature (← inferType input)
      let name := s!"pa_{i}"
      names := names.insert input.fvarId! name
      arities := arities.insert name arguments.size
      script := script ++ if arguments.isEmpty then s!"(declare-const {name} {sortName result})\n"
        else s!"(declare-fun {name} ({" ".intercalate (arguments.map sortName).toList}) {sortName result})\n"
    let symbols := inputs.map fun input => names[input.fvarId!]!
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
      unless fullyApplied arities term do
        throwError "PA SMT: partially applied or function-valued input"
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
      let answers := decodeSmtResponses response batch.indices.size
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

/-- Normalize function signatures without expanding the functions themselves. -/
private partial def firstOrderType? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  if type.isConstOf ``Int || type.isConstOf ``Bool || type == mkSort .zero then
    return some type
  if let .forallE _ domain body _ := type then
    if body.hasLooseBVars then return none
    let some domain ← firstOrderType? domain | return none
    let some body ← firstOrderType? body | return none
    return some (← mkArrow domain body)
  return none

/-- Share fixed first-order functions as uninterpreted inputs with normalized types. -/
private def withNamedFunctions (expressions : Array Expr)
    (k : Array Expr → MetaM Batch) : MetaM Batch := do
  let mut constants : NameSet := {}
  let mut translation : Smt.TranslationM.State := {}
  for expression in expressions do
    try
      let ((_, names, _), next) ← (Smt.Translator.translateExpr expression).run translation
      constants := constants ∪ names
      translation := next
    catch error =>
      if error.isInterrupt then throw error
  let mut originals := #[]
  let mut declarations := #[]
  for name in constants.toArray do
    let info ← getConstInfo name
    unless info.levelParams.isEmpty do continue
    let some type ← firstOrderType? info.type | continue
    originals := originals.push (Lean.mkConst name)
    declarations := declarations.push (name, type)
  withLocalDeclsDND declarations fun inputs => do
    let replacements := (originals.zip inputs).foldl (init := ({} : ExprMap Expr)) fun m (e, input) =>
      m.insert e input
    k (expressions.map fun e => e.replace replacements.get?)

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

/-- Simplify shared assumptions once and expose record fields. -/
private def withSimplifiedBatch (compact : Bool) (queries : Array Expr)
    (k : Array Expr → Array Expr → MetaM Batch) : MetaM Batch := do
  withSharedPrefix queries (fun _ premises conclusions => do
    let sources := flex.automation.sourcePredicates.get (← getOptions)
    let extensional ← if sources then ({} : SimpTheorems).addConst ``funext_iff
      else pure {}
    let context ← Simp.mkContext { maxSteps := 10000, failIfUnchanged := false }
      #[← getSimpTheorems, extensional] (← getSimpCongrTheorems)
    let mut simprocs := #[← Simp.getSimprocs]
    if compact then
      simprocs := simprocs.push (← ({} : Simp.Simprocs).add ``Flex.ExistsAndEq.existsAndEq true)
    let simplify (e : Expr) : MetaM Expr := do
      let e ← instantiateMVars e
      let e ← if sources then unfoldSourcePredicates e else pure e
      unfoldAbbreviations (← Meta.simp e context simprocs).1.expr
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
    k assumptions conclusions)
    (scalars := false)

/-- lean-smt prints function sorts infix; SMT-LIB higher-order sorts use prefix arrows. -/
private partial def solverSexp : Sexp → Sexp
  | .atom s => .atom s
  | .expr xs =>
    let xs := xs.map solverSexp
    if xs.length >= 3 && xs.length % 2 == 1 &&
        xs.zipIdx.all (fun (x, i) => i % 2 == 0 || x == .atom "->") then
      .expr (.atom "->" :: (xs.zipIdx.filterMap fun (x, i) => if i % 2 == 0 then some x else none))
    else .expr xs

private def hasFunctionSort : Smt.Term → Bool
  | .arrowT .. => true
  | .appT f a => hasFunctionSort f || hasFunctionSort a
  | .forallT _ t b | .existsT _ t b => hasFunctionSort t || hasFunctionSort b
  | .letT _ v b => hasFunctionSort v || hasFunctionSort b
  | _ => false

private def functionSignature : Smt.Term → List Smt.Term
  | .arrowT a b => a :: functionSignature b
  | t => [t]

private partial def firstOrderTerm (arities : Std.HashMap String Nat) : Smt.Term → Bool
  | .symbolT name => arities[name]?.getD 0 == 0
  | .literalT _ => true
  | .arrowT .. => false
  | .forallT name type body | .existsT name type body =>
    !hasFunctionSort type && firstOrderTerm (arities.insert name 0) body
  | .letT name value body =>
    firstOrderTerm arities value && firstOrderTerm (arities.insert name 0) body
  | term@(.appT ..) =>
    let (head, args) := application term []
    match head with
    | .symbolT name =>
      (arities[name]?.all (· == args.length)) && args.all (firstOrderTerm arities)
    | _ => false
where
  application : Smt.Term → List Smt.Term → Smt.Term × List Smt.Term
    | .appT f a, args => application f (a :: args)
    | f, args => (f, args)

/-- A higher-order candidate must not invalidate unrelated first-order SMT queries. -/
private def firstOrderCommands (commands : List Smt.Translate.Command) : Bool := Id.run do
  let mut arities : Std.HashMap String Nat := {}
  for command in commands do
    match command with
    | .declare name type =>
      let signature := functionSignature type
      if signature.any hasFunctionSort then return false
      arities := arities.insert name (signature.length - 1)
    | .defineFun name ps cod _ _ =>
      if hasFunctionSort cod || ps.any (hasFunctionSort ·.2) then return false
      arities := arities.insert name ps.length
    | .declareDatatypes _ datatypes =>
      for constructors in datatypes do
        for (name, fields) in constructors do
          if fields.any (hasFunctionSort ·.2) then return false
          arities := arities.insert name fields.length
          for (field, _) in fields do arities := arities.insert field 1
    | _ => pure ()
  return commands.all fun command => match command with
    | .assert term => firstOrderTerm arities term
    | .defineFun _ ps _ term _ =>
      firstOrderTerm (ps.foldl (fun m (n, _) => m.insert n 0) arities) term
    | .defineSort _ ps type => !hasFunctionSort type && !ps.any hasFunctionSort
    | _ => true

private def buildRichBatch (queries : Array Expr) (timeoutMs : Nat)
    (functions : Bool := false) : MetaM Batch :=
  withSimplifiedBatch functions queries fun assumptions conclusions => do
    let prepare := if functions then withNamedFunctions else fun es k => k es
    prepare (assumptions ++ conclusions) fun expressions => do
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
            unless functions || firstOrderCommands (nextGraph.commands.toList.map (·.2)) do
              throwError "PA SMT: candidate requires higher-order translation"
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
          (graph.graph.orderedDfs roots.toList fun e => do
            unless (facts.extract assumptions.size facts.size).contains e do
              Smt.Translate.Query.emitVertex graph.commands e) []
        -- Satisfiability of a quantified context can be harder than its valid consequences.
        indices := indices.filter (fun i => !conclusions[i]!.isConstOf ``False) ++
          indices.filter (fun i => conclusions[i]!.isConstOf ``False)
        let perQuery := if flex.automation.sourcePredicates.get (← getOptions) then
            max 1 (timeoutMs / max 1 indices.size) else timeoutMs
        let mut script := s!"(set-option :print-success false)\n(set-option :produce-proofs false)\n(set-option :timeout {perQuery})\n(set-logic ALL)\n"
        if functions then
          script := s!"(set-option :print-success false)\n(set-option :produce-proofs false)\n(set-option :tlimit-per {timeoutMs})\n(set-logic HO_ALL)\n"
          script := script ++ Sexp.serializeMany (commands.reverse.map (solverSexp ∘ ToSexp.toSexp)) ++ "\n"
        else
          script := script ++ Smt.Translate.Command.cmdsAsQuery commands.reverse ++ "\n"
        for index in indices do
          let name := Smt.Term.quoteSymbol names[flags[index]!.fvarId!]!
          let some command := graph.commands[facts[assumptions.size + index]!]?
            | throwError "PA SMT: missing candidate assertion"
          let assertion := if functions then
              toString (solverSexp (ToSexp.toSexp command)) else toString command
          -- Query definitions belong inside push/pop: quantified candidates otherwise
          -- burden every check, even when their answer flags are unconstrained.
          script := script ++ s!"(push 1)\n{assertion}\n(assert (not {name}))\n(check-sat)\n(pop 1)\n"
        return {
          script := script ++ "(exit)\n"
          indices, results
          omittedAssumptions := true }

/-- Use the existing CVC5 binding; each batch owns its solver and deadline. -/
private def runFunctionBatch (script : String) (count timeoutMs : Nat)
    : MetaM (Except String (Array PASynthResult)) := do
  let deadline := (← IO.monoMsNow) + timeoutMs
  let result ← cvc5.run (m := MetaM) do
    let manager ← cvc5.TermManager.new
    let solver ← cvc5.Solver.new manager
    solver.setOption "incremental" "true"
    let parser ← cvc5.InputParser.new solver
    let symbols ← parser.getSymbolManager
    parser.setStringInput script .SMT_LIB_2_6
    let mut answers := #[]
    while true do
      Core.checkInterrupted
      let now ← IO.monoMsNow
      if now >= deadline then break
      let command ← parser.nextCommand
      if command.isNull then break
      let checking := command.getCommandName == "check-sat"
      if checking then
        let now ← IO.monoMsNow
        if now >= deadline then break
        let share := max 1 ((deadline - now) / max 1 (count - answers.size))
        solver.setOption "tlimit-per" (toString share)
      let response := (← command.invoke solver symbols).trimAscii.toString
      if checking || !response.isEmpty then answers := answers.push response
    return answers
  match result with
  | .error error => return .error error.toString
  | .ok answers =>
    if answers.size > count then return .error "extra CVC5 responses"
    return do
      let parsed ← parseResponses ("\n".intercalate answers.toList) answers.size
      return parsed ++ unknowns (count - parsed.size) "CVC5 batch timed out"

/-- A bounded, decision-only retry after simplification. SAT remains inconclusive:
unfolding may leave fixed Lean functions uninterpreted in the SMT approximation. -/
private def richSmtOracle (timeoutMs : Nat) (functions : Bool) : PASynthOracle := fun queries => do
  if queries.isEmpty then return #[]
  if timeoutMs == 0 then return unknowns queries.size "SMT timeout must be positive"
  withNewMCtxDepth do
    let saved ← saveState
    try
      let queries ← queries.mapM fun query => do zetaReduce (← instantiateMVars query)
      if queries.any (fun q => q.hasMVar || q.hasLooseBVars) then
        return unknowns queries.size "unresolved metavariable or loose binder"
      let batch ← buildRichBatch queries timeoutMs functions
      if batch.indices.isEmpty then return batch.results
      Core.checkInterrupted
      let answers ← if functions then
        runFunctionBatch batch.script batch.indices.size timeoutMs
      else do
        let response ← CHC.Process.run {
          executable := "z3", args := #["-in", "-smt2"], timeoutMs } batch.script
        pure (decodeSmtResponses response batch.indices.size)
      Core.checkInterrupted
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


/-- Simplify and translate a batch with lean-smt's ordinary first-order encoding. -/
def simplifiedSmtOracle (timeoutMs : Nat := 2000) : PASynthOracle :=
  richSmtOracle timeoutMs false

/-- Normalize fixed function signatures and use CVC5's higher-order input syntax. -/
def functionSmtOracle (timeoutMs : Nat := 2000) : PASynthOracle :=
  richSmtOracle timeoutMs true


/-- Validate scalar observations and congruence without unfolding semantic predicates.
Only validity transfers back; an abstract counterexample is inconclusive. -/
def observationSmtOracle (timeoutMs : Nat := 2000) : PASynthOracle := fun queries => do
  if queries.isEmpty then return #[]
  withNewMCtxDepth do
    let saved ← saveState
    try
      let projected ← withSharedPrefix queries (fun _ premises conclusions => do
        let mut assumptions := premises
        for decl in ← getLCtx do
          if !decl.isImplementationDetail && (← isProp decl.type) then
            let type ← instantiateMVars decl.type
            unless assumptions.contains type do assumptions := assumptions.push type
        Observation.projectQueries assumptions conclusions) (scalars := false)
      let results ← smtOracle timeoutMs projected
      return results.map fun result => match result with
        | .valid => .valid
        | _ => .unknown "observation abstraction inconclusive"
    catch error =>
      if error.isInterrupt then throw error
      return unknowns queries.size (← error.toMessageData.toString)
    finally
      set saved.elab
      CHC.restoreMetaState saved.meta

end Flex.PA
