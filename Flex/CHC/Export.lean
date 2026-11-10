import Flex.Fusion.Flatten
import Flex.SMT.Decode
import Smt2Lean.Chc

namespace Flex.CHC

open Lean Meta

/-- Restore Meta/Core state after a speculative operation. -/
def restoreMetaState (saved : Meta.SavedState) : MetaM Unit := do
  set saved.meta
  modifyThe Core.State fun _ => saved.core.toState

/-- Map solver symbols to Lean witness slots, retaining unused arguments and Bool/Prop types. -/
structure Relation where
  symbol : String
  kvar : KVar
  leanType : Lean.Expr
  /-- SMT sorts of the κ's arguments, as the encoder declares them. -/
  argumentSorts : Array String := #[]
  deriving Inhabited

/-- A Horn problem in SMT-LIB, with metadata for model reconstruction. Clause terms come from
the exact encoder (`Flex.SMT`); datatypes and definitions are declared before the relations. -/
structure ExportedProblem where
  relations : Array Relation
  /-- Datatype and definition declarations, in dependency order. -/
  declarations : Array String := #[]
  clauses : Array SMT.HornClause := #[]
  /-- Relation symbols occurring in some clause. -/
  usedRelations : Std.HashSet String := {}
  clauseCount : Nat
  /-- Free variables of the body, quantified outside the κs, of any sort the encoder supports.
  Every relation takes them as leading arguments and every clause binds them, so κs may depend
  on them. -/
  parameters : Array Expr := #[]
  parameterSorts : Array String := #[]
  /-- The encoder's declared symbols, for decoding models. -/
  symbols : SMT.Symbols := {}
  /-- Alternate SMT presentation (one conjunction of premises per clause); the Lean clauses and
  relation slots are unchanged. -/
  canonicalClauses : Bool := false
  deriving Inhabited

/-- Serialize the script. -/
def ExportedProblem.toSMTLib (problem : ExportedProblem) : String :=
  let relations := problem.relations.map fun r =>
    let sorts := problem.parameterSorts ++ r.argumentSorts
    s!"(declare-fun {r.symbol} ({" ".intercalate sorts.toList}) Bool)"
  let clauses := problem.clauses.map (·.render problem.canonicalClauses)
  "\n".intercalate (#["(set-logic HORN)"] ++ problem.declarations ++ relations ++ clauses ++
    #["(check-sat)"]).toList ++ "\n"

namespace Fragment

/-- The encoder's configuration for Horn clauses. Non-linear arithmetic is always encoded; whether
the solver copes is up to the solver. -/
def hornConfig : MetaM SMT.Config := do
  return { SMT.Config.ofOptions (← getOptions) with
    horn := true, uninterpretedDefs := false, encodeQuantifiers := false, encodeNonlinear := true }

/-- Whether a closed type has an SMT sort in Horn clauses, checked in a throwaway encoding. -/
def checkSort (type : Expr) : MetaM Unit := do
  SMT.EncodeM.run' (← hornConfig) (discard <| SMT.encodeSort type)

end Fragment

namespace Prepare

/-- Existential symbol roles are determined by their Lean types. -/
private inductive WitnessKind where
  | predicate | carrier | constant | function | theoryParameter

private def witnessKind (type : Expr) : MetaM WitnessKind := do
  let type ← whnf type
  if type.isProp then return .predicate
  if type.isSort then return .carrier
  for id in (collectFVars {} type).fvarIds do
    let dependency ← whnf (← inferType (mkFVar id))
    if dependency.isSort && !dependency.isProp then return .theoryParameter
  forallTelescopeReducing type fun parameters result => do
    if result.isProp then return .predicate
    return if parameters.isEmpty then .constant else .function

private def checkPredicateType (name : Name) (type : Expr) : MetaM Unit := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelMVar then
    throwError "CHC preparation: predicate '{name}' has an open or unresolved signature"
  forallTelescopeReducing type fun parameters _ =>
    for parameter in parameters, i in [:parameters.size] do
      let domain ← inferType parameter
      if domain.hasFVar then
        throwError "CHC preparation: predicate '{name}' has a dependent argument {i + 1}"
      try Fragment.checkSort domain
      catch error =>
        if error.isInterrupt || error.isRuntime then throw error
        throwError "CHC preparation: predicate '{name}' argument {i + 1} has unsupported type {domain}: {error.toMessageData}"

/-- Validate the existential prefix before creating predicate witness slots. -/
partial def checkPredicatePrefix (input : Expr) : MetaM Unit := do
  let input ← whnf input
  unless input.isAppOfArity ``Exists 2 do return
  let type := input.getArg! 0
  let predicate ← whnf (input.getArg! 1)
  let .lam name _ body bi := predicate
    | throwError "CHC preparation: expected a lambda in an existential binder"
  match ← witnessKind type with
  | .predicate => checkPredicateType name type
  | .carrier =>
    throwError "CHC preparation: unsupported theory wrapper: existential carrier '{name}' : {type}; array and other abstract theory models require an interpretation before predicate synthesis"
  | .theoryParameter =>
    throwError "CHC preparation: unsupported theory-model parameter '{name}' : {type}; its type depends on an abstract carrier"
  | .constant =>
    throwError "CHC preparation: unsupported existential background constant '{name}' : {type}; only Prop-valued predicates can be synthesized"
  | .function =>
    throwError "CHC preparation: unsupported existential background function '{name}' : {type}; only Prop-valued predicates can be synthesized"
  withLocalDecl name bi type fun parameter =>
    checkPredicatePrefix (body.instantiate1 parameter)

/-- Expose named propositions and beta/let wrappers, preserving arithmetic operators. -/
partial def expose (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData.headBeta
  match expression with
  | .letE _ _ value body _ => expose (body.instantiate1 value)
  | .const .. =>
    let type ← whnf (← inferType expression)
    if (← isProp expression) || type.isConstOf ``Int || type.isConstOf ``Bool then
      if let some value ← unfoldDefinition? expression then return ← expose value
    return expression
  | _ => return expression

end Prepare

private def relation (kvar : KVar) (index : Nat) : MetaM Relation := do
  if ← kvar.mvarId.isAssigned then
    throwError "CHC export: predicate '{kvar.name}' is already assigned"
  let type ← instantiateMVars (← kvar.mvarId.getType)
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelMVar then
    throwError "CHC export: predicate '{kvar.name}' has an open or unresolved signature"
  forallTelescopeReducing type fun parameters result => do
    unless result.isProp do
      throwError "CHC export: predicate '{kvar.name}' must return Prop"
    unless parameters.size == kvar.paramTypes.length && parameters.size == kvar.params.length do
      throwError "CHC export: parameter metadata disagrees with predicate '{kvar.name}'"
    for parameter in parameters, i in [:parameters.size] do
      let parameterType ← inferType parameter
      if parameterType.hasFVar then
        throwError "CHC export: dependent predicate parameters are unsupported"
      unless ← isDefEq parameterType kvar.paramTypes[i]! do
        throwError "CHC export: parameter {i + 1} has inconsistent metadata for '{kvar.name}'"
  return { symbol := s!"k_{index}", kvar, leanType := type }

/-- Encode a relation's argument sorts, declaring any datatypes they need. -/
private def encodeArgumentSorts (relation : Relation) : SMT.EncodeM Relation := do
  let types ← forallTelescopeReducing relation.leanType fun parameters _ =>
    parameters.mapM fun p => inferType p
  let sorts ← types.mapIdxM fun i type => do
    try SMT.encodeSort type
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      throwError "CHC export: predicate '{relation.kvar.name}' argument {i + 1} : {type}: {error.toMessageData}"
  return { relation with argumentSorts := sorts }

private def validate (problem : ExportedProblem) : MetaM Unit := do
  (Smt2Lean.Chc.parseAndInspectProblem problem.toSMTLib (name := "flex-chc") fun parsed => do
    unless parsed.constants.isEmpty && parsed.functions.isEmpty &&
        parsed.relations.size == problem.relations.size && parsed.clauses.size == problem.clauseCount do
      throw (.error "CHC export: unexpected declarations or clause count after validation")
    for expected in problem.relations do
      let some actual := parsed.relations.find? (·.name == expected.symbol)
        | throw (.error s!"CHC export: missing relation '{expected.symbol}'")
      let expectedSorts := problem.parameterSorts ++ expected.argumentSorts
      unless actual.argumentSorts.size == expectedSorts.size do
        throw (.error s!"CHC export: wrong arity for '{expected.symbol}'")
      for actualSort in actual.argumentSorts, expectedSort in expectedSorts do
        unless (match expectedSort with
            | "Int" => actualSort.isInteger
            | "Bool" => actualSort.isBoolean
            | _ => !actualSort.isInteger && !actualSort.isBoolean) do
          throw (.error s!"CHC export: wrong argument sort for '{expected.symbol}'")
  ).runIO

/-- Check an equivalent Horn presentation before a solver retry. -/
def ExportedProblem.withCanonicalClauses (problem : ExportedProblem) : MetaM ExportedProblem := do
  let problem := { problem with canonicalClauses := true }
  validate problem
  return problem


/-- The body's free variables, in context order, as Horn parameters. -/
private def collectParameters (kvars : List KVar) (body : Expr)
    : MetaM (Array Expr) := do
  let lctx ← getLCtx
  let ids := (collectFVars {} body).fvarIds.qsort fun a b =>
    match lctx.find? a, lctx.find? b with
    | some x, some y => x.index < y.index
    | _, _ => false
  let mut parameters := #[]
  for id in ids do
    let decl ← id.getDecl
    let type ← instantiateMVars decl.type
    if type.hasFVar then
      throwError "CHC export: free variable '{decl.userName}' has a dependent type"
    for kvar in kvars do
      unless (← kvar.mvarId.getDecl).lctx.contains id do
        throwError "CHC export: free variable '{decl.userName}' is not in the context of '{kvar.name}'"
    try Fragment.checkSort type
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      throwError "CHC export: free variable '{decl.userName}' : {type} in the body has no SMT sort: {error.toMessageData}"
    parameters := parameters.push (mkFVar id)
  return parameters

/-- Export Horn clauses through the exact SMT encoder. κ arguments, clause variables, and free
variables of the body may range over anything the encoder supports (`Int`, `Bool`/`Prop`, `Nat`
as `Int`, records and other datatypes, functions as arrays). Unencodable premises are dropped,
which only strengthens a clause; an unencodable head fails the export. Free variables, which
must be in every κ's context, become parameters (see `ExportedProblem.parameters`). No
witnesses are assigned. -/
def exportConstraints (kvars : List KVar) (body : Expr) : MetaM ExportedProblem := do
  let saved ← Meta.saveState
  try
    let mut seen : Std.HashSet MVarId := {}
    for kvar in kvars do
      if seen.contains kvar.mvarId then throwError "CHC export: duplicate κ identity '{kvar.name}'"
      seen := seen.insert kvar.mvarId
    let relations ← kvars.toArray.mapIdxM fun i kvar => relation kvar i
    let body ← zetaReduce (← instantiateMVars body)
    let parameters ← collectParameters kvars body
    if body.hasLooseBVars then throwError "CHC export: loose bound variable in the body"
    unless ← isProp body do throwError "CHC export: expected a proposition"
    let context : KContext := { kvars := kvars.foldl (fun ctx k => ctx.insert k.mvarId k) {} }
    let clauses ← (exprFlat body Prepare.expose).run context
    let symbolTypes ← relations.mapM fun r => do
      return (Name.mkSimple r.symbol, ← mkForallFVars parameters r.leanType)
    withLocalDeclsDND symbolTypes fun symbols => do
      let replacements := (relations.zip symbols).foldl
        (fun map (r, symbol) => map.insert r.kvar.mvarId (mkAppN symbol parameters))
        ({} : Std.HashMap MVarId Expr)
      let relationSymbols := (relations.zip symbols).foldl
        (fun map (r, symbol) => map.insert symbol.fvarId! r.symbol) ({} : Std.HashMap FVarId String)
      let config ← Fragment.hornConfig
      let encodeAll : SMT.EncodeM (Array String × Array Relation × Array SMT.HornClause) := do
        -- Sorts first, so their datatypes are declared before any clause uses them.
        let parameterSorts ← parameters.mapM fun p => do SMT.encodeSort (← inferType p)
        let relations ← relations.mapM encodeArgumentSorts
        let clauses ← clauses.toArray.mapIdxM fun i original => do
          try
            let input := original.replace fun e => if e.isMVar then replacements[e.mvarId!]? else none
            if input.hasMVar then throwError "unregistered or unresolved metavariable"
            SMT.encodeHornClause (← mkForallFVars parameters input)
          catch error =>
            if error.isInterrupt || error.isRuntime then throw error
            throwError "CHC export: clause {i + 1}: {error.toMessageData}"
        return (parameterSorts, relations, clauses)
      let ((parameterSorts, relations, encoded), state) ←
        (encodeAll.run { config, relations := relationSymbols }).run {}
      let problem : ExportedProblem := {
        relations
        declarations := state.declarations
        clauses := encoded
        usedRelations := state.usedRelations
        clauseCount := encoded.size
        parameters, parameterSorts
        symbols := state.symbols }
      validate problem
      return problem
  finally restoreMetaState saved

end Flex.CHC
