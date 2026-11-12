import Flex.CHC.Export
import Flex.CHC.Backend

namespace Flex.CHC

open Lean Meta

/-- A closed, typed predicate candidate; satisfaction is checked by certification. -/
structure Witness where
  symbol : String
  mvarId : MVarId
  value : Expr
  /-- Flex supplied True for an unused predicate omitted from the model. -/
  defaulted : Bool := false
  deriving Inhabited

private def requireClosed (expression : Expr) (description : String) : MetaM Unit := do
  if expression.hasFVar || expression.hasLooseBVars || expression.hasMVar || expression.hasLevelMVar then
    throwError "CHC witnesses: {description} contains free or unresolved variables"

/-- Export metadata can become stale between preparation and model import. -/
private def checkRelations (problem : ExportedProblem) : MetaM Unit := do
  let mut symbols : Std.HashSet String := {}
  let mut identities : Std.HashSet MVarId := {}
  for relation in problem.relations do
    if relation.symbol.isEmpty || symbols.contains relation.symbol then
      throwError "CHC witnesses: empty or duplicate relation symbol '{relation.symbol}'"
    if identities.contains relation.kvar.mvarId then
      throwError "CHC witnesses: duplicate witness identity for '{relation.symbol}'"
    symbols := symbols.insert relation.symbol
    identities := identities.insert relation.kvar.mvarId
    if ← relation.kvar.mvarId.isAssignedOrDelayedAssigned then
      throwError "CHC witnesses: predicate '{relation.symbol}' is already assigned"
    requireClosed relation.leanType s!"signature of '{relation.symbol}'"
    let currentType ← instantiateMVars (← relation.kvar.mvarId.getType)
    requireClosed currentType s!"current signature of '{relation.symbol}'"
    unless ← isDefEq currentType relation.leanType do
      throwError "CHC witnesses: stale signature for '{relation.symbol}'"
    forallTelescopeReducing relation.leanType fun parameters result => do
      unless result.isProp do
        throwError "CHC witnesses: predicate '{relation.symbol}' must return Prop"
      unless parameters.size == relation.kvar.paramTypes.length &&
          parameters.size == relation.kvar.params.length do
        throwError "CHC witnesses: inconsistent arity metadata for '{relation.symbol}'"
      for parameter in parameters, i in [:parameters.size] do
        let type ← inferType parameter
        requireClosed type s!"parameter {i + 1} of '{relation.symbol}'"
        requireClosed relation.kvar.paramTypes[i]! s!"parameter metadata of '{relation.symbol}'"
        unless ← isDefEq type relation.kvar.paramTypes[i]! do
          throwError "CHC witnesses: inconsistent parameter metadata for '{relation.symbol}'"
      unless parameters.size == relation.argumentSorts.size do
        throwError "CHC witnesses: inconsistent arity for '{relation.symbol}'"

private def checkValue (problem : ExportedProblem) (relation : Relation) (value : Expr)
    : MetaM Unit := do
  let closed ← mkLambdaFVars problem.parameters value (usedOnly := false)
  requireClosed closed s!"candidate for '{relation.symbol}'"
  checkWithKernel closed
  unless ← isDefEq (← inferType closed) (← mkForallFVars problem.parameters relation.leanType) do
    throwError "CHC witnesses: candidate type does not match '{relation.symbol}'"

/-- Only predicates absent from every exported assertion may be completed. -/
private def completeUnused (problem : ExportedProblem) (relation : Relation) : MetaM Witness := do
  if problem.usedRelations.contains relation.symbol then
    throwError "CHC witnesses: missing model definition '{relation.symbol}' used by a clause"
  let value ← forallTelescopeReducing relation.leanType fun parameters _ =>
    mkLambdaFVars parameters (mkConst ``True) (usedOnly := false)
  checkValue problem relation value
  return { symbol := relation.symbol, mvarId := relation.kvar.mvarId, value, defaulted := true }

/-- Decode a relation's model definition. The leading parameters are the problem's parameters;
the rest are the κ's arguments, restored at their Lean types (`Bool` ones as `b = true`). -/
private def adapt (problem : ExportedProblem) (relation : Relation) (definition : SMT.Macro)
    (macros : Std.HashMap String SMT.Macro) : MetaM Witness := do
  let sorts := problem.parameterSorts ++ relation.argumentSorts ++ problem.abstractions.map (·.sort)
  unless definition.params.size == sorts.size &&
      (definition.params.zip sorts).all (fun ((_, s), t) => (SMT.Sexp.parseAll t).toOption == some #[s]) do
    throwError "CHC witnesses: model signature does not match '{relation.symbol}'"
  let value ← forallTelescopeReducing relation.leanType fun parameters _ => do
    -- Abstractions are bound to the definitions they stand for.
    let actuals := problem.parameters ++ parameters ++ problem.abstractions.map (·.value)
    let mut locals : Std.HashMap String SMT.Value := {}
    for (name, _) in definition.params, actual in actuals do
      locals := locals.insert name (← SMT.normalize actual (← inferType actual))
    let body ← (SMT.decodeTerm definition.body).run { symbols := problem.symbols, macros, locals }
    unless body.type.isProp do
      throwError "CHC witnesses: model of '{relation.symbol}' is not a formula"
    mkLambdaFVars parameters (← instantiateMVars body.expr) (usedOnly := false)
  checkValue problem relation value
  return { symbol := relation.symbol, mvarId := relation.kvar.mvarId, value }

private def successfulModel (result : SolverResult) : MetaM Unit := do
  let .sat claimed := result.outcome
    | throwError "CHC witnesses: expected a successful sat result with a model"
  match (SolverResult.ofProcess result.process).outcome with
  | .sat actual =>
    unless claimed == actual do
      throwError "CHC witnesses: model payload disagrees with the process transcript"
  | .error message => throwError "CHC witnesses: {message}"
  | _ => throwError "CHC witnesses: process did not successfully return a model"

/-- Import predicates in existential order, completing omitted unused ones with True.
Models are decoded by `Flex.SMT.Decode`, which expands model helper functions at their uses.
Caller state is restored without assigning witnesses. -/
def importWitnesses (problem : ExportedProblem) (result : SolverResult) : MetaM (Array Witness) := do
  let saved ← Meta.saveState
  try
    checkRelations problem
    successfulModel result
    let .sat commands := result.outcome | throwError "CHC witnesses: missing model"
    let mut byName : Std.HashMap String SMT.Macro := {}
    for command in commands do
      let parsed ← match SMT.Sexp.parseAll command.text with
        | .ok #[sexp] => pure sexp
        | .ok _ => throwError "CHC witnesses: expected one model command"
        | .error e => throwError "CHC witnesses: model syntax: {e}"
      let (name, definition, _) ← match SMT.parseDefineFun parsed with
        | .ok d => pure d
        | .error e => throwError "CHC witnesses: {e}"
      if byName.contains name then
        throwError "CHC witnesses: duplicate model definition '{name}'"
      byName := byName.insert name definition
    problem.relations.mapM fun relation => do
      match byName[relation.symbol]? with
      | some definition => adapt problem relation definition byName
      | none => completeUnused problem relation
  finally
    -- Keep auxiliary declarations (selector matchers) that decoded witnesses refer to.
    let env ← getEnv
    restoreMetaState saved
    setEnv env

/-- Validate the complete, ordered bundle before assigning any witnesses.
Discard validation state; restore entry state on failure. Leaves the body open. -/
def assignWitnesses (problem : ExportedProblem) (witnesses : Array Witness) : MetaM Unit := do
  let saved ← Meta.saveState
  try
    checkRelations problem
    unless witnesses.size == problem.relations.size do
      throwError "CHC witnesses: expected one candidate for every exported relation"
    for relation in problem.relations, witness in witnesses do
      unless witness.symbol == relation.symbol && witness.mvarId == relation.kvar.mvarId do
        throwError "CHC witnesses: candidate identity or order does not match '{relation.symbol}'"
      checkValue problem relation witness.value
    restoreMetaState saved
    for witness in witnesses do witness.mvarId.assign witness.value
  catch error =>
    restoreMetaState saved
    throw error

end Flex.CHC
