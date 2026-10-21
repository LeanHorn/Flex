import Flex.CHC.Export
import Flex.CHC.Backend
import Smt2Lean.Model

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
      unless parameters.size == relation.argumentSorts.size &&
          parameters.size == relation.kvar.paramTypes.length &&
          parameters.size == relation.kvar.params.length do
        throwError "CHC witnesses: inconsistent arity metadata for '{relation.symbol}'"
      for parameter in parameters, i in [:parameters.size] do
        let type ← inferType parameter
        requireClosed type s!"parameter {i + 1} of '{relation.symbol}'"
        requireClosed relation.kvar.paramTypes[i]! s!"parameter metadata of '{relation.symbol}'"
        unless ← isDefEq type relation.kvar.paramTypes[i]! do
          throwError "CHC witnesses: inconsistent parameter metadata for '{relation.symbol}'"
        unless (← Fragment.valueSort type) == relation.argumentSorts[i]! do
          throwError "CHC witnesses: inconsistent SMT sort metadata for '{relation.symbol}'"

/-- The shared importer represents every SMT Bool as Lean Prop. -/
private def importedType (relation : Relation) : Expr :=
  relation.argumentSorts.foldr (fun sort result =>
    let domain := match sort with
      | .int => mkConst ``Int
      | .bool => mkSort .zero
    .forallE .anonymous domain result .default) (mkSort .zero)

private def checkValue (relation : Relation) (value : Expr) : MetaM Unit := do
  requireClosed value s!"candidate for '{relation.symbol}'"
  checkWithKernel value
  unless ← isDefEq (← inferType value) relation.leanType do
    throwError "CHC witnesses: candidate type does not match '{relation.symbol}'"

private def usesSymbol (symbol : String) : Smt.Term → Bool
  | .literalT _ => false
  | .symbolT name => name == symbol
  | .arrowT a b | .appT a b => usesSymbol symbol a || usesSymbol symbol b
  | .forallT name a b | .existsT name a b | .letT name a b =>
    usesSymbol symbol a || (name != symbol && usesSymbol symbol b)

/-- Only predicates absent from every exported assertion may be completed. -/
private def completeUnused (problem : ExportedProblem) (relation : Relation) : MetaM Witness := do
  if problem.commands.any (fun
      | .assert term => usesSymbol relation.symbol term
      | _ => false) then
    throwError "CHC witnesses: missing model definition '{relation.symbol}' used by a clause"
  let value ← forallTelescopeReducing relation.leanType fun parameters _ =>
    mkLambdaFVars parameters (mkConst ``True) (usedOnly := false)
  checkValue relation value
  return { symbol := relation.symbol, mvarId := relation.kvar.mvarId, value, defaulted := true }

/-- Restore Bool arguments as `b = true`, retaining Prop and unused parameters. -/
private def adapt (relation : Relation) (definition : Smt2Lean.ReconstructedDefinition)
    : MetaM Witness := do
  unless ← isDefEq definition.type (importedType relation) do
    throwError "CHC witnesses: model signature does not match '{relation.symbol}'"
  let value ← forallTelescopeReducing relation.leanType fun parameters _ => do
    let arguments ← parameters.mapM fun parameter => do
      if (← whnf (← inferType parameter)).isConstOf ``Bool then
        mkEq parameter (mkConst ``Bool.true)
      else
        pure parameter
    mkLambdaFVars parameters (definition.value.beta arguments) (usedOnly := false)
  checkValue relation value
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
SMTLib-to-Lean expands helpers. Caller state is restored without assigning witnesses. -/
def importWitnesses (problem : ExportedProblem) (result : SolverResult) : MetaM (Array Witness) := do
  let saved ← Meta.saveState
  try
    checkRelations problem
    successfulModel result
    -- Kernel checking needs temporary declarations in an unlocked environment.
    let response ← withoutModifyingEnv do
      let environment ← getEnv
      Smt2Lean.Model.importResponse result.process.stdout environment "flex-chc-model"
    unless response.status == some .sat && response.diagnostics.isEmpty do
      throwError "CHC witnesses: expected a sat model without solver errors"
    let some definitions := response.definitions
      | throwError "CHC witnesses: missing model definitions"
    let mut byName : Std.HashMap String Smt2Lean.ReconstructedDefinition := {}
    for definition in definitions do
      if byName.contains definition.name then
        throwError "CHC witnesses: duplicate model definition '{definition.name}'"
      byName := byName.insert definition.name definition
    problem.relations.mapM fun relation => do
      match byName[relation.symbol]? with
      | some definition => adapt relation definition
      | none => completeUnused problem relation
  finally restoreMetaState saved

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
      checkValue relation witness.value
    restoreMetaState saved
    for witness in witnesses do witness.mvarId.assign witness.value
  catch error =>
    restoreMetaState saved
    throw error

end Flex.CHC
