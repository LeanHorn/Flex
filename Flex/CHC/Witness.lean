import Flex.CHC.Fragment
import Flex.CHC.Solver
import Smt2Lean.Model

namespace Flex.CHC

open Lean Meta

/-- A closed predicate candidate for an existing existential witness slot.
This records a typed interpretation, not evidence that it satisfies the CHCs. -/
structure Witness where
  symbol : String
  mvarId : MVarId
  value : Expr
  deriving Inhabited

private def requireClosed (expression : Expr) (description : String) : MetaM Unit := do
  if expression.hasFVar || expression.hasLooseBVars || expression.hasMVar || expression.hasLevelMVar then
    throwError "CHC witnesses: {description} contains free or unresolved variables"

/-- Recheck the export's metadata against the current witness slots. Exported
problems may outlive other tactic work; a previously prepared slot can be stale. -/
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

/-- Restore the original Bool/Prop distinction and keep even unused parameters.
For example, an imported `Prop → Int → Prop` becomes `Bool → Int → Prop` by
passing `b = true` in the Bool position; existing Prop positions are unchanged. -/
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

/-- Reconstruct and adapt all model predicates in the original existential order.

Every exported relation is required, including unused and nullary predicates.
Additional ordinary helper definitions are allowed; SMTLib-to-Lean expands them
and checks that the reconstructed expressions are closed. Definitions are matched
by solver symbol, never by model order or by the user's Lean binder names.

This preparation restores the caller's meta state on success and failure. It does
not assign any witness or establish that the candidates satisfy the constraints.
-/
def importWitnesses (problem : ExportedProblem) (result : SolverResult) : MetaM (Array Witness) := do
  let saved ← Meta.saveState
  try
    checkRelations problem
    successfulModel result
    -- Reconstruction creates temporary declarations for kernel checks. Give it
    -- a private, unlocked environment even inside an asynchronous theorem task;
    -- only closed expressions return, never that temporary environment.
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
      let some definition := byName[relation.symbol]?
        | throwError "CHC witnesses: missing model definition '{relation.symbol}'"
      adapt relation definition
  finally saved.restore

/-- Assign a complete, ordered witness bundle after revalidating every entry.

Validation runs before any assignment and its temporary state is discarded. Any
failure restores the caller's state, including pre-existing assignments. The body
proof goal remains open: witness type correctness is not invariant correctness.
-/
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
    saved.restore
    for witness in witnesses do witness.mvarId.assign witness.value
  catch error =>
    saved.restore
    throw error

end Flex.CHC
