import Flex.CHC.Export
import Lean.Meta.Tactic.Simp

namespace Flex.CHC

open Lean Meta

private def bounded (count limit : Nat) : MetaM Nat := do
  if count > limit then
    throwError "CHC normalization: expanded constraints exceed the clause limit ({limit})"
  return count

/-- Preflight guard expansion: conjunction multiplies, disjunction adds. -/
private partial def antecedentBranches (input : Expr) (limit : Nat) : MetaM Nat := do
  let input ← Prepare.expose input
  if let some (left, right) := input.and? then
    bounded ((← antecedentBranches left limit) * (← antecedentBranches right limit)) limit
  else if let some (left, right) := input.or? then
    bounded ((← antecedentBranches left limit) + (← antecedentBranches right limit)) limit
  else if input.isAppOfArity ``Exists 2 then
    let domain := input.getArg! 0
    let predicate := input.getArg! 1
    withLocalDeclD `witness domain fun witness =>
      antecedentBranches (predicate.beta #[witness]) limit
  else
    return 1

/-- Bound export's clause count and detect guards requiring normalization. -/
private partial def expandedClauses (input : Expr) (limit : Nat) : MetaM (Nat × Bool) := do
  let input ← Prepare.expose input
  if input.isConstOf ``True then return (0, false)
  if let some (left, right) := input.and? then
    let (leftCount, leftChanged) ← expandedClauses left limit
    let (rightCount, rightChanged) ← expandedClauses right limit
    return (← bounded (leftCount + rightCount) limit, leftChanged || rightChanged)
  if let .forallE name domain body bi := input then
    withLocalDecl name bi domain fun parameter => do
      let (count, changed) ← expandedClauses (body.instantiate1 parameter) limit
      if (← isProp domain) && !body.hasLooseBVar 0 then
        let domain ← Prepare.expose domain
        let structural := domain.and?.isSome || domain.or?.isSome || domain.isAppOfArity ``Exists 2
        return (← bounded ((← antecedentBranches domain limit) * count) limit,
          changed || structural)
      return (count, changed)
  else
    return (← bounded 1 limit, false)

/-- Normalize existential, disjunctive, and conjunctive Horn guards with proofs.
Use only the three logical equivalences below, bounding expansion before rewriting.
Keep predicate slots unassigned and the body open; failures restore entry state.
The returned goal has guard forms accepted by export. -/
def normalizeGoal (bodyGoal : MVarId) (maxClauses : Nat := 1024) : MetaM MVarId := do
  let saved ← Meta.saveState
  try
    bodyGoal.withContext do
      if maxClauses == 0 then throwError "CHC normalization: maxClauses must be positive"
      bodyGoal.checkNotAssigned `chc_normalize
      let target ← instantiateMVars (← bodyGoal.getType)
      unless ← isProp target do throwError "CHC normalization: expected a proposition"
      let (_, changed) ← expandedClauses target maxClauses
      unless changed do return bodyGoal
      let mut theorems : SimpTheorems := {}
      for name in [``exists_imp, ``or_imp, ``and_imp] do
        theorems ← theorems.addConst name
      let context ← Simp.mkContext {
        failIfUnchanged := false, iota := false, proj := false, etaStruct := .none
        maxSteps := 100000 } #[theorems]
      let (some normalized, _) ← simpTarget bodyGoal context (mayCloseGoal := false)
        | throwError "CHC normalization unexpectedly closed the body goal"
      -- Recheck after simp exposes any further beta/let wrappers.
      discard <| expandedClauses (← normalized.getType) maxClauses
      return normalized
  catch error =>
    restoreMetaState saved
    throw error

end Flex.CHC
