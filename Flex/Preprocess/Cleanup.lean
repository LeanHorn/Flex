import Flex.Preprocess.FalsePredicates
import Flex.Zap.Emit
import Flex.CHC.Normalize

open Lean Meta

namespace Flex.Preprocess

private def simplifyTarget (goal : MVarId) (names : Array Name) : MetaM MVarId :=
  goal.withContext do
    let mut lemmas : SimpTheorems := {}
    -- `simp only` also includes reflexive equality and equivalence.
    for name in #[``eq_self, ``iff_self] ++ names do
      lemmas ← lemmas.addConst name
    let context ← Simp.mkContext { failIfUnchanged := false, maxSteps := 1000000 }
      #[lemmas] (← getSimpCongrTheorems)
    let (next?, _) ← simpTarget goal context
    return next?.getD goal

/-- Zap's preparation, also available when elimination is disabled.
The returned goal may already be assigned if simplification closes it. -/
def prepareGoal (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← goal.getType
  let exposed ← whnf target
  -- Expose the constraint spine, preserving surface arithmetic at ordinary leaves.
  let target := if exposed.isForall || exposed.isAppOfArity ``Exists 2 ||
      exposed.isAppOfArity ``And 2 then exposed else target
  let goal ← goal.change target
  let goal ← simplifyTarget goal #[``true_implies, ``true_and, ``and_true]
  if ← goal.isAssignedOrDelayedAssigned then return goal
  let target ← goal.getType
  let (normalized, proof) ← inlineFalsePredicates target
  if normalized == target then return goal
  let next ← mkFreshExprMVar normalized (kind := .syntheticOpaque)
  goal.assign (← mkAppM ``Iff.mpr #[proof, next])
  simplifyTarget next.mvarId!
    #[``false_implies, ``true_implies, ``true_and, ``and_true, ``forall_const]

/-- Remove inert structure and equality-bound witnesses without expanding guards. -/
def cleanupGoal (goal : MVarId) (kvars : List KVar := []) : MetaM MVarId :=
  goal.withContext do
    if ← goal.isAssignedOrDelayedAssigned then return goal
    let target ← instantiateMVars (← goal.getType)
    let (clean, proof) ← collapseInert target
    let goal ← if clean == target then pure goal else
      goal.replaceTargetEq clean (mkApp3 (mkConst ``propext) target clean proof)
    let goal ← Flex.CHC.compactGoal goal kvars
    if (← goal.getType).isConstOf ``True then goal.assign (mkConst ``True.intro)
    return goal

end Flex.Preprocess
