import Flex.Preprocess.FalsePredicates
import Flex.Preprocess.TrueFalse
import Flex.Preprocess.Witnesses

open Lean Meta

namespace Flex.Preprocess

/-- Simplify True/False guards and inline predicate slots forced to False. -/
def prepareGoal (goal : MVarId) (simplify : Bool := true) : MetaM MVarId := goal.withContext do
  let original ← goal.getType
  let exposed ← whnf original
  let target := if exposed.isForall || exposed.isAppOfArity ``Exists 2 ||
      exposed.isAppOfArity ``And 2 then exposed else original
  let goal ← goal.change target
  let goal ← if simplify || target != original then simplifyGoal goal else pure goal
  if ← goal.isAssignedOrDelayedAssigned then return goal
  let target ← goal.getType
  let (normalized, proof) ← inlineFalsePredicates target
  if normalized == target then return goal
  let next ← goal.replaceTargetEq normalized (mkApp3 (mkConst ``propext) target normalized proof)
  simplifyGoal next

/-- Optional witness elimination, followed by True/False cleanup. Never expands guards. -/
def cleanupGoal (goal : MVarId) (kvars : List KVar := []) : MetaM MVarId := do
  let goal ← simplifyGoal goal
  if ← goal.isAssignedOrDelayedAssigned then return goal
  let next ← compactGoal goal kvars
  if next == goal then return goal
  simplifyGoal next

end Flex.Preprocess
