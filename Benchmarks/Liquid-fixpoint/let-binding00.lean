import Flex

def lhNonlinearProp : Prop :=
  ∀ x : Int, True → x * 2 = x + x

set_option flex.benchPhases true
theorem lhNonlinearProof : lhNonlinearProp := by
  solve_fixpoint
