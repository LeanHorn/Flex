import Flex

def existsOddityProp : Prop :=
  ∃ κ0 : Int → Prop,
    (∀ a0 : Int, a0 = 0 → κ0 a0)
    ∧ (∀ a1 : Int, ∀ _x : Int, κ0 a1 → a1 = 0)
    ∧ (∀ a2 : Int, ∀ _x : Int, a2 = 0 → κ0 a2)

set_option flex.benchPhases true
theorem existsOddityProof : existsOddityProp := by
  solve_fixpoint

theorem test : existsOddityProp := by
  fusion
  grind
