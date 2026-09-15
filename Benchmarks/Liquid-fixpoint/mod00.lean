import Flex

def mod00Prop : Prop :=
  ∃ κ0 : Int → Prop,
    (∀ a0 : Int, a0 = 4 → κ0 a0)
    ∧ (∀ a1 : Int, a1 = 10 → κ0 a1)
    ∧ (∀ a2 : Int, True → ∀ _ : Int, κ0 a2 → a2 % 2 = 0)

set_option flex.benchPhases true
theorem mod00Proof : mod00Prop := by
  solve_fixpoint
