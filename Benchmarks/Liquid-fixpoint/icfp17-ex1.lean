import Flex

def lhHornProp : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ v : Int, v = x - 1 → κ v x)
      ∧ (∀ y : Int, κ y x → ∀ v : Int, v = y + 1 → 0 ≤ v)

set_option flex.benchPhases true
theorem lhHornProof : lhHornProp := by
  solve_fixpoint
