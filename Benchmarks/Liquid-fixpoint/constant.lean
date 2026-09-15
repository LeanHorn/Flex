import Flex

def constantProp : Prop :=
  ∀ f : Int → Int,
    ∃ κ0 : Int → Int → Prop,
      ∀ x : Int, x > 0 →
        (∀ v : Int, v = f x → κ0 v x)
        ∧ (∀ z : Int, κ0 z x → z = f x)


set_option flex.benchPhases true
theorem constantProof : constantProp := by
  solve_fixpoint
