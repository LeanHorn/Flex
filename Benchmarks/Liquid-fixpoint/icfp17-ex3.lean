import Flex

def icfp17Ex3Prop : Prop :=
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ v : Int, v = a - 1 → κb v)
    ∧ (∀ b : Int, κb b → ∀ v : Int, v = b + 1 → κc v)
    ∧ (∀ v : Int, 0 ≤ v → κa v)
    ∧ (∀ v : Int, κc v → 0 ≤ v)

set_option flex.benchPhases true
theorem icfp17Ex3Proof : icfp17Ex3Prop := by
  solve_fixpoint
