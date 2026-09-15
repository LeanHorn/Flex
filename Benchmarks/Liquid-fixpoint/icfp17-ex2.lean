import Flex


def icfp17Ex2Prop : Prop :=
  ∃ κx : Int → Int → Int → Int → Prop,
  ∃ κy : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ n : Int, n = x - 1 →
        ∀ p : Int, p = x + 1 →
          (∀ v : Int, v = n → κx v x n p)
          ∧ (∀ v : Int, v = p → κy v x)
          ∧ (∀ v : Int, κx v x n p → κy v x))
      ∧ (∀ y : Int, κy y x → ∀ v : Int, v = y + 1 → 0 ≤ v)

set_option flex.benchPhases true
theorem icfp17Ex2Proof : icfp17Ex2Prop := by
  solve_fixpoint
