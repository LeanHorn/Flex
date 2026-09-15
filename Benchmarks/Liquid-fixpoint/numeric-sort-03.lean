import Flex


@[qualif] def q_eq_zero (v : Int)   : Prop := v = 0
@[qualif] def q_gt_zero (v : Int)   : Prop := 0 < v
@[qualif] def q_ge_zero (v : Int)   : Prop := 0 ≤ v
@[qualif] def q_lt_zero (v : Int)   : Prop := v < 0
@[qualif] def q_le_zero (v : Int)   : Prop := v ≤ 0
@[qualif] def q_eq      (a b : Int) : Prop := a = b
@[qualif] def q_gt      (a b : Int) : Prop := a > b
@[qualif] def q_ge      (a b : Int) : Prop := a ≥ b
@[qualif] def q_lt      (a b : Int) : Prop := a < b
@[qualif] def q_le      (a b : Int) : Prop := a ≤ b
@[qualif] def q_le1     (a b : Int) : Prop := a ≤ b - 1


def numericSort03Prop : Prop :=
  ∃ κ1 : Int → Int → Prop,
    ∀ zero : Int, zero = 0 →
      (∀ n : Int, n ≤ zero → ∀ VV : Int, VV = zero → κ1 VV zero)
      ∧ (∀ n : Int, 0 < n → ∀ n1 : Int, n1 = n - 1 →
          ∀ t1 : Int, κ1 t1 zero → ∀ v : Int, v = n + t1 → κ1 v zero)
      ∧ (∀ y : Int, ∀ r : Int, κ1 r zero → zero ≤ r)

set_option flex.benchPhases true
theorem numericSort03Proof : numericSort03Prop := by
  solve_fixpoint
