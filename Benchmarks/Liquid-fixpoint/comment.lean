import Flex
/-
  Demo: prove comment_vc by hoisting cut kvars to the front, then refining
  with metavariables for them. Cut kvars become outer mvars; the inner ∃'s
  for acyclic kvars + body becomes the residual goal.
-/

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
@[qualif] def q_diff    (v a b : Int) : Prop := v = a - b

-- Original: ∃ k1 k2 k3 k0 k5 k4, body  (acyclic-first)
def comment_vc : Prop :=
  ∃ k1 : Int → Int → Prop,
  ∃ k2 : Int → Int → Int → Prop,
  ∃ k3 : Int → Int → Int → Prop,
  ∃ k0 : Int → Int → Int → Prop,
  ∃ k5 : Int → Int → Int → Prop,
  ∃ k4 : Int → Int → Int → Prop,
    ∀ a0 : Int, ∀ a1 : Int, ∀ a2 : Bool,
      a0 < a1 →
        (a2 = false →
            k0 a1 a0 a1
          ∧ k1 a0 a1
          ∧ k2 a0 a0 a1
          ∧ (∀ a3 : Int, k0 a3 a0 a1 → k3 a3 a0 a1)
          ∧ (∀ a4 : Int, k0 a4 a0 a1 → k4 a4 a0 a1)
          ∧ (∀ a5 : Int, k4 a5 a0 a1 → k0 a5 a0 a1))
      ∧ (a2 = true →
            k5 a0 a0 a1
          ∧ k1 a0 a1
          ∧ (∀ a6 : Int, k5 a6 a0 a1 → k2 a6 a0 a1)
          ∧ k3 a1 a0 a1
          ∧ (∀ a7 : Int, k5 a7 a0 a1 → k4 a7 a0 a1)
          ∧ (∀ a8 : Int, k4 a8 a0 a1 → k5 a8 a0 a1))
      ∧ (k1 a0 a1 →
          ∀ a9 : Int, k4 a9 a0 a1 →
              (∀ a10 : Int, a10 = a9 + 1 → k4 a10 a0 a1)
            ∧ (∀ a11 : Int, k4 a11 a0 a1 →
                ∀ a12 : Int, k2 a12 a0 a1 →
                  ∀ a13 : Int, k3 a13 a0 a1 →
                    0 ≤ a11 - a0))

set_option flex.benchPhases true
theorem test : comment_vc := by
  fusion
  solve_fixpoint
