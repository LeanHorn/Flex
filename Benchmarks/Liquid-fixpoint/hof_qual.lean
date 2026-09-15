/-
(fixpoint "--allowho")
(fixpoint "--allowhoqs")
(fixpoint "--scrape=head")

(var $k0 (Int (func 0 (Int) bool)))

(constraint
  (and
    (forall ((p0 (func 0 (Int) bool)) (true))
      (and
        (forall ((x Int) ((p0 x)))
          ($k0 x p0))
        (forall ((y Int) ($k0 y p0))
          (forall ((v Int) ((= v y)))
            ($k0 v p0)))
        (forall ((z Int) ($k0 z p0))
          ((p0 z)))))))
-/
import Flex

-- The HO qualifier corresponding to `--allowhoqs --scrape=head`:
-- "the predicate holds at the int slot"
@[qualif] def q_apply (x : Int) (p : Int → Prop) : Prop := p x
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

def hofQual : Prop :=
  -- $k0 : (Int (func 0 (Int) bool))   in Liquid-Fixpoint
  --     ↦  Int → (Int → Prop) → Prop  in Lean
  ∃ k0 : Int → (Int → Prop) → Prop,
    -- ∀ p0 : Int → Prop, with no precondition (the SMT `(true)` guard)
    ∀ p0 : Int → Prop,
        -- Seed:  ∀ x, p0 x → k0 x p0
        (∀ x : Int, p0 x → k0 x p0)
        -- Idempotent step:  ∀ y, k0 y p0 → ∀ v, v = y → k0 v p0
      ∧ (∀ y : Int, k0 y p0 → ∀ v : Int, v = y → k0 v p0)
        -- Consumer:  ∀ z, k0 z p0 → p0 z
      ∧ (∀ z : Int, k0 z p0 → p0 z)

set_option maxHeartbeats 800000 in
set_option flex.benchPhases true
theorem hofQual_proof : hofQual := by
  solve_fixpoint
