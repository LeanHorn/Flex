import Flex
/-
NOTE: THIS REQUIRES
  1. QUALIFIER INFERENCE (sort of loop invariant inference)
  2. Predicate abstraction for cyclic kvars

(fixpoint "--scrape=both")

(var $k0 (Int Int Int))
(var $k1 (Int Int Int Int))

(datatype (Pair 2)
 ((Pair ((fst @(0)) (snd @(1))))))
(datatype (Unit 0)
 ((Unit ())))

(constraint
  (and
    (forall ((a0 Int) (true))
      (forall ((a1 Int) (true))
        (forall ((_ Unit) ((>= a0 0)))
          (forall ((_ Unit) ((<= a0 a1)))
            (forall ((_ Unit) ((>= a1 0)))
              (and
                (forall ((a2 Int) ((= a2 0)))
                  (and
                    ($k0 a0 a0 a1)
                    ($k1 a2 a0 a0 a1)))
                (forall ((a3 Int) (true))
                  (forall ((a4 Int) (true))
                    (forall ((_ Unit) (and ($k0 a4 a0 a1) ($k1 a3 a4 a0 a1)))
                      (and
                        (forall ((_ Unit) ((not (< a4 a1))))
                          ((= a3 (- a1 a0))))
                        (forall ((_ Unit) ((< a4 a1)))
                          (forall ((a5 Int) ((= a5 (+ a3 1))))
                            (forall ((a6 Int) ((= a6 (+ a4 1))))
                              (and
                                ($k0 a6 a0 a1)
                                ($k1 a5 a6 a0 a1)))))))))))))))))
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

-- k0 has 3 params, k1 has 4 params
def scrape00Prop : Prop :=
  ∃ κ0 : Int → Int → Int → Prop,
  ∃ κ1 : Int → Int → Int → Int → Prop,
    ∀ a0 : Int, ∀ a1 : Int,
      ∀ _u1 : Int, a0 ≥ 0 →
      ∀ _u2 : Int, a0 ≤ a1 →
      ∀ _u3 : Int, a1 ≥ 0 →
      (∀ a2 : Int, a2 = 0 →
        κ0 a0 a0 a1 ∧ κ1 a2 a0 a0 a1)
      ∧ (∀ a3 : Int, ∀ a4 : Int,
          κ0 a4 a0 a1 → κ1 a3 a4 a0 a1 →
          (∀ _u4 : Int, a4 ≥ a1 → a3 = a1 - a0)
          ∧ (∀ _u5 : Int, a4 < a1 →
              ∀ a5 : Int, a5 = a3 + 1 →
              ∀ a6 : Int, a6 = a4 + 1 →
              κ0 a6 a0 a1 ∧ κ1 a5 a6 a0 a1))

set_option maxRecDepth 1000 in
set_option flex.benchPhases true
theorem scrape00Proof : scrape00Prop := by
  solve_fixpoint
