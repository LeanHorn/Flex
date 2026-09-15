import Flex
/-
(fixpoint "--eliminate=horn")


(constraint
  (and
    (forall ((x Int) ((> x 0)))
      (and
        (forall ((y Int) ((> y x)))
          (forall ((v Int) ((= v (+ x y))))
            ((> v 0))))
        (forall ((z Int) ((> z 100)))
          (forall ((v Int) ((= v (+ x z))))
            ((> v 100))))))))
-/

def sumRec2Prop : Prop :=
  ∀ x : Int, x > 0 →
    (∀ y : Int, y > x → ∀ v : Int, v = x + y → v > 0)
    ∧ (∀ z : Int, z > 100 → ∀ v : Int, v = x + z → v > 100)

set_option flex.benchPhases true
theorem sumRec2Proof : sumRec2Prop := by
  solve_fixpoint
