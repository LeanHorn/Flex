import Flex
/-
(fixpoint "--eliminate=horn")

(qualif Foo ((v Int)) (> v 100))

(var $k0 (Int))

(constraint
  (and
    (forall ((x Int) ((> x 0)))
      (and
        (forall ((y Int) ((> y (+ x 100))))
          (forall ((v Int) ((= v (+ x y))))
            ($k0 v)))
        (forall ((z Int) ($k0 z))
          (forall ((v Int) ((= v (+ x z))))
            ((> v 100))))))))
-/

def sumRec3Prop : Prop :=
  ∃ κ0 : Int → Int → Prop,
    ∀ x : Int, x > 0 →
      (∀ y : Int, y > x + 100 → ∀ v : Int, v = x + y → κ0 v x)
      ∧ (∀ z : Int, κ0 z x → ∀ v : Int, v = x + z → v > 100)

set_option flex.benchPhases true
theorem sumRec3Proof : sumRec3Prop := by
  solve_fixpoint
