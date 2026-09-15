import Flex
/-
(fixpoint "--eliminate=horn")


(qualif Foo ((v Int) (x Int)) (= v x))
(qualif Bar ((v Int) (x Int)) (> v x))

(var $k1 (Int Int Int))
(var $k2 (Int Int Int))
(var $k3 (Int Int Int))





(constraint
  (and
    (forall ((x Int) ((> x 0)))
      (forall ((y Int) ((> y x)))
        (forall ((v Int) ((= v (+ x y))))
          ((> v 0)))))))
-/

def sumRec1Prop : Prop :=
  ∀ x : Int, x > 0 → ∀ y : Int, y > x → ∀ v : Int, v = x + y → v > 0

set_option flex.benchPhases true
theorem sumRec1Proof : sumRec1Prop := by
  solve_fixpoint
