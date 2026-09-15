import Flex

def adder (x y : Int) : Int := x + y

def adderProp : Prop :=
  ∀ x : Int, x = 5 → ∀ y : Int, y = 6 → adder x y = 11

set_option flex.benchPhases true
theorem adderProof : adderProp := by
  solve_fixpoint  -- unfolds adder, omega closes
