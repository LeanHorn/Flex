import Flex

def lhDefineFun01Prop
    (magic0 magic1 magic2 magic3 : Int → Prop) : Prop :=
  ∀ n0 : Int, True →
    ∀ _x : Int,
      (magic0 n0 ∧ magic1 n0 ∧ magic2 n0 ∧ magic3 n0) →
        magic3 n0

set_option flex.benchPhases true
theorem lhDefineFun01Proof :
    ∀ magic0 magic1 magic2 magic3 : Int → Prop,
    lhDefineFun01Prop magic0 magic1 magic2 magic3 := by
  solve_fixpoint
