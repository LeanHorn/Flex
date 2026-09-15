import Flex

inductive Vec (α : Type) where
  | vnil  : Vec α
  | vcons : α → Vec α → Vec α

def vecLen : Vec α → Int
  | .vnil       => 0
  | .vcons _ xs => 1 + vecLen xs

def pleListProp : Prop :=
  ∀ x : Int, True → ∀ y : Int, y = 2 → ∀ z : Int, z = 3 →
    vecLen (Vec.vcons x (Vec.vcons y (Vec.vcons z Vec.vnil))) = 3

set_option flex.benchPhases true
theorem pleListProof : pleListProp := by
  solve_fixpoint
