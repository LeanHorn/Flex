import Flex

inductive MyList (α : Type) where
  | nil  : MyList α
  | cons : α → MyList α → MyList α

def myLen : MyList α → Int
  | .nil       => 0
  | .cons _ xs => 1 + myLen xs

def ple1Prop : Prop :=
  ∀ x : Int, True → ∀ y : Int, y = 2 → ∀ z : Int, z = 3 →
    myLen (MyList.cons x (MyList.cons y (MyList.cons z MyList.nil))) = 3

set_option flex.benchPhases true
theorem ple1Proof : ple1Prop := by
  solve_fixpoint
