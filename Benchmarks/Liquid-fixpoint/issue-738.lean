import Flex

-- Sets are modeled mathlib-free as `List` (membership `∈` is core Lean).
structure MyData (α : Type) where
  mkdata :: field1 : α

def issue701 : Prop :=
  ∀ x : MyData (List Int), 0 ∈ x.field1 → 0 ∈ x.field1

set_option flex.benchPhases true
theorem issue701_proof : issue701 := by
  solve_fixpoint
