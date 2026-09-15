import Flex

-- (datatype (MyData 1) ((mkdata ((field1 @(0))))))
-- A single-field record parameterised by α; `@(0)` = first type parameter.
structure MyData (α : Type) where
  mkdata :: field1 : α

-- (constraint
--   (forall ((x (MyData (Set_Set int))) ((Set_mem 0 (field1 x))))
--     ((Set_mem 0 (field1 x)))))
-- Sets are modeled mathlib-free as `List` (membership `∈` is core Lean).
def issue701 : Prop :=
  ∀ x : MyData (List Int), 0 ∈ x.field1 → 0 ∈ x.field1

set_option flex.benchPhases true
theorem issue701_proof : issue701 := by
  solve_fixpoint
