import Flex

@[grind]
def mySum (n : Int) : Int :=
  if n ≤ 0 then 0 else n + mySum (n - 1)
termination_by n.toNat

@[simp]
def pleSumFuel4Prop : Prop :=
  ∀ x : Int, 0 ≤ mySum (x - 5) → 5 ≤ x → 15 ≤ mySum x

-- needs much more automation due to bounded x ≤ 5
set_option flex.benchPhases true
theorem pleSumFuel4Proof : pleSumFuel4Prop := by
  solve_fixpoint
