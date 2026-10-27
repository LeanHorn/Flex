import Flex.Tactic.Tactics.Flex

/-! `flex`: `zap`, then `fix` / `spacer` / `eldarica` for the cyclic κs, accepted
only when automation closes everything left. Spacer requires `z3` on PATH;
a missing `eld` only makes the Eldarica attempt fail. -/
namespace FlexDemo

-- Cyclic only: `zap` just normalizes, `fix` finds `0 ≤ i`.
theorem countdown :
    ∃ k : Int → Prop,
      k 5 ∧ (∀ i, k i → 1 ≤ i → k (i - 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex

-- κ2 is acyclic and eliminated by `zap`; κ1 is cyclic.
theorem mixed : ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
      (∀ y : Int, κ1 y → κ1 (y + 1))
    ∧ (∀ ν : Int, ν = 0 → κ1 ν)
    ∧ (∀ ν : Int, ν = 0 → κ2 ν)
    ∧ (∀ z : Int, κ2 z → 0 ≤ z) := by
  flex

-- A single CHC backend.
theorem boundedLoop :
    ∃ inv : Int → Int → Prop,
      (∀ limit, 0 ≤ limit → inv 0 limit) ∧
      (∀ x limit, inv x limit → x < limit → inv (x + 1) limit) ∧
      (∀ x limit, inv x limit → 0 ≤ x ∧ x ≤ limit) := by
  flex (backends := [spacer])

-- A closer that proves nothing rejects every backend: the goal is left as after `zap`.
theorem rejected : ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
      (∀ y : Int, κ1 y → κ1 (y + 1))
    ∧ (∀ ν : Int, ν = 0 → κ1 ν)
    ∧ (∀ ν : Int, ν = 0 → κ2 ν)
    ∧ (∀ z : Int, κ2 z → 0 ≤ z) := by
  flex (backends := [fix]) (closer := fail "no")
  exact ⟨fun y => 0 ≤ y, by grind⟩

-- An exhausted budget is not an error; the proof continues by hand.
theorem starved :
    ∃ k : Int → Prop,
      k 5 ∧ (∀ i, k i → 1 ≤ i → k (i - 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex (backends := [fix]) (config := { heartbeats := 1 })
  exact ⟨fun i => 0 ≤ i, by grind⟩

/-! ### Failure cases

Every failure below leaves a goal the proof can continue from. When `flex`
changes nothing, the unused-tactic linter says so; a closer that never succeeds
is reported as never executed, because its attempts were rolled back. -/

-- `fix`'s standard bank has no `x + y = 10`, so its invariant is too weak and
-- is rolled back; `spacer` then succeeds on the same goal.
theorem conserved :
    ∃ inv : Int → Int → Prop,
      inv 0 10 ∧
      (∀ x y, inv x y → 0 < y → inv (x + 1) (y - 1)) ∧
      (∀ x y, inv x y → x + y = 10) := by
  flex

-- Same goal with `fix` alone: nothing is solved, the goal is left as after `zap`.
theorem conservedByHand :
    ∃ inv : Int → Int → Prop,
      inv 0 10 ∧
      (∀ x y, inv x y → 0 < y → inv (x + 1) (y - 1)) ∧
      (∀ x y, inv x y → x + y = 10) := by
  flex (backends := [fix])
  exact ⟨fun x y => x + y = 10, by grind⟩

-- A solver that cannot be started is an ordinary failed attempt.
set_option flex.spacer.executable "no-such-solver" in
theorem missingSolver : ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
      (∀ y : Int, κ1 y → κ1 (y + 1))
    ∧ (∀ ν : Int, ν = 0 → κ1 ν)
    ∧ (∀ ν : Int, ν = 0 → κ2 ν)
    ∧ (∀ z : Int, κ2 z → 0 ≤ z) := by
  flex (backends := [spacer])
  exact ⟨fun y => 0 ≤ y, by grind⟩

-- A tight global budget: every step runs out and is rolled back, and the
-- reserved share is left for the manual proof.
set_option maxHeartbeats 800 in
theorem tightBudget :
    ∃ k : Int → Prop,
      k 5 ∧ (∀ i, k i → 1 ≤ i → k (i - 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex
  refine ⟨fun i => 0 ≤ i, ?_, ?_, ?_⟩ <;> intros <;> omega

-- `zap` and `fix` hit `maxRecDepth`; both are rolled back and `spacer` succeeds.
set_option maxRecDepth 30 in
theorem shallowRecursion :
    ∃ k : Int → Prop,
      k 5 ∧ (∀ i, k i → 1 ≤ i → k (i - 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex

-- An unprovable goal (the counter is unbounded): `flex` reports instead of
-- throwing, and the goal is left for the user. The `sorry` is intentional.
theorem unbounded :
    ∃ k : Int → Prop,
      k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → i ≤ 5) := by
  flex
  sorry

end FlexDemo
