import Flex.Tactic.Tactics.Flex

/-! `flex` prepares constraints, runs Zap and the invariant backends, and keeps
validated progress when proof obligations still need manual work. -/

namespace FlexDemo

-- The default portfolio starts with Fix and deep qualifier scraping.
theorem countdown :
    ∃ k : Int → Prop,
      k 5 ∧ (∀ i, k i → 1 ≤ i → k (i - 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex

-- Zap eliminates the acyclic predicate before solving the cyclic one.
theorem mixed : ∃ loop seed : Int → Prop,
    seed 0 ∧ (∀ i, seed i → loop i) ∧
    (∀ i, loop i → loop (i + 1)) ∧ (∀ i, loop i → 0 ≤ i) := by
  flex

-- Select a single backend when desired; Spacer needs z3 on PATH.
theorem boundedLoop :
    ∃ inv : Int → Int → Prop,
      (∀ limit, 0 ≤ limit → inv 0 limit) ∧
      (∀ x limit, inv x limit → x < limit → inv (x + 1) limit) ∧
      (∀ x limit, inv x limit → 0 ≤ x ∧ x ≤ limit) := by
  flex (backends := [spacer])

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

-- A failing closer keeps the validated invariant and leaves a structured VC.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem manualResidual :
    ∃ k : Int → Prop,
      k 5 ∧ (∀ i, k i → 1 ≤ i → k (i - 1)) ∧
      (∀ i, k i → 0 ≤ i) ∧ (∀ n, double n = n + n) := by
  flex (backends := [fix]) (closer := fail "manual residual")
  have hd : ∀ n, double n = n + n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [double, ih]; omega
  all_goals grind

-- Predicate constraints can occur under quantifiers and conjunctions.
theorem nested : ∀ start : Int, 0 ≤ start →
    (∃ k : Int → Prop,
      k start ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i)) ∧
    0 ≤ start + 1 := by
  flex

-- Nesting is optional, and an empty backend list gives the Zap-only pipeline.
theorem zapOnly : ∃ k : Int → Prop,
    (∀ i, 0 ≤ i → k i) ∧ (∀ i, k i → 0 ≤ i) := by
  flex (backends := []) (config := { nesting := true })

end FlexDemo
