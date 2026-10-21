import Flex.Tactic.Tactics.Spacer
import Flex.Tactic.Tactics.Eldarica

/-! Spacer and Eldarica remove proved heads and leave one VC for grind.
Requires `z3` and `eld` on PATH, or the `flex.spacer.executable` /
`flex.eldarica.executable` options. -/
namespace SpacerDemo

-- An increasing counter stays nonnegative.
theorem counter :
    ∃ inv : Int → Prop,
      inv 0 ∧
      (∀ x, inv x → inv (x + 1)) ∧
      (∀ x, inv x → 0 ≤ x) := by
  spacer
  grind

-- The bound is a predicate argument, so one invariant covers every loop limit.
theorem boundedLoop :
    ∃ inv : Int → Int → Prop,
      (∀ limit, 0 ≤ limit → inv 0 limit) ∧
      (∀ x limit, inv x limit → x < limit → inv (x + 1) limit) ∧
      (∀ x limit, inv x limit → 0 ≤ x ∧ x ≤ limit) := by
  eldarica
  grind

-- A Boolean flag selects increasing or decreasing motion from zero.
theorem booleanBranches :
    ∃ inv : Bool → Int → Prop,
      inv true 0 ∧ inv false 0 ∧
      (∀ x, inv true x → inv true (x + 1)) ∧
      (∀ x, inv false x → inv false (x - 1)) ∧
      (∀ x, inv true x → 0 ≤ x) ∧
      (∀ x, inv false x → x ≤ 0) := by
  spacer
  grind

-- Two mutually dependent predicates describe adjacent program locations.
theorem linkedPredicates :
    ∃ entry exit : Int → Prop,
      entry 0 ∧ exit 1 ∧
      (∀ x, entry x → entry (x + 1)) ∧
      (∀ x, exit x → exit (x + 1)) ∧
      (∀ x, entry x → exit (x + 1)) ∧
      (∀ x, exit x → entry x) ∧
      (∀ x, entry x → 0 ≤ x) ∧
      (∀ x, exit x → 1 ≤ x) := by
  eldarica
  grind

-- A nonlinear Horn clause has two predicate premises; its arithmetic stays linear.
theorem nonlinearBody :
    ∃ inv : Int → Prop,
      inv 0 ∧ inv 1 ∧
      (∀ x y, inv x → inv y → inv (x + y)) ∧
      (∀ x, inv x → 0 ≤ x) := by
  spacer
  grind

-- The second branch introduces a separate entry point above the bounded loop.
theorem disjunctiveGuard :
    ∃ inv : Int → Prop,
      inv 0 ∧
      (∀ x, (inv x ∧ x < 10 ∨ x = 20) → inv (x + 1)) ∧
      (∀ x, inv x → 0 ≤ x ∧ x ≤ 21) := by
  eldarica
  grind

-- Synthesis supplies a relational invariant; the conservation VC remains explicit.
theorem fuelConservation :
    ∃ inv : Int → Int → Prop,
      inv 0 10 ∧
      (∀ steps fuel, inv steps fuel → 0 < fuel → inv (steps + 1) (fuel - 1)) ∧
      (∀ steps fuel, inv steps fuel → steps + fuel = 10 ∧ 0 ≤ fuel) := by
  spacer
  grind

end SpacerDemo
