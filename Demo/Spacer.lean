import Flex.CHC

/-! Invariant synthesis with Spacer and kernel-checked Lean proofs.
Run `lake lean Demo/Spacer.lean` with `z3` on PATH, or set
`CHC_ELDARICA=/path/to/eld` to use Eldarica for the same examples. -/
namespace SpacerDemo

open Lean Elab Tactic Flex.CHC

-- `manual` keeps the synthesized predicates but leaves certification to the caller.
elab "chc" manual:("manual")? : tactic => withMainContext do
  let config : Flex.CHC.Config := match ← IO.getEnv "CHC_ELDARICA" with
    | some executable => { backend := .eldarica, executable := some executable }
    | none => { backend := .spacer }
  let oracle : ProofOracle :=
    if manual.isSome then fun _ => pure none else defaultProofOracle
  match ← solveGoal (← getMainGoal) config oracle with
  | .solved _ => replaceMainGoal []
  | .partial report =>
    replaceMainGoal (report.certificate.obligations.toList.map (·.goal))
  | .failed failure =>
    throwError "CHC {repr failure.stage}: {failure.message}"

-- An increasing counter stays nonnegative.
theorem counter :
    ∃ inv : Int → Prop,
      inv 0 ∧
      (∀ x, inv x → inv (x + 1)) ∧
      (∀ x, inv x → 0 ≤ x) := by
  chc

-- The bound is a predicate argument, so one invariant covers every loop limit.
theorem boundedLoop :
    ∃ inv : Int → Int → Prop,
      (∀ limit, 0 ≤ limit → inv 0 limit) ∧
      (∀ x limit, inv x limit → x < limit → inv (x + 1) limit) ∧
      (∀ x limit, inv x limit → 0 ≤ x ∧ x ≤ limit) := by
  chc

-- A Boolean flag selects increasing or decreasing motion from zero.
theorem booleanBranches :
    ∃ inv : Bool → Int → Prop,
      inv true 0 ∧ inv false 0 ∧
      (∀ x, inv true x → inv true (x + 1)) ∧
      (∀ x, inv false x → inv false (x - 1)) ∧
      (∀ x, inv true x → 0 ≤ x) ∧
      (∀ x, inv false x → x ≤ 0) := by
  chc

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
  chc

-- A nonlinear Horn clause has two predicate premises; its arithmetic stays linear.
theorem nonlinearBody :
    ∃ inv : Int → Prop,
      inv 0 ∧ inv 1 ∧
      (∀ x y, inv x → inv y → inv (x + y)) ∧
      (∀ x, inv x → 0 ≤ x) := by
  chc

-- The second branch introduces a separate entry point above the bounded loop.
theorem disjunctiveGuard :
    ∃ inv : Int → Prop,
      inv 0 ∧
      (∀ x, (inv x ∧ x < 10 ∨ x = 20) → inv (x + 1)) ∧
      (∀ x, inv x → 0 ≤ x ∧ x ≤ 21) := by
  chc

-- Synthesis supplies a relational invariant; ordinary Lean tactics certify it.
theorem fuelConservation :
    ∃ inv : Int → Int → Prop,
      inv 0 10 ∧
      (∀ steps fuel, inv steps fuel → 0 < fuel → inv (steps + 1) (fuel - 1)) ∧
      (∀ steps fuel, inv steps fuel → steps + fuel = 10 ∧ 0 ≤ fuel) := by
  chc manual
  all_goals omega

end SpacerDemo
