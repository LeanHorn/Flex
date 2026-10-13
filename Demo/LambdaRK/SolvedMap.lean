import Demo.LambdaRK.MapVC
import Flex.CHC

/-!
A real solver certificate for the generated polymorphic `map` VC. Run with
`lake lean Demo/LambdaRK/SolvedMap.lean`; it uses Spacer (`z3` on PATH).
Set `CHC_ELDARICA=/path/to/eld` to run the same check with Eldarica.

The external solver chooses the predicate. Flex imports its model, Lean proves
all scalar clauses, and `lowering_sound` proves the original generated VC.
This is a solver viability gate, not yet source-program total correctness.
-/
namespace LambdaRK.Examples.MapVC

open Lean Meta Elab Tactic

elab "synthesize_map_invariant" : tactic => withMainContext do
  let config : Flex.CHC.Config := match ← IO.getEnv "CHC_ELDARICA" with
    | some executable => { backend := .eldarica, executable := some executable }
    | none => { backend := .spacer }
  let report ← match ← Flex.CHC.solveGoal (← getMainGoal) config with
    | .solved report => pure report
    | .partial report =>
      throwError "map invariant left {report.certificate.obligations.size} uncertified clauses"
    | .failed failure =>
      throwError "map synthesis failed at {repr failure.stage}: {failure.message}"
  unless report.problem.relations.size == 1 && report.problem.clauseCount == 3 do
    throwError "map scalarization unexpectedly changed its relation or clause count"
  for witness in report.witnesses do
    logInfo m!"map invariant ({repr config.backend}): {witness.value}"
  for timing in report.timings do
    logInfo m!"map {repr timing.stage}: {timing.elapsedNs / 1000000} ms"
  setGoals []

/-- The witness is imported from the actual solver response and every clause
is then certified; no handwritten predicate is supplied by this theorem. -/
theorem scalar_solved : ∃ candidate, Scalar candidate := by
  change ∃ candidate : Int → Int → Prop,
    candidate 0 0 ∧
    (∀ input output, candidate input output → candidate (1 + input) (1 + output)) ∧
    (∀ input output, candidate input output → output = input)
  synthesize_map_invariant

/-- The proof targets `generate signature map mapTy`, not a handwritten scalar
toy. Its only solver dependency is the checked witness in `scalar_solved`. -/
theorem generated_valid : ∃ κ constraints,
    generate signature map mapTy = .ok constraints ∧ constraints.Valid signature κ := by
  obtain ⟨candidate, certified⟩ := scalar_solved
  exact ⟨assignment candidate, raw, generated, lowering_sound candidate certified⟩

run_elab do
  for theoremName in [``scalar_solved, ``generated_valid] do
    let axioms ← collectAxioms theoremName
    unless axioms.all (fun name => name == ``propext || name == ``Classical.choice ||
        name == ``Quot.sound) do
      throwError "map certificate contains a nonstandard axiom: {theoremName}: {axioms}"

end LambdaRK.Examples.MapVC
