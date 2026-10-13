import Demo.LambdaRK.MapVC
import Flex.VCG.LambdaRK.Correctness
import Flex.VCG.LambdaRK.Bridge.Goal

/-!
A real solver certificate for the generated polymorphic `map` VC. Run with
`lake lean Demo/LambdaRK/SolvedMap.lean`; it uses Spacer (`z3` on PATH).
Set `CHC_ELDARICA=/path/to/eld` to run the same check with Eldarica.

The generic frontend reads the source constraint and signature, derives scalar
clauses, and checks their connection to the source semantics. The external solver
chooses the predicate; Lean certifies it and establishes source-program total
correctness under the constructed datatype model. No map-specific scalar clauses,
measure lemmas, or invariant are supplied by this file.
-/
namespace LambdaRK.Examples.MapVC

open Lean Meta Elab Tactic

elab "synthesize_map_invariant" : tactic => withMainContext do
  let config : Flex.CHC.Config := match ← IO.getEnv "CHC_ELDARICA" with
    | some executable => { backend := .eldarica, executable := some executable }
    | none => { backend := .spacer }
  let report ← match ← LambdaRK.Bridge.solveGoal (← getMainGoal) config with
    | .solved report => pure report
    | .partial report =>
      throwError "map invariant left {report.obligations.size} obligations: {repr report.diagnostics}"
    | .failed message => throwError "map synthesis failed: {message}"
  unless report.checkedClauses == 4 && report.diagnostics.isEmpty do
    throwError "map source lowering unexpectedly changed: {repr report.diagnostics}"
  let some solver := report.solver
    | throwError "map synthesis unexpectedly bypassed the external solver"
  unless solver.problem.relations.size == 1 && solver.problem.clauseCount == 3 do
    throwError "map scalarization unexpectedly changed its relation or clause count"
  for (name, value) in report.witnesses do
    logInfo m!"map invariant {name} ({repr config.backend}): {value}"
  for timing in solver.timings do
    logInfo m!"map {repr timing.stage}: {timing.elapsedNs / 1000000} ms"
  setGoals []

/-- The witness is imported from the actual solver response and every clause
is then certified; no handwritten predicate is supplied by this theorem. -/
theorem raw_solved : ∃ assignment, raw.Valid signature assignment := by
  synthesize_map_invariant

/-- The proof targets `generate signature map mapTy`, not a handwritten scalar
toy. Its only solver dependency is the checked witness in `raw_solved`. -/
theorem generated_valid : ∃ κ constraints,
    generate signature map mapTy = .ok constraints ∧ constraints.Valid signature κ := by
  obtain ⟨assignment, certified⟩ := raw_solved
  exact ⟨assignment, raw, generated, certified⟩

/-- Both real solver paths certify the source program's semantic type, including
its impredicative function and length-preservation specification. -/
theorem map_total_correct : ∃ κ value,
    Eval signature [] none map value ∧
      mapTy.denote signature (signature.datatypeModel κ) κ [] [] value := by
  obtain ⟨κ, constraint, generated, valid⟩ := generated_valid
  obtain ⟨value, evaluated, typed⟩ := generated_total_correctness
    signature κ map mapTy constraint generated valid
  exact ⟨κ, value, evaluated, typed⟩

run_elab do
  for theoremName in [``raw_solved, ``generated_valid, ``map_total_correct] do
    let axioms ← collectAxioms theoremName
    unless axioms.all (fun name => name == ``propext || name == ``Classical.choice ||
        name == ``Quot.sound) do
      throwError "map certificate contains a nonstandard axiom: {theoremName}: {axioms}"

end LambdaRK.Examples.MapVC
