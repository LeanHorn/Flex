import Flex.CHC.Script
import Flex.CHC.Solver

namespace Flex.CHC.Spacer

/-- The timeout covers writing the script, solving, and collecting the model.
Use an executable path or a name on PATH; invocation never goes through a shell. -/
structure Config where
  executable : String := "z3"
  timeoutMs : Nat := 10000
  deriving Inhabited

/-- Run Spacer on a PR4 export without touching Lean goals or assigning witnesses.

Z3's `-model` flag prints a model only after `sat`. Unlike appending `get-model`,
this does not cause a protocol error after `unsat` or `unknown`, and it needs only
one solver process and one check. Use the grouped-binder serializer for Spacer's
Horn preprocessing. Reconstructing and checking the returned definitions is a
separate step; `sat` by itself is not a Lean proof.
-/
def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult := do
  let process ← Process.run {
    executable := config.executable
    args := #["-in", "-smt2", "-model", "fp.engine=spacer"]
    timeoutMs := config.timeoutMs
  } problem.toSMTLib
  return SolverResult.ofProcess process

end Flex.CHC.Spacer
