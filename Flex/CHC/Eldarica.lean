import Flex.CHC.Script
import Flex.CHC.Solver

namespace Flex.CHC.Eldarica

/-- Run the Eldarica executable (or its launcher script) directly. The positive
wall-clock timeout includes startup, input, solving, and output collection. -/
structure Config where
  executable : String := "eld"
  timeoutMs : Nat := 10000
  deriving Inhabited

/-- Ask Eldarica for a model of the exported Horn constraints.

`-in -hsmt` selects SMT-LIB Horn input on stdin; `-ssol` prints the satisfying
predicate interpretations in SMT-LIB format. Both the native executable and the
standard launcher can be supplied via `executable`. Response decoding and process
cleanup use the same implementation as Spacer. No Lean goal or witness is changed.
-/
def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult := do
  let process ← Process.run {
    executable := config.executable
    args := #["-in", "-hsmt", "-ssol"]
    timeoutMs := config.timeoutMs
  } problem.toSMTLib
  return SolverResult.ofProcess process

end Flex.CHC.Eldarica
