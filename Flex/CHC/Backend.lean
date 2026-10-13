import Flex.CHC.Spacer
import Flex.CHC.Eldarica

namespace Flex.CHC

/-- Select one CHC solver. Selection is explicit; this API does not fall back to
another solver or to predicate abstraction. -/
inductive Backend where
  | spacer
  | eldarica
  deriving Inhabited, Repr, BEq

/-- Shared configuration for one solver request. With no executable override,
Spacer uses `z3` and Eldarica uses `eld`, resolved on PATH. Overrides name an
executable or launcher, not a shell command. No environment-variable overrides
are read by the library; applications may supply them explicitly. -/
structure Config where
  backend : Backend := .spacer
  executable : Option String := none
  timeoutMs : Nat := 10000
  deriving Inhabited, Repr

/-- Run the selected backend on a checked export and retain its complete process
transcript. `sat` supplies candidate definitions; importing, assigning witnesses,
and proving the original constraints remain separate operations. -/
def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult :=
  match config.backend with
  | .spacer => Spacer.run problem {
      executable := config.executable.getD ({} : Spacer.Config).executable
      timeoutMs := config.timeoutMs }
  | .eldarica => Eldarica.run problem {
      executable := config.executable.getD ({} : Eldarica.Config).executable
      timeoutMs := config.timeoutMs }

end Flex.CHC
