import Flex.CHC.Export
import Flex.CHC.Process
import Smt2Lean.SolverResponse

namespace Flex.CHC

/-- `sat` contains candidate predicate definitions, not Lean witnesses or proofs. -/
inductive SolverOutcome where
  | sat (model : Array Smt2Lean.Source.Command)
  | unsat
  | unknown (diagnostics : Array Smt2Lean.SolverResponse.Diagnostic)
  | timedOut
  | error (message : String)
  deriving Inhabited

/-- The decoded outcome and complete process transcript. -/
structure SolverResult where
  outcome : SolverOutcome
  process : Process.Result
  deriving Inhabited

private def parseOutcome (stdout : String) : SolverOutcome :=
  match Smt2Lean.SolverResponse.parse stdout "chc-solver" with
  | .error message => .error message
  | .ok response => Id.run do
    let errors := response.diagnostics.filter (·.kind == .error)
    unless errors.isEmpty do
      return .error (String.intercalate "\n" (errors.toList.map (·.message)))
    match response.status with
    | some .sat =>
      match response.model with
      | some definitions => return .sat definitions
      | none => return .error "CHC solver returned sat without a model"
    | some .unsat => return .unsat
    | some .unknown => return .unknown response.diagnostics
    | none => return .error "CHC solver response is missing a check-sat status"

/-- Decode successful processes only. Reject error diagnostics and missing models;
an explicitly empty model is valid. -/
def SolverResult.ofProcess (process : Process.Result) : SolverResult :=
  let outcome := match process.completion with
    | .exited 0 => parseOutcome process.stdout
    | .exited code => .error s!"CHC solver exited with code {code}"
    | .timedOut => .timedOut
    | .spawnError message => .error s!"Could not start CHC solver: {message}"
    | .ioError message => .error s!"CHC solver I/O failed: {message}"
  { outcome, process }

namespace Spacer

/-- The executable is invoked directly; the timeout covers the whole request. -/
structure Config where
  executable : String := "z3"
  timeoutMs : Nat := 10000
  deriving Inhabited

/-- Run Spacer on a checked export. `-model` prints definitions only after `sat`,
avoiding the protocol error from `get-model` after `unsat` or `unknown`. -/
def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult := do
  let process ← Process.run {
    executable := config.executable
    args := #["-in", "-smt2", "-model", "fp.engine=spacer"]
    timeoutMs := config.timeoutMs
  } problem.toSMTLib
  return SolverResult.ofProcess process

end Spacer

namespace Eldarica

/-- The executable or launcher is invoked directly; the timeout covers the whole request. -/
structure Config where
  executable : String := "eld"
  timeoutMs : Nat := 10000
  deriving Inhabited

/-- Run Eldarica with SMT-LIB Horn input and SMT-LIB predicate interpretations. -/
def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult := do
  let process ← Process.run {
    executable := config.executable
    args := #["-in", "-hsmt", "-ssol"]
    timeoutMs := config.timeoutMs
  } problem.toSMTLib
  return SolverResult.ofProcess process

end Eldarica

/-- Select one CHC solver; there is no automatic fallback. -/
inductive Backend where
  | spacer
  | eldarica
  deriving Inhabited, Repr, BEq

/-- With no executable override, resolve `z3` or `eld` on PATH.
Overrides name an executable or launcher, not a shell command. -/
structure Config where
  backend : Backend := .spacer
  executable : Option String := none
  timeoutMs : Nat := 10000
  deriving Inhabited, Repr

/-- Run the selected solver and retain its transcript. Importing candidates and
proving the original constraints are separate operations. -/
def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult :=
  match config.backend with
  | .spacer => Spacer.run problem {
      executable := config.executable.getD ({} : Spacer.Config).executable
      timeoutMs := config.timeoutMs }
  | .eldarica => Eldarica.run problem {
      executable := config.executable.getD ({} : Eldarica.Config).executable
      timeoutMs := config.timeoutMs }

end Flex.CHC
