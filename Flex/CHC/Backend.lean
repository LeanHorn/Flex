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
  timeoutMs : Nat := 30000
  inlining : Bool := false
  deriving Inhabited

/-- Keep predicate interpretations compact; normal inlining is available on retry. -/
def Config.toProcessConfig (config : Config) : Process.Config :=
  {
    executable := config.executable
    args := #["-in", "-smt2", "-model", "fp.engine=spacer"] ++
      (if config.inlining then #[] else
        #["fp.xform.inline_eager=false", "fp.xform.inline_linear=false"])
    timeoutMs := config.timeoutMs }

def runScript (input : String) (config : Config := {}) : IO SolverResult := do
  let process ← Process.run config.toProcessConfig input
  return SolverResult.ofProcess process

def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult :=
  runScript problem.toSMTLib config

end Spacer

namespace Eldarica

/-- The executable or launcher is invoked directly; the timeout covers the whole request. -/
structure Config where
  executable : String := "eld"
  timeoutMs : Nat := 30000
  intervals : Bool := true
  largeBlockEncoding : Bool := false
  deriving Inhabited

/-- Use SMT-LIB Horn input and request predicate interpretations. -/
def Config.toProcessConfig (config : Config) : Process.Config :=
  {
    executable := config.executable
    args := #["-in", "-hsmt", "-ssol"] ++
      (if config.intervals then #[] else #["-noIntervals"]) ++
      (if config.largeBlockEncoding then #["-lbe"] else #[])
    timeoutMs := config.timeoutMs }

def runScript (input : String) (config : Config := {}) : IO SolverResult := do
  let process ← Process.run config.toProcessConfig input
  return SolverResult.ofProcess process

def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult :=
  runScript problem.toSMTLib config

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
  timeoutMs : Nat := 30000
  /-- Shared absolute monotonic deadline, including time spent between solver calls. -/
  deadlineMs : Option Nat := none
  /-- Retry timeout/unknown with equivalent Horn syntax when the caller has time. -/
  retrySearch : Bool := true
  spacerInlining : Bool := false
  /-- Eldarica interval analysis can be disabled when retrying an unimportable model. -/
  eldaricaIntervals : Bool := true
  /-- Alternate preprocessing for models rejected by the strict importer. -/
  eldaricaLargeBlockEncoding : Bool := false
  deriving Inhabited, Repr

/-- The same invocation is used for original and Flex-exported benchmark queries. -/
def Config.toProcessConfig (config : Config) : Process.Config :=
  match config.backend with
  | .spacer => Spacer.Config.toProcessConfig {
      executable := config.executable.getD ({} : Spacer.Config).executable
      timeoutMs := config.timeoutMs
      inlining := config.spacerInlining }
  | .eldarica => Eldarica.Config.toProcessConfig {
      executable := config.executable.getD ({} : Eldarica.Config).executable
      timeoutMs := config.timeoutMs
      intervals := config.eldaricaIntervals
      largeBlockEncoding := config.eldaricaLargeBlockEncoding }

/-- Alternate model-producing settings for the same problem; the caller bounds retries. -/
def Config.modelFallback? (config : Config) : Option Config :=
  match config.backend with
  | .spacer => if config.spacerInlining then some { config with spacerInlining := false } else none
  | .eldarica =>
    if config.eldaricaIntervals && !config.eldaricaLargeBlockEncoding then
      some { config with eldaricaLargeBlockEncoding := true }
    else if config.eldaricaIntervals then
      some { config with eldaricaIntervals := false, eldaricaLargeBlockEncoding := false }
    else none

/-- Return the actual call configuration and result, or `none` if its deadline expired. -/
def runScript? (input : String) (config : Config) : IO (Option (Config × SolverResult)) := do
  let config ← match config.deadlineMs with
    | none => pure config
    | some deadline =>
      let now ← IO.monoMsNow
      if now >= deadline then return none
      pure { config with timeoutMs := min config.timeoutMs (deadline - now) }
  let result ← Process.run config.toProcessConfig input
  return some (config, SolverResult.ofProcess result)

/-- Run a script without assigning Lean witnesses or trusting the solver's answer. -/
def runScript (input : String) (config : Config := {}) : IO SolverResult := do
  match ← runScript? input config with
  | some (_, result) => return result
  | none => return SolverResult.ofProcess { completion := .timedOut }

/-- Run the selected solver, retaining its transcript for import and certification. -/
def run (problem : ExportedProblem) (config : Config := {}) : IO SolverResult :=
  runScript problem.toSMTLib config

end Flex.CHC
