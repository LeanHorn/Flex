import Flex.CHC.Process
import Smt2Lean.SolverResponse

namespace Flex.CHC

/-- Results use assertion/check-sat semantics: `sat` supplies candidate predicate
interpretations. These definitions are solver text, not Lean witnesses or proofs. -/
inductive SolverOutcome where
  | sat (model : Array Smt2Lean.Source.Command)
  | unsat
  | unknown (diagnostics : Array Smt2Lean.SolverResponse.Diagnostic)
  | timedOut
  | error (message : String)
  deriving Inhabited

/-- Keep the original transcript, exit information, and wall time for diagnostics
and later model reconstruction. No native parser handles or Lean state are retained. -/
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

/-- Decode only a successful process's complete response. In particular, a solver
that reports an error and later prints `sat` must not supply candidate witnesses.
An explicitly empty model is valid; a missing model after `sat` is an error. -/
def SolverResult.ofProcess (process : Process.Result) : SolverResult :=
  let outcome := match process.completion with
    | .exited 0 => parseOutcome process.stdout
    | .exited code => .error s!"CHC solver exited with code {code}"
    | .timedOut => .timedOut
    | .spawnError message => .error s!"Could not start CHC solver: {message}"
    | .ioError message => .error s!"CHC solver I/O failed: {message}"
  { outcome, process }

end Flex.CHC
