import Flex.CHC

open Lean Elab Tactic

register_option flex.spacer.executable : String := {
  defValue := "z3"
  descr := "Z3 executable used by the spacer tactic."
}

namespace Flex.CHC

/-- Instantiate invariants and prove heads, leaving one structured residual VC. -/
def solverTactic (config : Config) : TacticM Unit := withMainContext do
  let name := match config.backend with
    | .spacer => "spacer"
    | .eldarica => "eldarica"
  let oracle : ProofOracle := proveLeafWith (← `(tactic| grind))
  let report ← match ← solveGoal (← getMainGoal) config oracle (headsOnly := true) with
    | .solved report | .partial report => pure report
    | .failed failure =>
      if let some solver := failure.solver then
        if let .spawnError _ := solver.process.completion then
          throwError "{name}: {failure.message}\nInstall the solver on PATH or set flex.{name}.executable to its full path."
      throwError "{name}: {failure.message}"
  withOptions (·.setBool `pp.funBinderTypes true) do
    let entries := (report.problem.relations.zip report.witnesses).toList.map fun (relation, witness) =>
      m!"  {relation.kvar.name} := {witness.value}"
    logInfo (MessageData.joinSep (m!"{name}: instantiated invariants" :: entries) "\n")
  replaceMainGoal report.certificate.goals.toList

end Flex.CHC

/-- Synthesize with Spacer, report invariants, and certify heads with grind. -/
elab "spacer" : tactic => do
  Flex.CHC.solverTactic {
    backend := .spacer
    executable := some (flex.spacer.executable.get (← getOptions)) }
