import Flex.CHC

open Lean Elab Tactic

register_option flex.spacer.executable : String := {
  defValue := "z3"
  descr := "Z3 executable used by the spacer tactic."
}

namespace Flex.CHC

/-- Instantiate invariants and prove heads, leaving one structured residual VC. -/
def solverTactic (config : Config) (facts : Facts.Config := {}) : TacticM Unit := withMainContext do
  let name := match config.backend with
    | .spacer => "spacer"
    | .eldarica => "eldarica"
  let report ← match ← solveGoal (← getMainGoal) config (headsOnly := true) (facts := facts) with
    | .solved report | .partial report => pure report
    | .failed failure =>
      if let some solver := failure.solver then
        if let .spawnError _ := solver.process.completion then
          throwError "{name}: {failure.message}\nInstall the solver on PATH or set flex.{name}.executable to its full path."
      throwError "{name}: {failure.message}"
  withOptions (·.setBool `pp.funBinderTypes true) do
    let entries := (report.problem.relations.zip report.witnesses).toList.map fun (relation, witness) =>
      let source := if witness.defaulted then " (unused; completed by Flex)" else ""
      m!"  {relation.kvar.name} := {witness.value}{source}"
    logInfo (MessageData.joinSep (m!"{name}: instantiated invariants" :: entries) "\n")
  replaceMainGoal report.certificate.goals.toList

end Flex.CHC

/-- Synthesize and certify invariants; optional lemmas and equations supply proved facts. -/
syntax "spacer" (atomic("(" &"lemmas" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"defs" ":=") "[" ident,* "]" ")")? : tactic

elab_rules : tactic
  | `(tactic| spacer $[(lemmas := [$lemmas:ident,*])]? $[(defs := [$defs:ident,*])]?) => do
    let resolve (names : Array (TSyntax `ident)) : TacticM (Array Name) :=
      names.mapM fun name => do return ← realizeGlobalConstNoOverloadWithInfo name
    let lemmas ← resolve (lemmas.map (·.getElems) |>.getD #[])
    let defs ← resolve (defs.map (·.getElems) |>.getD #[])
    Flex.CHC.solverTactic {
      backend := .spacer
      executable := some (flex.spacer.executable.get (← getOptions)) } { lemmas, defs }
