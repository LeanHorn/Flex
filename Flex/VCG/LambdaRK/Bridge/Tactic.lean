import Flex.VCG.LambdaRK.Bridge.Goal

namespace LambdaRK.Bridge

open Lean Elab Tactic

/-- Lower and certify a closed λRK VC. The default backend is Spacer.
Use `lambdark_chc eldarica` or `lambdark_chc eldarica "/path/to/eld"`
to select Eldarica. Partial success leaves instantiated source/certificate VCs.
Programmatic callers can configure timeouts and proof oracles through `solveGoal`.
-/
syntax (name := lambdaRKCHC) "lambdark_chc" (ident)? (str)? : tactic

elab_rules : tactic
  | `(tactic| lambdark_chc $[$backend:ident]? $[$executable:str]?) => do
      let backend ← match backend.map TSyntax.getId with
        | none | some `spacer => pure Flex.CHC.Backend.spacer
        | some `eldarica => pure Flex.CHC.Backend.eldarica
        | some name => throwError "unknown λRK CHC backend {name}; use spacer or eldarica"
      let config : Flex.CHC.Config := {
        backend := backend
        executable := executable.map TSyntax.getString }
      let result ← solveGoal (← getMainGoal) config
      match result with
      | .failed message => throwError message
      | .solved _ => replaceMainGoal []
      | .«partial» report =>
          for diagnostic in report.diagnostics do
            logInfo m!"λRK source clause {diagnostic.clauseIndex + 1}: {diagnostic.message}"
          replaceMainGoal (report.obligations.toList.map (·.goal))

end LambdaRK.Bridge
