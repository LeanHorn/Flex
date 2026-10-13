import Flex.VCG.SystemFRK.Bridge.Goal

namespace SystemFRK.Bridge

open Lean Elab Tactic

/-- Solve with Spacer (default) or `systemfrk_chc eldarica ["/path/to/eld"]`.
Partial success leaves instantiated VCs; `solveGoal` exposes timeout/oracle configuration. -/
syntax (name := systemFRKCHC) "systemfrk_chc" (ident)? (str)? : tactic

elab_rules : tactic
  | `(tactic| systemfrk_chc $[$backend:ident]? $[$executable:str]?) => do
      let backend ← match backend.map TSyntax.getId with
        | none | some `spacer => pure Flex.CHC.Backend.spacer
        | some `eldarica => pure Flex.CHC.Backend.eldarica
        | some name => throwError "unknown SystemFRK CHC backend {name}; use spacer or eldarica"
      let config : Flex.CHC.Config := {
        backend := backend
        executable := executable.map TSyntax.getString }
      let result ← solveGoal (← getMainGoal) config
      match result with
      | .failed message => throwError message
      | .solved _ => replaceMainGoal []
      | .«partial» report =>
          for diagnostic in report.diagnostics do
            logInfo m!"SystemFRK source clause {diagnostic.clauseIndex + 1}: {diagnostic.message}"
          replaceMainGoal (report.obligations.toList.map (·.goal))

end SystemFRK.Bridge
