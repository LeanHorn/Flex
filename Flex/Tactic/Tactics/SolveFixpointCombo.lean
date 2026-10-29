import Flex.Tactic.Tactics.SolveFixpoint
import Flex.Tactic.Tactics.RewriteKs
import Flex.Tactic.Tactics.Zap

open Lean Elab Meta Tactic

/-!
  ## `solve_fixpoint_combo` tactic

  Tries `solve_fixpoint` first. If it leaves any goals, resets to the original
  goal and runs `rewriteKs ; zap ; simp [*] ; solve_fixpoint` (each wrapped
  in `try` so partial progress is still kept).
-/
syntax "solve_fixpoint_combo" : tactic
elab_rules : tactic
  | `(tactic| solve_fixpoint_combo) => do
    let saved ← saveState
    solveFixpointImpl
    let remaining ← getGoals
    if remaining.isEmpty then
      pure ()
    else
      restoreState saved
      evalTactic (← `(tactic| (try rewriteKs) ; (try zap) ; (try simp [*]) ; (try solve_fixpoint)))
