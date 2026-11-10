
set_option maxHeartbeats 4000000
namespace ProbeImpl
open Lean Meta Elab Tactic Flex.CHC

def outcome (goal : MVarId) : TermElabM String := do
  let result ← solveGoal goal { backend := .spacer, executable := some "z3", timeoutMs := 30000 }
    (headsOnly := true)
  match result with
  | .solved _ => return "solved"
  | .partial r =>
    let mut left := 0
    for g in r.certificate.goals do
      let rest ← try Tactic.run g (Tactic.evalTactic (← `(tactic| grind))) catch _ => pure [g]
      left := left + rest.length
    return s!"partial({r.certificate.goals.size}) grind-left={left}"
  | .failed f =>
    return s!"failed[{repr f.stage}]: {(((f.message.splitOn "\n").headD "").take 200).toString}"

elab "probe" : tactic => withMainContext do
  let goal ← getMainGoal
  logInfo m!"PROBE outcome=<{← outcome goal}>"
  for g in ← getGoals do
    unless ← g.isAssigned do g.admit

end ProbeImpl
