import Lean

open Lean Meta Elab Tactic

namespace Flex.Timeout

private def runCore (deadline : Nat) (action : CoreM α) : CoreM (Option α) := do
  Core.checkInterrupted
  if (← IO.monoMsNow) >= deadline then return none
  let token ← IO.CancelToken.new
  let used ← IO.mkRef 0
  let action ← Core.wrapAsync (fun () => do
    let start ← IO.getNumHeartbeats
    try
      let value ← action
      return (value, ← get)
    finally used.set ((← IO.getNumHeartbeats) - start)) (some token)
  let task ← (action ()).asTask (prio := .dedicated)
  let cancel := do token.set; IO.cancel task
  if let some parent := (← read).cancelTk? then parent.onSet cancel
  try
    while !(← IO.hasFinished task) do
      Core.checkInterrupted
      if (← IO.monoMsNow) >= deadline then return none
      IO.sleep 5
    Core.checkInterrupted
    match ← IO.wait task with
    | .ok (value, state) => set state; return some value
    | .error error => throw error
  finally
    -- Join before restoring a checkpoint: no cancelled worker may keep changing it.
    cancel
    discard <| IO.wait task
    IO.addHeartbeats (← used.get)

/-- Request cancellation at the deadline, then discard unfinished state.
Unresponsive calls can delay return; caller interrupts propagate. -/
def run (deadline : Option Nat) (action : TacticM α) : TacticM (Option α) := do
  let some deadline := deadline | return some (← action)
  -- Explicit `run`s allocate fresh state references; `controlAt` would share them.
  let term := (action (← readThe Tactic.Context)).run (← getThe Tactic.State)
  let metaAction := term.run (← readThe Term.Context) (← getThe Term.State)
  let core := metaAction.run (← readThe Meta.Context) (← getThe Meta.State)
  match ← runCore deadline core with
  | none => return none
  | some (((value, tacticState), termState), metaState) =>
    set metaState
    set termState
    set tacticState
    return some value

end Flex.Timeout
