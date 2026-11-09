import Lean

open Lean Meta Elab Tactic

register_option flex.automation.deadlineMs : Nat := {
  defValue := 0
  descr := "Internal: the absolute `IO.monoMsNow` deadline of the enclosing `Flex.Timeout.run`; \
    zero means none. Automation stops starting work after it and caps external calls by it."
}

namespace Flex.Timeout

/-- The enclosing deadline, if any. -/
def deadline? : CoreM (Option Nat) := do
  let deadline := flex.automation.deadlineMs.get (← getOptions)
  return if deadline == 0 then none else some deadline

/-- Throw once the enclosing deadline has passed. -/
def checkDeadline : CoreM Unit := do
  Core.checkInterrupted
  if let some deadline ← deadline? then
    if (← IO.monoMsNow) >= deadline then throwError "flex: time budget exhausted"

/-- `limitMs`, capped by the time left before the enclosing deadline; throws once it has
passed. -/
def capMs (limitMs : Nat) : CoreM Nat := do
  checkDeadline
  let some deadline ← deadline? | return limitMs
  return min limitMs (deadline - (← IO.monoMsNow))

/-- Run with a deadline no later than `deadline`; an enclosing earlier one is kept. -/
def withDeadline [MonadWithOptions m] (deadline : Option Nat) : m α → m α :=
  withOptions fun opts => match deadline with
    | none => opts
    | some deadline =>
      let previous := flex.automation.deadlineMs.get opts
      flex.automation.deadlineMs.set opts (if previous == 0 then deadline else min previous deadline)

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
Unresponsive calls can delay return; caller interrupts propagate. The action also sees the
deadline through `flex.automation.deadlineMs`, so automation inside it can stop early and
bound external processes, which cancellation cannot interrupt. -/
def run (deadline : Option Nat) (action : TacticM α) : TacticM (Option α) := do
  let some deadline := deadline | return some (← action)
  let action := withDeadline (some deadline) action
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
