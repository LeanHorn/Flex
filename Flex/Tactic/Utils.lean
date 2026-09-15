import Lean

open Lean Elab Tactic

/-- When `true`, the solver tactics emit a per-phase heartbeat delta line
    `[phase] <tac>:<phase>=<hb/1000>` to stdout (consumed by the RQ3 eval
    harness). Off by default so normal builds / regression stay quiet. -/
register_option flex.benchPhases : Bool := {
  defValue := false
  descr    := "Emit per-phase heartbeat deltas for the RQ3 evaluation."
}

/-- Measure the heartbeats AND wall-clock ms consumed by `act` and, iff
    `flex.benchPhases` is set, print `[phase] <tac>:<phase>=<hb/1000> ms=<ms>`.
    The `<tac>:<phase>=<hb>` prefix is kept byte-for-byte from the original
    heartbeats-only format (consumed by `scripts/run_rq3.py`'s `PHASE_RE`);
    the ` ms=<ms>` suffix is new and simply ignored by that older regex.
    Generic over the tactic/meta monad (needs options + IO lifting). -/
@[inline] def benchPhase {m : Type → Type} {α : Type}
    [Monad m] [MonadLiftT IO m] [MonadOptions m]
    (tac phase : String) (act : m α) : m α := do
  if flex.benchPhases.get (← getOptions) then
    let h0 ← (IO.getNumHeartbeats : IO Nat)
    let t0 ← (IO.monoMsNow : IO Nat)
    let r ← act
    let h1 ← (IO.getNumHeartbeats : IO Nat)
    let t1 ← (IO.monoMsNow : IO Nat)
    (IO.println s!"[phase] {tac}:{phase}={(h1 - h0) / 1000} ms={t1 - t0}" : IO Unit)
    pure r
  else
    act

/--
  Run `tactic` and report whether it succeeded
  or not. On failure, roll back the tactic state
  AND restore the Core message log so any errors
  the tactic logged before throwing don't leak —
  `saveState`/`saved.restore` only cover Term/Meta
  state, not the message log.
-/
def attemptTactic (tactic : TacticM Unit) : TacticM Bool := do
  let saved     ← saveState
  let savedMsgs ← Core.getMessageLog
  try
    tactic
    return true
  catch _ =>
    saved.restore
    Core.setMessageLog savedMsgs
    return false
