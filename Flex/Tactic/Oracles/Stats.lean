import Lean

/-! Process-wide wall-time counters for external oracle stages. `fix` resets
    them on entry and prints them when `flex.benchOracles` is set. -/

namespace Flex.OracleStats

initialize statsRef : IO.Ref (Std.HashMap String (Nat × Nat)) ← IO.mkRef {}

/-- Stage totals of the oracle call in progress, for per-call reports. -/
initialize callRef : IO.Ref (Std.HashMap String Nat) ← IO.mkRef {}

def reset : IO Unit := statsRef.set {}

def record (key : String) (ns : Nat) : IO Unit := do
  statsRef.modify fun m =>
    let (total, count) := m.getD key (0, 0)
    m.insert key (total + ns, count + 1)
  callRef.modify fun m => m.insert key (m.getD key 0 + ns)

def beginCall : IO Unit := callRef.set {}

/-- Print one `ORACLE_CALL` line with the stages recorded since `beginCall`. -/
def endCall (oracle outcome : String) (totalNs : Nat) : IO Unit := do
  let stages := (← callRef.get).toArray.qsort (·.1 < ·.1)
  let fields := stages.foldl (fun acc (k, ns) => acc ++ s!" {k}={ns}") ""
  IO.println s!"ORACLE_CALL oracle={oracle} outcome={outcome} total={totalNs}{fields}"

/-- Run `act` as one reported oracle call when `enabled`. `outcome` names a
    result; a thrown exception is reported as `refuted` and rethrown. -/
def reportCall {m : Type → Type} {α : Type} [Monad m] [MonadLiftT IO m] [MonadExcept ε m]
    (enabled : Bool) (oracle : String) (outcome : α → String) (act : m α) : m α := do
  unless enabled do return ← act
  (beginCall : IO Unit)
  let start ← (IO.monoNanosNow : IO Nat)
  let finish (o : String) : m Unit := do
    let stop ← (IO.monoNanosNow : IO Nat)
    (endCall oracle o (stop - start) : IO Unit)
  try
    let r ← act
    finish (outcome r)
    return r
  catch e =>
    finish "refuted"
    throw e

/-- Time `act` under `key`, including runs that throw. -/
def time {m : Type → Type} {α : Type} [Monad m] [MonadLiftT IO m] [MonadFinally m]
    (key : String) (act : m α) : m α := do
  let start ← (IO.monoNanosNow : IO Nat)
  tryFinally act do
    let stop ← (IO.monoNanosNow : IO Nat)
    (record key (stop - start) : IO Unit)

/-- `(key, total ns, count)`, sorted by key. -/
def snapshot : IO (Array (String × Nat × Nat)) := do
  let entries := (← statsRef.get).toArray.map fun (k, (t, c)) => (k, t, c)
  return entries.qsort (·.1 < ·.1)

end Flex.OracleStats
