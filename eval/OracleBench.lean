import Flex
import Flex.Tactic.Oracles.Smt

/-! Prelude injected by `scripts/benchmark_oracles.py`. Time declaration
elaboration after imports; inspect the result so failed/admitted proofs cannot
be mistaken for speedups. Run serially to include external solver wall time. -/
open Lean Elab Command

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option auto.smt.timeout 1
set_option auto.smt.solver.name "z3"
set_option flex.benchOracles true

elab "oracle_bench " name:str " in " cmd:command : command => do
  let errorsBefore := ((← get).messages.toList.filter (·.severity == .error)).length
  let start ← IO.monoNanosNow
  try elabCommand cmd catch e => logException e
  let stop ← IO.monoNanosNow
  let errorsAfter := ((← get).messages.toList.filter (·.severity == .error)).length
  let mut success := errorsAfter == errorsBefore
  let mut axioms : Array Name := #[]
  if let some ci := (← getEnv).find? (Name.mkSimple name.getString) then
    if let some value := ci.value? then
      success := success && !value.hasSorry && !value.hasExprMVar
      axioms ← liftCoreM (collectAxioms ci.name)
      success := success && !(axioms.contains ``sorryAx)
    else success := false
  else success := false
  let result := Json.mkObj [
    ("success", toJson success),
    ("elaboration_ns", toJson (stop - start)),
    ("axioms", toJson (axioms.map toString))]
  IO.println s!"ORACLE_RESULT {result.compress}"
