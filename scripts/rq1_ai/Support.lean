import Flex.Tactic

open Lean Meta Elab Tactic Command

namespace RQ1Experiment

private def record (event : Json) : IO Unit := do
  if let some path ← IO.getEnv "FLEX_AI_EVENTS" then
    IO.FS.withFile path .append fun file => file.putStrLn event.compress

/-- The two synthesis conditions differ only in whether PA is enabled. -/
elab "rq1_prefix " arm:str : tactic => do
  let arm := arm.getString
  let start ← IO.monoMsNow
  let heartbeats ← IO.getNumHeartbeats
  record <| Json.mkObj [("event", toJson "prefix_start"), ("arm", toJson arm)]
  match arm with
  | "original" => pure ()
  | "zap" => Flex.Portfolio.flexImpl { backends := [] }
  | "zap_fix" => Flex.Portfolio.flexImpl { backends := [.fix] }
  | _ => throwError "unknown experiment condition: {arm}"
  record <| Json.mkObj [
    ("event", toJson "prefix_end"), ("arm", toJson arm),
    ("milliseconds", toJson ((← IO.monoMsNow) - start)),
    ("heartbeats", toJson (((← IO.getNumHeartbeats) - heartbeats) / 1000)),
    ("goals", toJson (← getUnsolvedGoals).length)]

/-- Admissions cannot turn an unfinished task into a successful trial. -/
elab "rq1_verify " theoremName:ident : command => liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo theoremName
  for axiomName in ← collectAxioms name do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unfinished or untrusted proof: {axiomName}"
  logInfo "RQ1_PROOF_COMPLETE"

end RQ1Experiment
