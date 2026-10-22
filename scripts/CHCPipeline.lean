import Flex.Tactic
import Flex.CHC
import Flex.Tactic.Automation

/-! Paired CHC pilot: identical checked automation, with nesting and PA ablations. -/

open Lean Meta Elab Term Tactic Flex.CHC

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option Elab.async false

namespace FlexPilot

private structure Context where
  caseName : String
  variant : String
  output : System.FilePath
  solverMs : Nat
  paSeconds : Nat
  phaseHeartbeats : Nat
  stopAfterFix : Bool
  deadline : Nat
  events : IO.Ref (Array Json)
  closedBy : IO.Ref String

private def envNat (name : String) (fallback : Nat) : IO Nat := do
  return ((← IO.getEnv name).bind String.toNat?).getD fallback

private def publish (ctx : Context) (marker : String) (value : Json) : IO Unit := do
  let line := marker ++ value.compress
  IO.FS.withFile (ctx.output.parent.getD ctx.output / "progress.jsonl") .append fun handle =>
    handle.putStrLn line
  let stdout ← IO.getStdout
  stdout.putStrLn line
  stdout.flush

private def emit (ctx : Context) (phase status : String)
    (fields : List (String × Json) := []) : IO Unit := do
  let event := Json.mkObj ([
    ("case", toJson ctx.caseName), ("variant", toJson ctx.variant),
    ("phase", toJson phase), ("status", toJson status)] ++ fields)
  ctx.events.modify (·.push event)
  publish ctx "FLEX_PILOT_PHASE " event

private def restore (state : Tactic.SavedState) : TacticM Unit := do
  restoreTermState state.term
  set state.tactic

private def checkTime (ctx : Context) : TermElabM Unit := do
  if (← IO.monoMsNow) >= ctx.deadline then throwError "pilot wall-clock budget exhausted"

private def bounded (budget : Nat) (action : TacticM α) : TacticM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget * 1000 }) <|
    Core.withCurrHeartbeats action

/-- Failed phases restore their entry state; their timing and diagnostics survive. -/
private def attempt (ctx : Context) (phase : String) (action : TacticM Unit)
    : TacticM Bool := do
  let saved ← Tactic.saveState
  let start ← IO.monoMsNow
  let heartbeats ← IO.getNumHeartbeats
  emit ctx phase "running" [
    ("heartbeat_limit", toJson ctx.phaseHeartbeats),
    ("recursion_limit", toJson (← readThe Core.Context).maxRecDepth)]
  tryCatchRuntimeEx (do
    checkTime ctx
    bounded ctx.phaseHeartbeats action
    pruneSolvedGoals
    let solved := (← getGoals).isEmpty
    if solved then ctx.closedBy.set phase
    emit ctx phase (if solved then "proved" else "partial") [
      ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
      ("heartbeats", toJson (((← IO.getNumHeartbeats) - heartbeats) / 1000)),
      ("remaining_goals", toJson (← getGoals).length)]
    return true)
    (fun error => do
      let message ← error.toMessageData.toString
      restore saved
      emit ctx phase "failed" [
        ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
        ("heartbeats", toJson (((← IO.getNumHeartbeats) - heartbeats) / 1000)),
        ("error", toJson message)]
      return false)

private def hasPredicates (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← whnf (← instantiateMVars (← goal.getType))
  unless target.isAppOfArity ``Exists 2 do return false
  let type := target.appFn!.appArg!
  forallTelescopeReducing type fun _ result => return result.isProp

/-- Leave predicate existentials for synthesis, and discharge ordinary residuals. -/
private def discharge : TacticM Unit := do
  let goals ← getUnsolvedGoals
  let predicates ← goals.filterM fun goal => hasPredicates goal
  setGoals (goals.filter fun goal => !predicates.contains goal)
  Flex.Automation.discharge
  setGoals (predicates ++ (← getUnsolvedGoals))

private def onPredicates (action : TacticM Unit) : TacticM Unit := do
  let goals ← getUnsolvedGoals
  let mut remaining := []
  for goal in goals do
    if ← hasPredicates goal then
      setGoals [goal]
      action
      remaining := remaining ++ (← getUnsolvedGoals)
    else remaining := remaining ++ [goal]
  setGoals remaining

private def saveGoals (ctx : Context) (stem : String) : TacticM Unit := do
  let goals ← (← getUnsolvedGoals).mapM fun goal => return (← Meta.ppGoal goal).pretty
  IO.FS.writeFile (ctx.output / (stem ++ ".txt")) (String.intercalate "\n\n" goals)

private def runPA (ctx : Context) (close : Bool := true) : TacticM Unit := do
  let mode := match ctx.variant with
    | "scrape_no" => PAScrapeMode.no
    | "scrape_basic" | "ab_nest_post_fix_basic" | "ab_zap_fix_basic" => PAScrapeMode.basic
    | "scrape_standard" | "ab_nest_post_fix_standard" | "ab_zap_fix_standard" => PAScrapeMode.standard
    | _ => PAScrapeMode.deep
  let start ← IO.monoMsNow
  let calls ← IO.mkRef 0
  let accepted ← IO.mkRef 0
  let invalid ← IO.mkRef 0
  let unknown ← IO.mkRef 0
  let batches ← IO.mkRef 0
  let oracleMs ← IO.mkRef 0
  let rounds ← IO.mkRef 0
  let observe : PAObserver := fun event => do
    match event with
    | .setup scraped standard tagged candidates =>
      emit ctx "fix_setup" "prepared" [
        ("scraped_templates", toJson scraped), ("standard_templates", toJson standard),
        ("tagged_templates", toJson tagged),
        ("initial_candidates", toJson (candidates.foldl (fun n (_, count) => n + count) 0)),
        ("candidates", Json.arr (candidates.map fun (name, count) => Json.mkObj [
          ("name", toJson name.toString), ("count", toJson count)]))]
    | .roundStarted count =>
      rounds.modify (· + 1)
      emit ctx "fix_round" "running" [
        ("round", toJson (← rounds.get)), ("candidates_before", toJson count)]
    | .roundFinished before after =>
      emit ctx "fix_round" "completed" [
        ("round", toJson (← rounds.get)), ("candidates_before", toJson before),
        ("candidates_after", toJson after)]
    | .converged count =>
      emit ctx "fix_converged" "converged" [
        ("rounds", toJson (← rounds.get)), ("surviving_candidates", toJson count)]
  let checkBudget : TermElabM Unit := do
    checkTime ctx
    if (← IO.monoMsNow) - start >= ctx.paSeconds * 1000 then
      throwError "PA wall-clock budget exhausted"
  let oracle : PASynthOracle := fun targets => do
    checkBudget
    calls.modify (· + targets.size)
    batches.modify (· + 1)
    let queryStart ← IO.monoMsNow
    try
      let decisions ← Flex.Automation.synthOracle checkBudget targets
      for decision in decisions do
        match decision with
        | .valid => accepted.modify (· + 1)
        | .invalid => invalid.modify (· + 1)
        | .unknown _ => unknown.modify (· + 1)
      return decisions
    finally oracleMs.modify (· + ((← IO.monoMsNow) - queryStart))
  try
    let maxGuardedQualifiers ← envNat "FLEX_PILOT_GUARD_LIMIT" 32
    withOptions (flex.benchOracles.set · true) do
      onPredicates <| fixImpl proveLeaf { mode, maxGuardedQualifiers }
        (some Flex.Automation.proofOracle) observe (some oracle)
    emit ctx "fix_certificate" "built" [("remaining_goals", toJson (← getGoals).length)]
    if close then discharge
  finally
    let warnings ← (← Core.getMessageLog).toList.filterMapM fun message => do
      if message.severity == .warning then return some (← message.data.toString)
      return none
    emit ctx "fix_queries" "measured" [
      ("queries", toJson (← calls.get)), ("accepted", toJson (← accepted.get)),
      ("batches", toJson (← batches.get)), ("invalid", toJson (← invalid.get)),
      ("unknown", toJson (← unknown.get)),
      ("oracle_ms", toJson (← oracleMs.get)),
      ("elapsed_ms", toJson ((← IO.monoMsNow) - start)), ("warnings", toJson warnings)]

private def solver (ctx : Context) (backend : Backend) (close : Bool := true) : TacticM Unit := do
  let label := if backend == .spacer then "spacer" else "eldarica"
  let index ← IO.mkRef 0
  onPredicates do
    checkTime ctx
    let goal ← getMainGoal
    let result ← solveGoal goal { backend, timeoutMs := ctx.solverMs }
      Flex.Automation.proofOracle (headsOnly := true)
    let i ← index.get
    index.modify (· + 1)
    let saveTranscript (result : SolverResult) : IO Unit := do
      IO.FS.writeFile (ctx.output / s!"{label}-{i}.stdout") result.process.stdout
      IO.FS.writeFile (ctx.output / s!"{label}-{i}.stderr") result.process.stderr
    match result with
    | .failed failure =>
      if let some result := failure.solver then saveTranscript result
      emit ctx (label ++ "_candidate") "failed" [
        ("stage", toJson (reprStr failure.stage)), ("error", toJson failure.message)]
      throwError failure.message
    | .solved report | .partial report =>
      saveTranscript report.solver
      IO.FS.writeFile (ctx.output / s!"{label}-{i}.smt2") report.problem.toSMTLib
      let witnesses ← report.witnesses.toList.mapM fun witness => do
        return s!"{witness.symbol} := {(← ppExpr witness.value).pretty}"
      IO.FS.writeFile (ctx.output / s!"{label}-{i}-invariants.txt")
        (String.intercalate "\n" witnesses)
      emit ctx (label ++ "_candidate") "imported" [
        ("witnesses", toJson report.witnesses.size),
        ("proved_heads", toJson report.certificate.provedHeads),
        ("process_ms", toJson report.solver.process.elapsedMs),
        ("timings", Json.arr (report.timings.map fun timing => Json.mkObj [
          ("stage", toJson (reprStr timing.stage)),
          ("elapsed_ms", toJson (timing.elapsedNs / 1000000))]))]
      setGoals report.certificate.goals.toList
  if close then discharge

private def ablation (ctx : Context) : TacticM Unit := do
  if ctx.variant.startsWith "ab_nest_" then
    discard <| attempt ctx "nest" (evalTactic (← `(tactic| nest_chc)))
  if ctx.variant != "ab_solver" && !(← getUnsolvedGoals).isEmpty then
    discard <| attempt ctx "zap" <| onPredicates (evalTactic (← `(tactic| zap)))
  saveGoals ctx "after-zap"
  if (← getUnsolvedGoals).isEmpty then return
  if ctx.variant.startsWith "ab_nest_post_" || ctx.variant == "ab_zap_post_solver" then
    discard <| attempt ctx "postprocess" do
      let goals ← getUnsolvedGoals
      setGoals (← goals.mapM fun goal => compactGoal goal [])
    saveGoals ctx "after-postprocess"
  if (← getUnsolvedGoals).isEmpty then return
  if ctx.variant.endsWith "basic" || ctx.variant.endsWith "standard" || ctx.variant.endsWith "deep" then
    unless (← getUnsolvedGoals).isEmpty do
      discard <| attempt ctx "fix" (runPA ctx false)
    saveGoals ctx "after-fix"
    unless (← getUnsolvedGoals).isEmpty do
      discard <| attempt ctx "discharge" discharge
    return
  let entry ← Tactic.saveState
  let mut best := entry
  for backend in #[Backend.spacer, Backend.eldarica] do
    if (← getUnsolvedGoals).isEmpty then return
    restore entry
    let label := if backend == .spacer then "spacer" else "eldarica"
    if ← attempt ctx label (solver ctx backend false) then
      unless (← getUnsolvedGoals).isEmpty do
        discard <| attempt ctx (label ++ "_discharge") discharge
      best ← Tactic.saveState
      saveGoals ctx ("after-" ++ label)
      if (← getUnsolvedGoals).isEmpty then return
  restore best
  unless (← getUnsolvedGoals).isEmpty do
    discard <| attempt ctx "discharge" discharge

private def pipeline (ctx : Context) : TacticM Unit := do
  if ctx.variant.startsWith "ab_" then return ← ablation ctx
  let withNest := ctx.variant == "nest_fix" || ctx.variant == "nest_no_fix"
  let withFix := #["nest_fix", "flat_fix", "scrape_no", "scrape_basic",
    "scrape_standard", "scrape_deep"].contains ctx.variant
  if withNest then discard <| attempt ctx "nest" (evalTactic (← `(tactic| nest_chc)))
  if ctx.variant != "solver_only" then
    discard <| attempt ctx "zap" do
      onPredicates (evalTactic (← `(tactic| zap)))
      discharge
  if (← getUnsolvedGoals).isEmpty then return
  saveGoals ctx "after-zap"
  let cleaned ← Tactic.saveState
  let mut best := cleaned
  if withFix then
    if ← attempt ctx "fix" (runPA ctx) then
      if (← getUnsolvedGoals).isEmpty then return
      best ← Tactic.saveState
      saveGoals ctx "after-fix"
    restore cleaned
  if ctx.stopAfterFix then
    restore best
    return
  for backend in #[Backend.spacer, Backend.eldarica] do
    let label := if backend == .spacer then "spacer" else "eldarica"
    restore cleaned
    if ← attempt ctx label (solver ctx backend) then
      if (← getUnsolvedGoals).isEmpty then return
      best ← Tactic.saveState
      saveGoals ctx ("after-" ++ label)
  restore best

/-- Check a proof of the original target from precisely the remaining obligations. -/
private def checkBridge (original target : Expr) (goals : Array MVarId) : TermElabM Unit := do
  let saved ← Term.saveState
  try
    let closed ← goals.mapM fun goal => goal.revertAll
    let types ← closed.mapM fun goal => do instantiateMVars (← goal.getType)
    for type in types do
      if type.hasMVar || type.hasFVar || type.hasLooseBVars then
        throwError "residual contains unresolved variables"
    let names := Array.ofFn (n := types.size) fun ⟨i, _⟩ => Name.mkSimple s!"residual{i}"
    withLocalDeclsDND (names.zip types) fun hypotheses => do
      for goal in closed, hyp in hypotheses do goal.assign hyp
      let proof ← mkLambdaFVars hypotheses (← instantiateMVars original)
      if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
        throwError "certificate contains unresolved or admitted evidence"
      checkWithKernel proof
      unless ← isDefEq (← inferType proof) (← mkForallFVars hypotheses target) do
        throwError "certificate does not prove the original target"
      for name in proof.getUsedConstants do
        for axiomName in ← collectAxioms name do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "certificate depends on {axiomName}"
  finally restoreTermState saved

/-- Run one variant without leaking assignments, declarations, or messages to the next. -/
private def runImpl (name : Name) (variant caseName : String) : TermElabM Unit := do
  let saved ← Term.saveState
  let start ← IO.monoMsNow
  let initialHeartbeats ← IO.getNumHeartbeats
  let recursionLimit ← envNat "FLEX_PILOT_RECURSION_LIMIT" 16384
  let output : System.FilePath := (← IO.getEnv "FLEX_PILOT_OUTPUT").getD "/tmp/flex-pilot"
  let ctx : Context := {
    caseName, variant, output := output / variant
    solverMs := ← envNat "FLEX_PILOT_SOLVER_MS" 30000
    paSeconds := ← envNat "FLEX_PILOT_PA_SECONDS" 30
    phaseHeartbeats := ← envNat "FLEX_PILOT_PHASE_HEARTBEATS" 2000000
    stopAfterFix := (← IO.getEnv "FLEX_PILOT_STOP_AFTER_FIX") == some "1"
    deadline := start + (← envNat "FLEX_PILOT_CASE_SECONDS" 180) * 1000
    events := ← IO.mkRef #[], closedBy := ← IO.mkRef "" }
  IO.FS.createDirAll ctx.output
  publish ctx "FLEX_PILOT_START " (Json.mkObj [
    ("case", toJson caseName), ("variant", toJson variant)])
  let (status, error, remaining) ← try
    tryCatchRuntimeEx (do
      let target := Lean.mkConst name
      let original ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
      let goals ← withTheReader Core.Context (fun c => { c with maxRecDepth := recursionLimit }) <|
        Tactic.run original.mvarId! (pipeline ctx)
      let checkStart ← IO.monoMsNow
      let checkHeartbeats ← IO.getNumHeartbeats
      checkBridge original target goals.toArray
      emit ctx "kernel" "checked" [
        ("elapsed_ms", toJson ((← IO.monoMsNow) - checkStart)),
        ("heartbeats", toJson (((← IO.getNumHeartbeats) - checkHeartbeats) / 1000))]
      let residuals ← goals.mapM fun goal => return (← Meta.ppGoal goal).pretty
      IO.FS.writeFile (ctx.output / "residual.txt") (String.intercalate "\n\n" residuals)
      return (if goals.isEmpty then "proved" else "partial", "", goals.length))
      (fun exception => do
        ctx.closedBy.set ""
        return ("failed", ← exception.toMessageData.toString, 1))
  finally restoreTermState saved
  let result := Json.mkObj [
    ("case", toJson caseName), ("variant", toJson variant), ("status", toJson status),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
    ("heartbeats", toJson (((← IO.getNumHeartbeats) - initialHeartbeats) / 1000)),
    ("recursion_limit", toJson recursionLimit), ("peak_recursion_depth", Json.null),
    ("remaining_goals", toJson remaining), ("phases", Json.arr (← ctx.events.get)),
    ("closed_by", toJson (← ctx.closedBy.get)), ("error", toJson error)]
  IO.FS.writeFile (ctx.output / "result.json") result.pretty
  publish ctx "FLEX_PILOT " result

end FlexPilot

namespace FlexPilot

def run (name : Name) (variant caseName : String) : TermElabM Unit := do
  let limit ← envNat "FLEX_PILOT_RECURSION_LIMIT" 16384
  withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := limit }) <|
    runImpl name variant caseName

end FlexPilot
