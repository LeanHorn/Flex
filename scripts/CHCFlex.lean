import Flex.Tactic.Tactics.Flex
import Std.Time.DateTime.Timestamp

/-! Evaluate the main flex pipeline with a shared internal budget. -/

open Lean Meta Elab Term

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option Elab.async false
set_option trace.flex true

namespace FlexParity

private def envNat (name : String) (fallback : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | none => return fallback
  | some value =>
    let some n := value.toNat? | throw <| IO.userError s!"invalid {name}: {value}"
    return n

private def emit (output : System.FilePath) (stage status : String)
    (fields : List (String × Json) := []) : IO Unit :=
  IO.FS.withFile (output / "events.jsonl") .append fun handle =>
    handle.putStrLn (Json.mkObj ([
      ("stage", toJson stage), ("status", toJson status),
      ("backend", toJson "flex")] ++ fields)).compress

private def emitPhase (output : System.FilePath) (event : Flex.Portfolio.PhaseEvent) : IO Unit :=
  IO.FS.withFile (output / "phases.jsonl") .append fun handle => do
    handle.putStrLn (Json.mkObj [
      ("phase", toJson event.phase), ("status", toJson event.status),
      ("elapsed_ms", toJson event.elapsedMs), ("mono_ms", toJson (← IO.monoMsNow))]).compress

private def recordPA (output : System.FilePath) : PAObserver := fun event => do
  let record (status : String) (fields : List (String × Json)) := do
    emit output "fix/pa" status (("mono_ms", toJson (← IO.monoMsNow)) :: fields)
  match event with
  | .stageStarted mode => record "stage_start" [("mode", toJson (toString mode))]
  | .stageFinished mode accepted => record "stage_end" [
      ("mode", toJson (toString mode)), ("accepted", toJson accepted)]
  | .setup scraped standard tagged candidates =>
    record "setup" [
      ("scraped_templates", toJson scraped), ("bank_templates", toJson standard),
      ("tagged_templates", toJson tagged),
      ("candidates", Json.arr (candidates.map fun (name, count) => Json.mkObj [
        ("name", toJson name.toString), ("count", toJson count)]))]
  | .roundStarted count => record "round_start" [("candidates", toJson count)]
  | .roundFinished before after => record "round_end" [
      ("before", toJson before), ("after", toJson after)]
  | .converged count => record "converged" [("candidates", toJson count)]

private def recordCHC (output : System.FilePath) (attempt : IO.Ref Nat)
    (backend : Flex.Portfolio.Backend) (event : Flex.CHC.Event) : TermElabM Unit := do
  if event matches .exported _ then attempt.modify (· + 1)
  let index ← attempt.get
  let directory := output / "attempts" / s!"{index}-{backend}"
  IO.FS.createDirAll directory
  let record (stage status : String) (fields : List (String × Json) := []) :=
    emit output s!"chc/{stage}" status
      ([("solver_backend", toJson (toString backend)), ("attempt", toJson index)] ++ fields)
  match event with
  | .exported problem =>
    IO.FS.writeFile (directory / "exported.smt2") problem.toSMTLib
    let relations ← problem.relations.mapM fun relation => do
      return Json.mkObj [("symbol", toJson relation.symbol),
        ("name", toJson relation.kvar.name.toString),
        ("type", toJson (← Meta.ppExpr relation.leanType).pretty)]
    IO.FS.writeFile (directory / "relations.json") (toJson relations).pretty
    record "export" "ok" [("predicates", toJson relations.size),
      ("canonical_clauses", toJson problem.canonicalClauses),
      ("clauses", toJson problem.clauseCount)]
  | .solverReturned config result =>
    IO.FS.writeFile (directory / "stdout.txt") result.process.stdout
    IO.FS.writeFile (directory / "stderr.txt") result.process.stderr
    let process := config.toProcessConfig
    IO.FS.writeFile (directory / "invocation.json") (Json.mkObj [
      ("executable", toJson process.executable), ("args", toJson process.args),
      ("timeout_ms", toJson process.timeoutMs)]).pretty
    let status := match result.outcome with
      | .sat _ => "sat" | .unsat => "unsat" | .unknown _ => "unknown"
      | .timedOut => "timeout" | .error _ => "error"
    record "solver" status [("elapsed_ms", toJson result.process.elapsedMs)]
  | .imported witnesses =>
    let values ← witnesses.mapM fun witness => do
      return Json.mkObj [("symbol", toJson witness.symbol),
        ("predicate", toJson (← Meta.ppExpr witness.value).pretty),
        ("defaulted", toJson witness.defaulted)]
    IO.FS.writeFile (directory / "witnesses.json") (toJson values).pretty
    record "import" "ok" [("predicates", toJson values.size)]
  | .importFailed message =>
    IO.FS.writeFile (directory / "import-error.txt") message
    record "import" "failed" [("error", toJson message)]
  | .certified certificate =>
    record "certificate" "ok" [("proved_heads", toJson certificate.provedHeads),
      ("remaining_heads", toJson certificate.remainingHeads),
      ("goals", toJson certificate.goals.size)]

private def measure (output : System.FilePath) (name : String)
    (action : Unit → TermElabM α) : TermElabM α := do
  let start ← IO.monoMsNow
  emitPhase output { phase := name, status := "start" }
  try action ()
  finally emitPhase output { phase := name, status := "end", elapsedMs := (← IO.monoMsNow) - start }

/-- Count predicate existentials in the positive constraint structure. -/
private partial def predicateCount (target : Expr) : MetaM Nat := do
  let target ← whnf (← instantiateMVars target)
  if target.isAppOfArity ``Exists 2 then
    let domain := target.getArg! 0
    let isPredicate ← forallTelescopeReducing domain fun _ result => pure result.isProp
    return ← withLocalDeclD `witness domain fun witness => do
      let rest ← predicateCount (target.appArg!.beta #[witness])
      return rest + if isPredicate then 1 else 0
  if let some (left, right) := target.and? then
    return (← predicateCount left) + (← predicateCount right)
  if target.isForall then
    return ← withLocalDecl target.bindingName! target.bindingInfo! target.bindingDomain!
      fun x => predicateCount (target.bindingBody!.instantiate1 x)
  return 0

/-- Check the original theorem as a function of exactly the reported residual goals. -/
private def checkBridge (output : System.FilePath) (original target : Expr)
    (goals : Array MVarId) : TermElabM Unit := do
  let saved ← saveState
  try
    let closed ← measure output "verify/reclose" fun _ => goals.mapM fun goal => goal.revertAll
    let types ← closed.mapM fun goal => do instantiateMVars (← goal.getType)
    for type in types do
      if type.hasMVar || type.hasFVar || type.hasLooseBVars then
        throwError "residual contains unresolved variables"
    let names := Array.ofFn (n := types.size) fun ⟨i, _⟩ => Name.mkSimple s!"residual{i}"
    withLocalDeclsDND (names.zip types) fun hypotheses => do
      for goal in closed, hyp in hypotheses do goal.assign hyp
      let proof ← measure output "verify/assemble" fun _ => do
        mkLambdaFVars hypotheses (← instantiateMVars original)
      if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
        throwError "certificate contains unresolved or admitted evidence"
      measure output "verify/kernel" fun _ => checkWithKernel proof
      measure output "verify/type" fun _ => do
        unless ← isDefEq (← inferType proof) (← mkForallFVars hypotheses target) do
          throwError "certificate does not prove the original target"
      measure output "verify/axioms" fun _ => do
        for name in proof.getUsedConstants do
          for axiomName in ← collectAxioms name do
            unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
              throwError "certificate depends on {axiomName}"
  finally Flex.CHC.restoreTermState saved

def run (targetName : Option Name := none) : TermElabM Unit := do
  let some output ← IO.getEnv "FLEX_PARITY_OUTPUT"
    | throwError "missing FLEX_PARITY_OUTPUT"
  let output : System.FilePath := output
  emit output "start" "ok" [
    ("unix_ms", toJson (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val)]
  let some name := targetName
    | emit output "result" "translation_failed"; return
  let saved ← saveState
  let stage ← IO.mkRef "prepare"
  let start ← IO.monoMsNow
  let initialHeartbeats ← IO.getNumHeartbeats
  try
    tryCatchRuntimeEx (do
      let heartbeats ← envNat "FLEX_PARITY_HEARTBEATS" 2000000
      let proofHeartbeats ← envNat "FLEX_PARITY_PROOF_HEARTBEATS" 20000
      let caseSeconds ← envNat "FLEX_PARITY_CASE_SECONDS" 120
      let totalSeconds ← envNat "FLEX_PARITY_FLEX_SECONDS" 60
      let solverSeconds ← envNat "FLEX_PARITY_SOLVER_SECONDS" 30
      let zap := (← IO.getEnv "FLEX_PARITY_ZAP").getD "1" != "0"
      let full := (← IO.getEnv "FLEX_PARITY_FULL").getD "0" == "1"
      let scrapeName := (← IO.getEnv "FLEX_PARITY_SCRAPE").getD "auto"
      let scrapeMode : PAScrapeMode ← match scrapeName with
        | "no" => pure .no | "basic" => pure .basic
        | "standard" => pure .standard | "deep" => pure .deep
        | "auto" => pure .auto
        | _ => throwError "invalid FLEX_PARITY_SCRAPE: {scrapeName}"
      let profilePA := (← IO.getEnv "FLEX_PARITY_PROFILE_PA").getD "0" == "1"
      let solvers := (← IO.getEnv "FLEX_PARITY_SE").getD "1" != "0"
      let backends : List Flex.Portfolio.Backend :=
        (if full then [.fix] else []) ++ (if solvers then [.spacer, .eldarica] else [])
      let recursionLimit ← envNat "FLEX_PARITY_RECURSION_LIMIT" 16384
      let spacerExe ← IO.getEnv "FLEX_PARITY_EXECUTABLE"
      let eldaricaExe ← IO.getEnv "FLEX_PARITY_ELDARICA_EXECUTABLE"
      let currentOptions ← getOptions
      let options := Id.run do
        let opts := flex.benchOracles.set currentOptions profilePA
        let opts := opts.setBool `trace.flex.synthesis profilePA
        let opts := flex.automation.proofHeartbeats.set opts proofHeartbeats
        let opts := match spacerExe with
          | some executable => flex.spacer.executable.set opts executable
          | none => opts
        let opts := match eldaricaExe with
          | some executable => flex.eldarica.executable.set opts executable
          | none => opts
        return opts
      withOptions (fun _ => options) <|
        withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := recursionLimit }) do
          let config : Flex.Portfolio.Config := {
            nesting := false, zap
            heartbeats, totalTimeout := totalSeconds, solverTimeout := solverSeconds }
          IO.FS.writeFile (output / "invocation.json") (Json.mkObj [
            ("entry_point", toJson "Flex.Portfolio.flexImpl"),
            ("backends", toJson (backends.map toString)),
            ("scrape", if full then toJson scrapeName else Json.null),
            ("profile_pa", toJson profilePA),
            ("preprocess", toJson config.preprocess), ("zap", toJson config.zap),
            ("postprocess", toJson config.postprocess), ("nesting", toJson config.nesting),
            ("split_free", toJson config.splitFree),
            ("keep_candidates", toJson config.keepCandidates),
            ("total_timeout_seconds", toJson config.totalTimeout),
            ("solver_timeout_seconds", toJson config.solverTimeout),
            ("oracle_timeout_policy", toJson "remaining shared budget"),
            ("case_timeout_seconds", toJson caseSeconds),
            ("phase_heartbeats", toJson heartbeats),
            ("proof_heartbeats", toJson proofHeartbeats),
            ("function_smt", toJson (flex.automation.functionSmt.get options)),
            ("recursion_limit", toJson recursionLimit)]).pretty
          let target := Lean.mkConst name
          let before ← predicateCount target
          let original ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
          stage.set "flex"
          emit output "flex" "running" [("original_predicates", toJson before)]
          let attempt ← IO.mkRef 0
          let goals ← Tactic.run original.mvarId! <| Flex.Portfolio.flexImpl {
            config, backends, scrape := { mode := scrapeMode }, onPhase := emitPhase output
            onPA := if profilePA then recordPA output else fun _ => pure ()
            onCHC := recordCHC output attempt }
          let flexMs := (← IO.monoMsNow) - start
          emit output "flex" "ok" [("elapsed_ms", toJson flexMs)]
          let after ← measure output "checkpoint/format" fun _ => do
            let mut after := 0
            let mut residuals := []
            for goal in goals do
              after := after + (← goal.withContext do predicateCount (← goal.getType))
              residuals := residuals ++ [(← Meta.ppGoal goal).pretty]
            IO.FS.writeFile (output / "residual.txt") (String.intercalate "\n\n---\n\n" residuals)
            return after
          emit output "checkpoint" "retained" [
            ("goals", toJson goals.length), ("original_predicates", toJson before),
            ("remaining_predicates", toJson after), ("kernel_checked", toJson false)]
          stage.set "kernel"
          emit output "kernel" "running"
          let kernelStart ← IO.monoMsNow
          checkBridge output original target goals.toArray
          emit output "kernel" "ok" [("elapsed_ms", toJson ((← IO.monoMsNow) - kernelStart))]
          emit output "result" (if goals.isEmpty then "proved" else "partial") [
            ("goals", toJson goals.length),
            ("original_predicates", toJson before), ("remaining_predicates", toJson after),
            ("predicate_count_reduction", toJson (before - after)),
            ("all_predicates_instantiated", toJson (after == 0)),
            ("fully_proved", toJson goals.isEmpty), ("kernel_checked", toJson true),
            ("flex_ms", toJson flexMs), ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
            ("heartbeats", toJson (((← IO.getNumHeartbeats) - initialHeartbeats) / 1000)),
            ("recursion_limit", toJson recursionLimit), ("peak_recursion_depth", Json.null)])
      (fun error => do
        emit output "result" ((← stage.get) ++ "_failed") [
          ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
          ("heartbeats", toJson (((← IO.getNumHeartbeats) - initialHeartbeats) / 1000)),
          ("error", toJson (← error.toMessageData.toString))])
  finally
    let traces ← getTraceState
    let messages ← Core.getMessageLog
    Flex.CHC.restoreTermState saved
    modifyTraceState fun _ => traces
    Core.setMessageLog messages

end FlexParity
