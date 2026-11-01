import Flex.CHC
import Flex.Tactic.Automation
import Std.Time.DateTime.Timestamp

/-! CHC parity benchmark. The Python runner appends generated statements, never their proofs. -/

open Lean Meta Elab Term Flex.CHC

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option Elab.async false

namespace FlexParity

private structure Settings where
  input : System.FilePath
  output : System.FilePath
  events : System.FilePath
  mode : String
  backendName : String
  solver : Flex.CHC.Config
  eldaricaExecutable : Option String
  heartbeats : Nat
  proofHeartbeats : Nat
  smtTimeout : Nat
  proofBudgetMs : Nat

private def envNat (name : String) (fallback : Nat) (allowZero : Bool := false) : IO Nat := do
  match ← IO.getEnv name with
  | none => return fallback
  | some value =>
    let some n := value.toNat? | throw <| IO.userError s!"invalid {name}: {value}"
    if n == 0 && !allowZero then throw <| IO.userError s!"{name} must be positive"
    return n

private def settings : IO Settings := do
  let some input ← IO.getEnv "FLEX_PARITY_INPUT"
    | throw <| IO.userError "missing FLEX_PARITY_INPUT"
  let some output ← IO.getEnv "FLEX_PARITY_OUTPUT"
    | throw <| IO.userError "missing FLEX_PARITY_OUTPUT"
  let mode := (← IO.getEnv "FLEX_PARITY_MODE").getD "parity"
  unless mode == "parity" || mode == "portfolio" do
    throw <| IO.userError s!"unknown evaluation mode: {mode}"
  let backendName := (← IO.getEnv "FLEX_PARITY_BACKEND").getD "spacer"
  let backend ← match backendName with
    | "spacer" | "portfolio" => pure Backend.spacer
    | "eldarica" => pure Backend.eldarica
    | name => throw <| IO.userError s!"unknown backend: {name}"
  let executable ← IO.getEnv "FLEX_PARITY_EXECUTABLE"
  let timeoutMs ← envNat "FLEX_PARITY_SOLVER_MS" ({} : Flex.CHC.Config).timeoutMs
  return {
    input, output, events := output, mode, backendName
    solver := { backend, executable, timeoutMs }
    eldaricaExecutable := ← IO.getEnv "FLEX_PARITY_ELDARICA_EXECUTABLE"
    heartbeats := ← envNat "FLEX_PARITY_HEARTBEATS" 2000000
    proofHeartbeats := ← envNat "FLEX_PARITY_PROOF_HEARTBEATS" 20000
    smtTimeout := ← envNat "FLEX_PARITY_SMT_TIMEOUT" 30
    proofBudgetMs := ← envNat "FLEX_PARITY_PROOF_MS"
      (if mode == "portfolio" then 15000 else 0) true }

private def emit (cfg : Settings) (stage status : String)
    (fields : List (String × Json) := []) : IO Unit :=
  IO.FS.withFile (cfg.events / "events.jsonl") .append fun handle =>
    handle.putStrLn (Json.mkObj ([
      ("stage", toJson stage), ("status", toJson status),
      ("backend", toJson cfg.backendName)] ++ fields)).compress

private def budget (heartbeats : Nat) (action : TermElabM α) : TermElabM α :=
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := heartbeats * 1000 }) <|
    Core.withCurrHeartbeats action

private def errorText (error : Exception) : TermElabM String := do
  (← addMessageContext error.toMessageData).toString

private def phase (cfg : Settings) (stage : String) (action : TermElabM α)
    (describe : α → List (String × Json) := fun _ => []) : TermElabM α := do
  emit cfg stage "running"
  let start ← IO.monoMsNow
  tryCatchRuntimeEx (do
    let value ← budget cfg.heartbeats action
    emit cfg stage "ok" (("elapsed_ms", toJson ((← IO.monoMsNow) - start)) :: describe value)
    return value)
    (fun error => do
      emit cfg stage "error" [
        ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
        ("error", toJson (← errorText error))]
      throw error)

/-- Keep original assertions and definitions; remove response requests and process controls. -/
def nativeInput (input : String) : Except String (String × Array String × Bool) := do
  let mut reader : Smt2Lean.Source.Reader input := {}
  let mut commands := #[]
  let mut removed := #[]
  let mut checks := 0
  let mut hasLogic := false
  let mut exited := false
  let responses := #["get-model", "get-proof", "get-unsat-core", "get-unsat-assumptions",
    "get-value", "get-assignment", "get-info", "get-option", "echo", "exit"]
  repeat
    let (command, next) ← reader.next "native" |>.mapError fun e => e.message
    reader := next
    let some command := command | break
    let kind := command.tokens[1]?.getD ""
    if exited then throw "native parity: command after exit"
    if checks > 0 && !responses.contains kind then
      throw "native parity: only response requests may follow the single check"
    if kind == "exit" then exited := true
    if #["query", "rule", "declare-rel"].contains kind then
      throw "fixedpoint command protocol requires a separate parity adapter"
    if kind == "check-sat" || kind == "check-sat-assuming" then checks := checks + 1
    if kind == "set-logic" then
      unless command.tokens[2]? == some "HORN" do
        throw "native parity requires HORN logic"
      hasLogic := true
    if responses.contains kind then
      removed := removed.push command.text
    else if kind == "set-option" then
      -- Runtime and output settings must not override the shared benchmark configuration.
      let option := command.tokens[2]?.getD ""
      if #[":timeout", ":rlimit", ":print-success", ":produce-models",
          ":produce-proofs", ":produce-unsat-cores"].contains option then
        removed := removed.push command.text
      else
        throw s!"native parity: unsupported source solver option {option}"
    else
      commands := commands.push command.text
  unless checks == 1 do throw s!"native parity requires exactly one check, found {checks}"
  let scriptPrefix := if hasLogic then "" else "(set-logic HORN)\n"
  return (scriptPrefix ++ String.intercalate "\n" commands.toList ++ "\n", removed, !hasLogic)

private def outcomeName : SolverOutcome → String
  | .sat _ => "sat"
  | .unsat => "unsat"
  | .unknown _ => "unknown"
  | .timedOut => "timeout"
  | .error _ => "error"

private def verdict (result : SolverResult) : String :=
  match result.process.completion with
  | .exited 0 =>
    match Smt2Lean.SolverResponse.parse result.process.stdout "parity" with
    | .ok response =>
      if response.diagnostics.any (·.kind == .error) then "error"
      else match response.status with
        | some .sat => "sat"
        | some .unsat => "unsat"
        | some .unknown => "unknown"
        | none => "error"
    | .error _ => "error"
  | _ => outcomeName result.outcome

private def solve (cfg : Settings) (stage stem input : String) : IO SolverResult := do
  emit cfg stage "running"
  IO.FS.writeFile (cfg.output / s!"{stem}.smt2") input
  let start ← IO.monoMsNow
  let result ← runScript input cfg.solver
  IO.FS.writeFile (cfg.output / s!"{stem}.stdout") result.process.stdout
  IO.FS.writeFile (cfg.output / s!"{stem}.stderr") result.process.stderr
  emit cfg stage (outcomeName result.outcome) [
    ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
    ("process_ms", toJson result.process.elapsedMs),
    ("solver_status", toJson (verdict result)),
    ("model_available", toJson (match result.outcome with | .sat _ => true | _ => false)),
    ("completion", toJson (reprStr result.process.completion)),
    ("error", toJson (match result.outcome with | .error e => e | _ => ""))]
  return result

/-- A partial result must prove the original target from exactly its reported residuals. -/
private def checkBridge (original target : Expr) (goals : Array MVarId) : TermElabM Unit := do
  let saved ← saveState
  try
    let closed ← goals.mapM fun goal => goal.revertAll
    let types ← closed.mapM fun goal => do instantiateMVars (← goal.getType)
    for ty in types do
      if ty.hasMVar || ty.hasFVar || ty.hasLooseBVars then
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
  finally saved.restore

private structure AttemptResult where
  backend : String := ""
  status : String := "not_run"
  imported : Bool := false
  headsEliminated : Bool := false
  proved : Bool := false

private def AttemptResult.rank (r : AttemptResult) : Nat :=
  if r.proved then 3 else if r.headsEliminated then 2 else if r.imported then 1 else 0

/-- Each backend starts from the same prepared goal; only checked milestones survive. -/
private def runAttempt (cfg : Settings) (target original : Expr)
    (prepared : PreparedGoal) (problem : ExportedProblem) : TermElabM AttemptResult := do
  let saved ← saveState
  let stage ← IO.mkRef "solver"
  let progress ← IO.mkRef ({ backend := cfg.backendName } : AttemptResult)
  try
    tryCatchRuntimeEx (do
      let process := cfg.solver.toProcessConfig
      IO.FS.writeFile (cfg.output / "invocation.json") (Json.mkObj [
        ("executable", toJson process.executable), ("args", toJson process.args),
        ("timeout_ms", toJson process.timeoutMs)]).pretty
      let result ← solve cfg "solver" "exported" problem.toSMTLib
      let .sat _ := result.outcome
        | let status := "solver_" ++ outcomeName result.outcome
          emit cfg "result" status
          return { backend := cfg.backendName, status }
      stage.set "import"
      let witnesses ← phase cfg (← stage.get) (importWitnesses problem result)
        (fun ws => [("witnesses", toJson ws.size),
          ("defaulted_witnesses", toJson (ws.filter (·.defaulted)).size)])
      progress.modify fun r => { r with imported := true }
      let candidates ← witnesses.mapM fun witness => do
        let value ← withOptions (·.setBool `pp.funBinderTypes true) <|
          Meta.ppExpr witness.value
        return Json.mkObj [
          ("symbol", toJson witness.symbol), ("predicate", toJson value.pretty),
          ("defaulted", toJson witness.defaulted)]
      IO.FS.writeFile (cfg.output / "witnesses.json") (toJson candidates).pretty
      stage.set "certificate"
      let prove := proofOracle {
        heartbeats := cfg.proofHeartbeats, smtTimeout := cfg.smtTimeout }
      let start ← IO.monoMsNow
      -- Stop starting proof attempts after this model's shared search budget.
      let oracle : ProofOracle := fun target => do
        if cfg.proofBudgetMs != 0 && (← IO.monoMsNow) - start >= cfg.proofBudgetMs then
          return none
        prove target
      let certificate ← phase cfg (← stage.get)
        (certifyWitnesses problem witnesses prepared.bodyGoal oracle (headsOnly := true))
        (fun c => [("goals", toJson c.goals.size),
          ("proved_heads", toJson c.provedHeads),
          ("remaining_heads", toJson c.remainingHeads)])
      stage.set "heads_kernel"
      phase cfg (← stage.get) (checkBridge original target certificate.goals)
      let allHeads := certificate.remainingHeads == some 0
      progress.modify fun r => { r with headsEliminated := allHeads }
      emit cfg "heads" (match certificate.remainingHeads with
        | some 0 => "eliminated"
        | some _ => "remaining"
        | none => "unknown")
      let headsResidual ← certificate.goals.toList.mapM fun goal => do
        return (← Meta.ppGoal goal).pretty
      IO.FS.writeFile (cfg.output / "heads-residual.txt")
        (String.intercalate "\n\n---\n\n" headsResidual)
      stage.set "discharge"
      let remaining ← phase cfg (← stage.get) (do
        let mut remaining := #[]
        for goal in certificate.goals do
          unless ← goal.isAssignedOrDelayedAssigned do
            let goals ← goal.withContext <|
              Tactic.run goal (Flex.Automation.discharge (checkedOracle oracle))
            remaining := remaining ++ goals.toArray
        remaining.filterM fun goal => return !(← goal.isAssignedOrDelayedAssigned))
        (fun goals => [("goals", toJson goals.size)])
      stage.set "kernel"
      phase cfg (← stage.get) (checkBridge original target remaining)
      let goals ← remaining.toList.mapM fun goal => do
        return (← Meta.ppGoal goal).pretty
      IO.FS.writeFile (cfg.output / "residual.txt") (String.intercalate "\n\n---\n\n" goals)
      let proved := remaining.isEmpty
      let status := if proved then "proved" else "partial"
      emit cfg "result" status [("goals", toJson remaining.size)]
      return { (← progress.get) with
        status, proved, headsEliminated := allHeads || proved })
      (fun error => do
        let status := (← stage.get) ++ "_failed"
        emit cfg "result" status [("error", toJson (← errorText error))]
        return { (← progress.get) with status })
  finally saved.restore

private def runFlex (cfg : Settings) (name : Name) : TermElabM Unit := do
  let saved ← saveState
  let stage ← IO.mkRef "prepare"
  try
    tryCatchRuntimeEx (do
      let target := Lean.mkConst name
      let original ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
      let prepared ← phase cfg "prepare" <| prepareGoal original.mvarId!
      stage.set "export"
      let problem ← phase cfg "export"
        (exportConstraints prepared.kvars (← prepared.exportGoal.getType))
        (fun p => [("relations", toJson p.relations.size), ("clauses", toJson p.clauseCount)])
      if cfg.mode != "portfolio" then
        discard <| runAttempt cfg target original prepared problem
        return
      let mut best : AttemptResult := {}
      let mut imported := false
      let mut heads := false
      for backend in #[Backend.spacer, Backend.eldarica] do
        let backendName := if backend == .spacer then "spacer" else "eldarica"
        let output := cfg.output / backendName
        IO.FS.createDirAll output
        let solver : Flex.CHC.Config := {
          backend, timeoutMs := cfg.solver.timeoutMs
          executable := if backend == .spacer then cfg.solver.executable else cfg.eldaricaExecutable }
        let attempt := { cfg with output, backendName, solver }
        let result ← runAttempt attempt target original prepared problem
        imported := imported || result.imported
        heads := heads || result.headsEliminated
        if result.rank >= best.rank then best := result
        if result.proved then break
      emit cfg "result" best.status [
        ("selected_backend", toJson best.backend),
        ("invariants_obtained", toJson imported),
        ("heads_eliminated", toJson heads),
        ("fully_proved", toJson best.proved)])
      (fun error => do
        emit cfg "result" ((← stage.get) ++ "_failed")
          [("error", toJson (← errorText error))])
  finally saved.restore

/-- Portfolio mode exports once and skips the separately recorded native baseline. -/
def run (targetName : Option Name := none) : TermElabM Unit := do
  let cfg ← settings
  emit cfg "start" "ok" [
    ("unix_ms", toJson (← Std.Time.Timestamp.now).toMillisecondsSinceUnixEpoch.val)]
  let process := cfg.solver.toProcessConfig
  IO.FS.writeFile (cfg.output / "invocation.json") (Json.mkObj [
    ("executable", toJson process.executable), ("args", toJson process.args),
    ("timeout_ms", toJson process.timeoutMs), ("mode", toJson cfg.mode)]).pretty
  if cfg.mode == "parity" then
    try
      let source ← IO.FS.readFile cfg.input
      let (input, removed, addedLogic) ← ofExcept (nativeInput source)
      emit cfg "native_prepare" "ok" [
        ("removed_commands", toJson removed), ("added_horn_logic", toJson addedLogic)]
      discard <| solve cfg "native_solver" "native" input
    catch error =>
      emit cfg "native_prepare" "error" [("error", toJson (← errorText error))]
  match targetName with
  | some name => runFlex cfg name
  | none => emit cfg "result" "translation_failed"

end FlexParity
