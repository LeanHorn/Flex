import Flex.Tactic.Tactics.Flex
import Std.Time.DateTime.Timestamp

/-! Evaluate the main flex pipeline with a shared internal budget. -/

open Lean Meta Elab Term

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option Elab.async false
set_option trace.flex false

namespace FlexParity

private def envNat (name : String) (fallback : Nat) : IO Nat := do
  match ← IO.getEnv name with
  | none => return fallback
  | some value =>
    let some n := value.toNat? | throw (IO.userError s!"invalid {name}: {value}")
    return n

private def emit (output : System.FilePath) (stage status : String)
    (fields : List (String × Json) := []) : IO Unit :=
  IO.FS.withFile (output / "events.jsonl") .append fun handle =>
    handle.putStrLn (Json.mkObj ([
      ("stage", toJson stage), ("status", toJson status),
      ("backend", toJson "flex")] ++ fields)).compress

private def emitPhase (output : System.FilePath) (event : Flex.Portfolio.PhaseEvent)
    (backendAttempt : Option Nat := none) : IO Unit :=
  IO.FS.withFile (output / "phases.jsonl") .append fun handle => do
    handle.putStrLn (Json.mkObj [
      ("phase", toJson event.phase), ("status", toJson event.status),
      ("budget_ms", toJson event.budgetMs), ("deadline_ms", toJson event.deadlineMs),
      ("backend_attempt", toJson backendAttempt),
      ("heartbeats_raw", toJson (← IO.getNumHeartbeats)),
      ("elapsed_ms", toJson event.elapsedMs), ("mono_ms", toJson (← IO.monoMsNow))]).compress

private structure PAStage where
  index : Nat := 0
  mode : Option String := none
  startedMs : Nat := 0
  startedHeartbeats : Nat := 0

private def recordPA (output : System.FilePath) (state : IO.Ref PAStage) : PAObserver := fun event => do
  let now ← IO.monoMsNow
  let heartbeats ← IO.getNumHeartbeats
  if let .stageStarted mode := event then
    state.modify fun previous => {
      index := previous.index + 1, mode := some (toString mode),
      startedMs := now, startedHeartbeats := heartbeats }
  let current ← state.get
  let record (status : String) (fields : List (String × Json)) := do
    emit output "fix/pa" status ([
      ("mono_ms", toJson now), ("heartbeats_raw", toJson heartbeats),
      ("pa_stage", toJson current.index), ("mode", toJson current.mode),
      ("stage_elapsed_ms", toJson (now - current.startedMs)),
      ("stage_heartbeats_raw", toJson (heartbeats - current.startedHeartbeats))] ++ fields)
  match event with
  | .stageStarted _ => record "stage_start" []
  | .stageFinished _ accepted => record "stage_end" [("accepted", toJson accepted)]
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

private def recordCHC (output : System.FilePath) (attempt backendAttempt : IO.Ref Nat)
    (backend : Flex.Portfolio.Backend) (event : Flex.CHC.Event) : TermElabM Unit := do
  if event matches .exported _ then attempt.modify (· + 1)
  let index ← attempt.get
  let directory := output / "attempts" / s!"{index}-{backend}"
  IO.FS.createDirAll directory
  let record (stage status : String) (fields : List (String × Json) := []) := do
    emit output s!"chc/{stage}" status
      ([("solver_backend", toJson (toString backend)), ("attempt", toJson index),
        ("backend_attempt", toJson (← backendAttempt.get)),
        ("mono_ms", toJson (← IO.monoMsNow))] ++ fields)
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
      ("timeout_ms", toJson process.timeoutMs), ("deadline_ms", toJson config.deadlineMs)]).pretty
    let status := match result.outcome with
      | .sat _ => "sat" | .unsat => "unsat" | .unknown _ => "unknown"
      | .timedOut => "timeout" | .error _ => "error"
    record "solver" status [("elapsed_ms", toJson result.process.elapsedMs),
      ("timeout_ms", toJson process.timeoutMs), ("deadline_ms", toJson config.deadlineMs)]
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

private def children : Expr → List Expr
  | .app f a => [f, a]
  | .lam _ t b _ | .forallE _ t b _ => [t, b]
  | .letE _ t v b _ => [t, v, b]
  | .mdata _ e | .proj _ _ e => [e]
  | _ => []

/-- Follow generated helpers, stopping at declarations present before the trial. -/
private def proofPackage (baseline : Environment) (roots : Array Expr)
    : TermElabM (Array ConstantInfo) := do
  let env ← getEnv
  let mut states : Std.HashMap Name Nat := {}
  let mut pending := roots.toList.flatMap (fun e => e.getUsedConstants.toList.map (·, false))
  let mut ordered := #[]
  while let (name, visited) :: rest := pending do
    pending := rest
    if baseline.contains name || states[name]? == some 2 then continue
    let some info := env.find? name | throwError "missing proof dependency {name}"
    if visited then
      states := states.insert name 2
      ordered := ordered.push info
    else
      if states[name]? == some 1 then throwError "cyclic generated proof dependency {name}"
      let some value := info.value? true | throwError "unsupported generated proof dependency {name}"
      states := states.insert name 1
      let deps := info.type.getUsedConstants.toList ++ value.getUsedConstants.toList
      pending := deps.map (·, false) ++ (name, true) :: pending
  return ordered

/-- DAG metrics: new helper types and bodies are included without materializing expansions. -/
private def expressionStats (roots : Array Expr) (helpers : Array ConstantInfo)
    : Nat × Nat × Nat := Id.run do
  let values : Std.HashMap Name (List Expr) := helpers.foldl (fun m info =>
    m.insert info.name [info.type, info.value! true]) {}
  let descendants := fun (e : Expr) => match e with
    | .const name _ => values.getD name []
    | _ => children e
  let mut depths : Std.HashMap Expr Nat := {}
  let mut constants : NameSet := {}
  let mut pending := roots.toList.map (·, false)
  while let (e, visited) :: rest := pending do
    pending := rest
    if depths.contains e then continue
    if visited then
      depths := depths.insert e (1 + (descendants e).foldl (fun n c => max n (depths[c]!)) 0)
      if let .const name _ := e then constants := constants.insert name
    else
      pending := (descendants e).map (·, false) ++ (e, true) :: pending
  return (roots.foldl (fun n e => max n (depths[e]!)) 0, depths.size, constants.size)

private def replayDeclaration : ConstantInfo → TermElabM Declaration
  | .thmInfo value => pure (.thmDecl value)
  | .defnInfo value => pure (.defnDecl value)
  | .opaqueInfo value => pure (.opaqueDecl value)
  | info => throwError "cannot replay generated declaration {info.name}"


/-- Check the original theorem and generated helpers against the pre-trial environment. -/
private def checkBridge (output : System.FilePath) (baseline : Environment) (original target : Expr)
    (goals : Array MVarId) : TermElabM Json := do
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
      let type ← mkForallFVars hypotheses target
      let helpers ← measure output "verify/helpers" fun _ => proofPackage baseline #[type, proof]
      let declarations ← helpers.mapM replayDeclaration
      let finalDecl := Declaration.thmDecl {
        name := ← mkFreshUserName `rq3_certificate
        levelParams := [], type, value := proof }
      let context ← readThe Core.Context
      let opts := maxRecDepth.set (maxHeartbeats.set
        ((← getOptions).setBool `debug.skipKernelTC false) 0) context.maxRecDepth
      let kernelStart ← IO.monoNanosNow
      measure output "verify/kernel" fun _ => do
        let mut kernel := baseline.toKernelEnv
        for declaration in declarations.push finalDecl do
          match kernel.addDecl opts declaration context.cancelTk? with
          | .ok next => kernel := next
          | .error error => throwError "kernel rejected proof package: {error.toMessageData opts}"
      let kernelNs := (← IO.monoNanosNow) - kernelStart
      measure output "verify/type" fun _ => do
        unless ← isDefEq (← inferType proof) (← mkForallFVars hypotheses target) do
          throwError "certificate does not prove the original target"
      measure output "verify/axioms" fun _ => do
        for name in proof.getUsedConstants do
          for axiomName in ← collectAxioms name do
            unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
              throwError "certificate depends on {axiomName}"
      let (packageDepth, packageNodes, packageConstants) ← measure output "verify/metrics" fun _ =>
        pure (expressionStats #[type, proof] helpers)
      return Json.mkObj [("kernel_ns", toJson kernelNs),
        ("kernel_scope", toJson "original bridge and all generated auxiliary declarations"),
        ("proof_package_depth", toJson packageDepth),
        ("proof_package_nodes", toJson packageNodes),
        ("proof_package_constants", toJson packageConstants),
        ("proof_auxiliary_declarations", toJson helpers.size),
        ("proof_metrics_version", toJson (2 : Nat)),
        ("proof_depth", toJson proof.approxDepth.toNat),
        ("proof_nodes", toJson (← proof.numObjs)),
        ("proof_constants", toJson proof.getUsedConstants.size)]
  finally Flex.CHC.restoreTermState saved

/-- Markers live in the saved metavariable state, so rolled-back attempts disappear. -/
private structure Retention where
  marker : MVarId
  markerType : Expr
  key : Name
  backend : String
  remainingHeads : Option Nat
  heads : Array MVarId
  paStage : Option Nat
  scrapeMode : Option String

private def remember (records : IO.Ref (Array Retention)) (key : Name) (backend : String)
    (remainingHeads : Option Nat) (goals : Array MVarId) (zap := false)
    (pa : Option PAStage := none) : TermElabM Unit := do
  let index := (← records.get).size
  let markerType ← mkEq (mkNatLit index) (mkNatLit index)
  let marker ← mkFreshExprMVar markerType
  let heads ← if zap then pure goals else goals.filterM fun goal => do
    let tag := (← goal.getTag).toString
    return tag.contains "_head"
  records.modify (·.push {
    marker := marker.mvarId!, markerType, key, backend,
    remainingHeads, heads, paStage := pa.map (·.index), scrapeMode := pa.bind (·.mode) })

private def retained (records : Array Retention) : TermElabM Json := do
  let mut selected : Std.HashMap Name Retention := {}
  for record in records do
    if let some decl := (← getMCtx).decls.find? record.marker then
      if decl.type == record.markerType then selected := selected.insert record.key record
  let mut remaining := 0
  let mut known := true
  let mut rows := #[]
  for (_, record) in selected do
    let mut count := record.remainingHeads
    if count == some record.heads.size then
      let n ← record.heads.foldlM (fun n goal => do
        let proof ← instantiateMVars (mkMVar goal)
        return n + if proof.hasMVar then 1 else 0) 0
      count := some n
    known := known && count.isSome
    remaining := remaining + count.getD 0
    rows := rows.push (Json.mkObj [("backend", toJson record.backend),
      ("remaining_heads", toJson count), ("pa_stage", toJson record.paStage),
      ("scrape_mode", toJson record.scrapeMode)])
  return Json.mkObj [("retained_candidates", Json.arr rows),
    ("remaining_heads", if known then toJson remaining else Json.null),
    ("heads_known", toJson known)]

private partial def graph (target : Expr) : Tactic.TacticM (Array Nat) := do
  let target ← whnf target
  if target.isForall then
    return ← withLocalDeclD target.bindingName! target.bindingDomain! fun x =>
      graph (target.bindingBody!.instantiate1 x)
  if let some (a, b) := target.and? then
    let a ← graph a; let b ← graph b
    return a.zipWith (· + ·) b
  unless target.isAppOfArity ``Exists 2 do return #[0, 0, 0, 0]
  let result ← IO.mkRef #[0, 0, 0, 0]
  withPeeledExists target #[] fun binders body => do
    let mut body := body
    let mut vars : Array KVar := #[]
    for (name, ty, fv) in binders do
      let types ← collectArrowTypes ty
      let mv ← mkFreshExprMVar ty (kind := .syntheticOpaque)
      vars := vars.push {
        name, paramTypes := types,
        params := (List.range types.length).map (fun i => Name.mkSimple s!"x{i}"),
        mvarId := mv.mvarId! }
      body := body.replaceFVar fv mv
    let ctx : KContext := { kvars := vars.foldl (fun m k => m.insert k.mvarId k) {} }
    let deps ← (exprDeps body).run ctx
    let (elim, cut) ← (exprPartitionKVars body).run ctx
    let cyc := (tarjanSCC vars.toList deps).filter fun scc =>
      scc.length > 1 || scc.any (fun k => hasSelfLoop k deps)
    result.set #[vars.size - cyc.flatten.length, cyc.flatten.length, elim.length, cut.length]
  result.get

private def classify (target : Expr) : TermElabM Json := do
  let saved ← saveState
  try
    let original ← mkFreshExprMVar target
    let goal ← Flex.Preprocess.prepareGoal original.mvarId!
    let countsRef ← IO.mkRef #[0,0,0,0]
    unless ← goal.isAssignedOrDelayedAssigned do
      discard $ Tactic.run goal do
        countsRef.set (← graph (← goal.getType))
    let counts ← countsRef.get
    let kind := if counts[0]! + counts[1]! == 0 then "none"
      else if counts[1]! == 0 then "acyclic_only"
      else if counts[0]! == 0 then "cyclic_only" else "mixed"
    return Json.mkObj [("kind", toJson kind), ("acyclic", toJson counts[0]!),
      ("cyclic", toJson counts[1]!), ("eliminable", toJson counts[2]!),
      ("cut", toJson counts[3]!)]
  finally Flex.CHC.restoreTermState saved

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

/-- Run the original assertions with a model request and the benchmark timeout. -/
def native : TermElabM Unit := do
  let some dir ← IO.getEnv "FLEX_PARITY_OUTPUT" | throwError "missing output"
  let dir : System.FilePath := dir
  let some input ← IO.getEnv "FLEX_PARITY_INPUT" | throwError "missing input"
  let backend := (← IO.getEnv "RQ3_NATIVE").getD "spacer"
  let executable ← IO.getEnv "FLEX_PARITY_EXECUTABLE"
  let seconds ← envNat "FLEX_PARITY_SOLVER_SECONDS" 90
  let config : Flex.CHC.Config := {
    backend := if backend == "spacer" then .spacer else .eldarica
    executable, timeoutMs := seconds * 1000 }
  let source ← IO.FS.readFile input
  let (input, removed, addedLogic) ← ofExcept (nativeInput source)
  let script := input ++ "(get-model)\n"
  IO.FS.writeFile (dir / "sent.smt2") script
  let result ← Flex.CHC.Process.run config.toProcessConfig script
  IO.FS.writeFile (dir / "stdout.txt") result.stdout
  IO.FS.writeFile (dir / "stderr.txt") result.stderr
  let answer := (result.stdout.splitOn "\n").findSome? fun line =>
    let line := line.trimAscii.toString
    if #["sat", "unsat", "unknown"].contains line then some line else none
  let status := match result.completion with
    | .timedOut => "solver_timeout"
    | .exited 0 => answer.getD "solver_error"
    | _ => "solver_error"
  let model := status == "sat" && !(result.stdout.contains "(error") &&
    (result.stdout.contains "define-fun" || result.stdout.contains "()" ||
      result.stdout.contains "(model)")
  IO.FS.writeFile (dir / "native.json") (Json.mkObj [
    ("status", toJson (if status == "sat" && !model then "sat_no_model" else status)),
    ("model_obtained", toJson model), ("elapsed_ms", toJson result.elapsedMs),
    ("removed_commands", toJson removed), ("added_horn_logic", toJson addedLogic),
    ("args", toJson config.toProcessConfig.args),
    ("timeout_ms", toJson config.timeoutMs)]).pretty


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
      let heartbeats ← envNat "FLEX_PARITY_HEARTBEATS" 4000000
      let proofHeartbeats ← envNat "FLEX_PARITY_PROOF_HEARTBEATS" 40000
      let synthHeartbeats ← envNat "FLEX_PARITY_SYNTH_HEARTBEATS" 0
      let preparation := (← IO.getEnv "FLEX_PARITY_PREPARE").filter fun source =>
        !source.trimAscii.isEmpty
      let zap := (← IO.getEnv "FLEX_PARITY_ZAP").getD "1" != "0"
      let full := (← IO.getEnv "FLEX_PARITY_FULL").getD "0" == "1"
      let solvers := (← IO.getEnv "FLEX_PARITY_SE").getD "1" != "0"
      let chcFirst := (← IO.getEnv "RQ3_CHC_FIRST").getD "0" == "1"
      let stageSeconds ← envNat "RQ3_STAGE_SECONDS" 0
      let zapSeconds ← envNat "FLEX_PARITY_ZAP_SECONDS" 0
      let paSeconds ← envNat "FLEX_PARITY_PA_SECONDS" 0
      let totalSeconds ← envNat "FLEX_PARITY_FLEX_SECONDS" (if full && solvers then 360 else 180)
      let caseSeconds ← envNat "FLEX_PARITY_CASE_SECONDS" (totalSeconds + 120)
      let solverSeconds ← envNat "FLEX_PARITY_SOLVER_SECONDS" 90
      let scrapeName := (← IO.getEnv "FLEX_PARITY_SCRAPE").getD "auto"
      let scrapeMode : PAScrapeMode ← match scrapeName with
        | "no" => pure .no | "basic" => pure .basic
        | "standard" => pure .standard | "deep" => pure .deep
        | "auto" => pure .auto
        | _ => throwError "invalid FLEX_PARITY_SCRAPE: {scrapeName}"
      let profilePA := (← IO.getEnv "FLEX_PARITY_PROFILE_PA").getD "0" == "1"
      let diagnostic := (← IO.getEnv "RQ3_DIAGNOSTIC").getD "0" == "1"
      let backends : List Flex.Portfolio.Backend :=
        (if full then [.fix] else []) ++ (if solvers then [.spacer, .eldarica] else [])
      let recursionLimit ← envNat "FLEX_PARITY_RECURSION_LIMIT" 16384
      let spacerExe ← IO.getEnv "FLEX_PARITY_EXECUTABLE"
      let eldaricaExe ← IO.getEnv "FLEX_PARITY_ELDARICA_EXECUTABLE"
      let currentOptions ← getOptions
      let options := Id.run do
        let opts := flex.benchOracles.set currentOptions profilePA
        let opts := opts.setBool `trace.flex diagnostic
        let opts := opts.setBool `trace.flex.synthesis profilePA
        let opts := flex.automation.proofHeartbeats.set opts proofHeartbeats
        let opts := flex.fixpointTimeout.set opts totalSeconds
        -- RQ3a defaults to SMT-only synthesis; semantic scraping runs can enable
        -- the library's native fallback explicitly without changing earlier trials.
        let opts := flex.automation.synthHeartbeats.set opts synthHeartbeats
        -- Refinement-type constraints use non-linear arithmetic (e.g. `%` by a variable);
        -- leave it to the solver instead of bailing.
        let opts := flex.smt.encodeNonlinear.set opts true
        let opts := match spacerExe with
          | some executable => flex.spacer.executable.set opts executable
          | none => opts
        let opts := match eldaricaExe with
          | some executable => flex.eldarica.executable.set opts executable
          | none => opts
        return opts
      withOptions (fun _ => options) do
        withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := recursionLimit }) do
          let config : Flex.Portfolio.Config := {
            nesting := false, zap, chcFirst, stageTimeout := stageSeconds
            zapTimeout := zapSeconds, paTimeout := paSeconds
            heartbeats, totalTimeout := totalSeconds, solverTimeout := solverSeconds }
          IO.FS.writeFile (output / "invocation.json") (Json.mkObj [
            ("entry_point", toJson "Flex.Portfolio.flexImpl"),
            ("backends", toJson (backends.map toString)),
            ("chc_first", toJson chcFirst),
            ("stage_timeout_seconds", toJson stageSeconds),
            ("zap_timeout_seconds", toJson zapSeconds),
            ("pa_timeout_seconds", toJson paSeconds),
            ("scrape", if full then toJson scrapeName else Json.null),
            ("profile_pa", toJson profilePA),
            ("input_preparation", toJson preparation),
            ("diagnostic", toJson diagnostic),
            ("preprocess", toJson config.preprocess), ("zap", toJson config.zap),
            ("postprocess", toJson config.postprocess), ("nesting", toJson config.nesting),
            ("split_free", toJson config.splitFree),
            ("keep_candidates", toJson config.keepCandidates),
            ("total_timeout_seconds", toJson config.totalTimeout),
            ("fixpoint_timeout_seconds", toJson (if paSeconds > 0 then 0 else
              flex.fixpointTimeout.get options)),
            ("solver_timeout_seconds", toJson config.solverTimeout),
            ("timeout_policy", toJson (if zapSeconds > 0 || paSeconds > 0 then
              "component_caps_v1" else "reserved_blocks_v1")),
            ("oracle_timeout_policy", toJson "remaining backend allocation"),
            ("case_timeout_seconds", toJson caseSeconds),
            ("phase_heartbeats", toJson heartbeats),
            ("proof_heartbeats", toJson proofHeartbeats),
            ("smt_uninterpreted_defs", toJson (flex.smt.uninterpretedDefs.get options)),
            ("smt_encode_nonlinear", toJson (flex.smt.encodeNonlinear.get options)),
            ("smt_encode_quantifiers", toJson (flex.smt.encodeQuantifiers.get options)),
            ("synth_heartbeats", toJson (flex.automation.synthHeartbeats.get options)),
            ("recursion_limit", toJson recursionLimit)]).pretty
          let target := Lean.mkConst name
          let baseline ← getEnv
          let original ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
          let prepared ← match preparation with
            | none => pure original.mvarId!
            | some source => do
              let tactic ← match Parser.runParserCategory (← getEnv) `tactic ("(\n" ++ source ++ "\n)") with
                | .ok tactic => pure tactic
                | .error error => throwError "input preparation: {error}"
              let goals ← measure output "prepare/input" fun _ =>
                Tactic.run original.mvarId! (Tactic.evalTactic tactic)
              let [goal] := goals
                | throwError "input preparation must leave exactly one goal"
              pure goal
          -- Measure the prepared proposition, not the file or recursively expanded definitions.
          let inputMetrics ← measure output "input/metrics" fun _ => prepared.withContext do
            let expression ← whnf (← instantiateMVars (← prepared.getType))
            let (depth, nodes, constants) := expressionStats #[expression] #[]
            pure (Json.mkObj [("expr_depth", toJson depth), ("expr_dag_nodes", toJson nodes),
              ("expr_constants", toJson constants),
              ("scope", toJson "prepared goal after top-level unfolding; named model definitions remain opaque")])
          IO.FS.writeFile (output / "input_metrics.json") inputMetrics.pretty
          -- Structural classification shares the trial's process; it precedes the measured tactic.
          if (← IO.getEnv "RQ3_CLASSIFY").getD "1" != "0" then
            let classifyStart ← IO.monoMsNow
            let info ← tryCatchRuntimeEx (prepared.withContext do
                some <$> classify (← prepared.getType)) fun error => do
              if error.isInterrupt then throw error
              emit output "classification" "failed" [("error", toJson (← error.toMessageData.toString))]
              pure none
            if let some info := info then
              IO.FS.writeFile (output / "classification.json") info.pretty
              emit output "classification" "ok"
                [("elapsed_ms", toJson ((← IO.monoMsNow) - classifyStart))]
          let before ← prepared.withContext do predicateCount (← prepared.getType)
          stage.set "flex"
          emit output "flex" "running" [("original_predicates", toJson before)]
          let attempt ← IO.mkRef 0
          let backendAttempt ← IO.mkRef 0
          let retentions ← IO.mkRef (#[] : Array Retention)
          let paState ← IO.mkRef ({} : PAStage)
          let tacticStart ← IO.monoMsNow
          let tacticHB ← IO.getNumHeartbeats
          let goals ← Tactic.run prepared $ Flex.Portfolio.flexImpl {
            config, backends, scrape := { mode := scrapeMode }
            onPhase := fun event => do
              let isAttempt := event.phase.startsWith "attempt/"
              if isAttempt && event.status == "start" then backendAttempt.modify (· + 1)
              let index ← backendAttempt.get
              emitPhase output event (if isAttempt && !event.status.startsWith "skipped_" then
                some index else none)
            onPA := if profilePA then recordPA output paState else fun _ => pure ()
            onCHC := recordCHC output attempt backendAttempt
            onSynthesis := fun goal backend _ heads goals => do
              let pa ← if backend == .fix && profilePA then some <$> paState.get else pure none
              remember retentions goal.name (toString backend) heads goals (pa := pa)
            onZap := fun heads => do
              let key ← mkFreshId
              remember retentions key "zap" (some heads.size) heads true }
          let tacticHeartbeats := ((← IO.getNumHeartbeats) - tacticHB) / 1000
          let flexMs := (← IO.monoMsNow) - tacticStart
          let retention ← retained (← retentions.get)
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
          let proofMetrics ← checkBridge output baseline original target goals.toArray
          emit output "kernel" "ok" [("elapsed_ms", toJson ((← IO.monoMsNow) - kernelStart))]
          emit output "result" (if goals.isEmpty then "proved" else "partial") [
            ("retention", retention), ("proof_metrics", proofMetrics),
            ("tactic_heartbeats", toJson tacticHeartbeats),
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
