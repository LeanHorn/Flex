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
    let some n := value.toNat? | throw <| IO.userError s!"invalid {name}: {value}"
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

/-- Names of predicate existentials still present in the positive constraint structure. -/
private partial def predicateNames (target : Expr) : MetaM (Array Name) := do
  let target ← whnf (← instantiateMVars target)
  if target.isAppOfArity ``Exists 2 then
    let domain := target.getArg! 0
    let isPredicate ← forallTelescopeReducing domain fun _ result => pure result.isProp
    let name := match target.appArg! with
      | .lam name .. => name
      | _ => `_
    return ← withLocalDeclD name domain fun witness => do
      let rest ← predicateNames (target.appArg!.beta #[witness])
      return if isPredicate then rest.push name else rest
  if let some (left, right) := target.and? then
    return (← predicateNames left) ++ (← predicateNames right)
  if target.isForall then
    return ← withLocalDecl target.bindingName! target.bindingInfo! target.bindingDomain!
      fun x => predicateNames (target.bindingBody!.instantiate1 x)
  return #[]

/-- Check the original theorem as a function of exactly the reported residual goals. -/
private def checkBridge (output : System.FilePath) (original target : Expr)
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
      let kernelStart ← IO.monoNanosNow
      measure output "verify/kernel" fun _ => withoutModifyingEnv do
        addDecl (.thmDecl {
          name := ← mkFreshUserName `rq3_certificate
          levelParams := [], type, value := proof })
      let kernelNs := (← IO.monoNanosNow) - kernelStart
      measure output "verify/type" fun _ => do
        unless ← isDefEq (← inferType proof) (← mkForallFVars hypotheses target) do
          throwError "certificate does not prove the original target"
      measure output "verify/axioms" fun _ => do
        for name in proof.getUsedConstants do
          for axiomName in ← collectAxioms name do
            unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
              throwError "certificate depends on {axiomName}"
      return Json.mkObj [("kernel_ns", toJson kernelNs),
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

private def remember (records : IO.Ref (Array Retention)) (key : Name) (backend : String)
    (remainingHeads : Option Nat) (goals : Array MVarId) (zap := false) : TermElabM Unit := do
  let index := (← records.get).size
  let markerType ← mkEq (mkNatLit index) (mkNatLit index)
  let marker ← mkFreshExprMVar markerType
  let heads ← if zap then pure goals else goals.filterM fun goal => do
    let tag := (← goal.getTag).toString
    return tag.contains "_head"
  records.modify (·.push {
    marker := marker.mvarId!, markerType, key, backend,
    remainingHeads, heads })

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
      ("remaining_heads", toJson count)])
  return Json.mkObj [("retained_candidates", Json.arr rows),
    ("remaining_heads", if known then toJson remaining else Json.null),
    ("heads_known", toJson known)]

/-- Cyclic predicate names and predicate dependency edges, across all ∃-blocks. -/
private structure GraphInfo where
  /-- Predicates on a dependency cycle (strongly connected components). -/
  sccCyclic : Array Name := #[]
  /-- Zap's cut set: the predicates Zap cannot eliminate. -/
  cut : Array Name := #[]
  edges : Array (Name × Name) := #[]

private partial def graph (info : IO.Ref GraphInfo) (target : Expr) : Tactic.TacticM (Array Nat) := do
  let target ← whnf target
  if target.isForall then
    return ← withLocalDeclD target.bindingName! target.bindingDomain! fun x =>
      graph info (target.bindingBody!.instantiate1 x)
  if let some (a, b) := target.and? then
    let a ← graph info a; let b ← graph info b
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
    info.modify fun i => { sccCyclic := i.sccCyclic ++ (cyc.flatten.map (·.name)).toArray,
                           cut := i.cut ++ (cut.map (·.name)).toArray,
                           edges := i.edges ++ (deps.map fun (a, b) => (a.name, b.name)).toArray }
  result.get

private def classify (target : Expr) : TermElabM Json := do
  let saved ← saveState
  try
    let original ← mkFreshExprMVar target
    let goal ← Flex.Preprocess.prepareGoal original.mvarId!
    let countsRef ← IO.mkRef #[0,0,0,0]
    let info ← IO.mkRef ({} : GraphInfo)
    unless ← goal.isAssignedOrDelayedAssigned do
      discard <| Tactic.run goal do
        countsRef.set (← graph info (← goal.getType))
    let info ← info.get
    let counts ← countsRef.get
    -- Cyclic means Zap's cut set (predicates Zap cannot eliminate); acyclic means Zap
    -- eliminates it, including predicates on a cycle that every cycle reaches through a
    -- cut predicate. Strongly connected components are kept as `scc_*` for reference.
    let (acyclic, cyclic) := (counts[2]!, counts[3]!)
    let kind := if acyclic + cyclic == 0 then "none"
      else if cyclic == 0 then "acyclic_only"
      else if acyclic == 0 then "cyclic_only" else "mixed"
    return Json.mkObj [("kind", toJson kind), ("acyclic", toJson acyclic),
      ("cyclic", toJson cyclic), ("eliminable", toJson counts[2]!),
      ("cut", toJson counts[3]!),
      ("cyclic_predicates", toJson (info.cut.map (·.toString))),
      ("scc_acyclic", toJson counts[0]!), ("scc_cyclic", toJson counts[1]!),
      ("scc_cyclic_predicates", toJson (info.sccCyclic.map (·.toString))),
      ("dependency_edges", toJson (info.edges.map fun (a, b) => #[a.toString, b.toString]))]
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
      -- Overrides for budget-sensitivity checks; defaults match Flex.
      let dischargeHeartbeats ← envNat "FLEX_PARITY_DISCHARGE_HEARTBEATS" 500000
      let smtSeconds ← envNat "FLEX_PARITY_SMT_SECONDS" 30
      let zap := (← IO.getEnv "FLEX_PARITY_ZAP").getD "1" != "0"
      let full := (← IO.getEnv "FLEX_PARITY_FULL").getD "0" == "1"
      let solvers := (← IO.getEnv "FLEX_PARITY_SE").getD "1" != "0"
      let chcFirst := (← IO.getEnv "RQ3_CHC_FIRST").getD "0" == "1"
      let stageSeconds ← envNat "RQ3_STAGE_SECONDS" 0
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
      -- RQ3_SE_BACKENDS selects the CHC solvers (default both, Spacer first).
      let seNames := ((← IO.getEnv "RQ3_SE_BACKENDS").getD "spacer,eldarica").splitOn ","
      let seBackends : List Flex.Portfolio.Backend ← seNames.mapM fun
        | "spacer" => pure .spacer | "eldarica" => pure .eldarica
        | other => throwError "invalid RQ3_SE_BACKENDS entry: {other}"
      let backends : List Flex.Portfolio.Backend :=
        (if full then [.fix] else []) ++ (if solvers then seBackends else [])
      let recursionLimit ← envNat "FLEX_PARITY_RECURSION_LIMIT" 16384
      let spacerExe ← IO.getEnv "FLEX_PARITY_EXECUTABLE"
      let eldaricaExe ← IO.getEnv "FLEX_PARITY_ELDARICA_EXECUTABLE"
      let currentOptions ← getOptions
      let options := Id.run do
        let opts := flex.benchOracles.set currentOptions profilePA
        let opts := opts.setBool `trace.flex diagnostic
        let opts := opts.setBool `trace.flex.synthesis profilePA
        let opts := flex.automation.proofHeartbeats.set opts proofHeartbeats
        let opts := flex.automation.smtTimeout.set opts smtSeconds
        -- Record each predicate-head obligation with its hypothesis predicates.
        let opts := flex.logObligations.set opts true
        let opts := flex.fixpointTimeout.set opts totalSeconds
        -- Synthesis decides candidates with the exact SMT encoding alone; undecided
        -- candidates are dropped. Certification and discharge still use Lean automation.
        let opts := flex.automation.synthHeartbeats.set opts 0
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
      withOptions (fun _ => options) <|
        withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := recursionLimit }) do
          let config : Flex.Portfolio.Config := {
            nesting := false, zap, chcFirst, stageTimeout := stageSeconds
            heartbeats, totalTimeout := totalSeconds, solverTimeout := solverSeconds
            dischargeHeartbeats }
          IO.FS.writeFile (output / "invocation.json") (Json.mkObj [
            ("entry_point", toJson "Flex.Portfolio.flexImpl"),
            ("backends", toJson (backends.map toString)),
            ("chc_first", toJson chcFirst),
            ("stage_timeout_seconds", toJson stageSeconds),
            ("scrape", if full then toJson scrapeName else Json.null),
            ("profile_pa", toJson profilePA),
            ("diagnostic", toJson diagnostic),
            ("preprocess", toJson config.preprocess), ("zap", toJson config.zap),
            ("postprocess", toJson config.postprocess), ("nesting", toJson config.nesting),
            ("split_free", toJson config.splitFree),
            ("keep_candidates", toJson config.keepCandidates),
            ("total_timeout_seconds", toJson config.totalTimeout),
            ("fixpoint_timeout_seconds", toJson (flex.fixpointTimeout.get options)),
            ("solver_timeout_seconds", toJson config.solverTimeout),
            ("timeout_policy", toJson "reserved_blocks_v1"),
            ("oracle_timeout_policy", toJson "remaining backend allocation"),
            ("case_timeout_seconds", toJson caseSeconds),
            ("phase_heartbeats", toJson heartbeats),
            ("proof_heartbeats", toJson proofHeartbeats),
            ("discharge_heartbeats", toJson dischargeHeartbeats),
            ("smt_timeout_seconds", toJson smtSeconds),
            ("smt_uninterpreted_defs", toJson (flex.smt.uninterpretedDefs.get options)),
            ("smt_encode_nonlinear", toJson (flex.smt.encodeNonlinear.get options)),
            ("smt_encode_quantifiers", toJson (flex.smt.encodeQuantifiers.get options)),
            ("synth_heartbeats", toJson (flex.automation.synthHeartbeats.get options)),
            ("recursion_limit", toJson recursionLimit)]).pretty
          let target := Lean.mkConst name
          -- Structural classification shares the trial's process; it precedes the measured tactic.
          if (← IO.getEnv "RQ3_CLASSIFY").getD "1" != "0" then
            let classifyStart ← IO.monoMsNow
            let info ← tryCatchRuntimeEx (some <$> classify target) fun error => do
              if error.isInterrupt then throw error
              emit output "classification" "failed" [("error", toJson (← error.toMessageData.toString))]
              pure none
            if let some info := info then
              IO.FS.writeFile (output / "classification.json") info.pretty
              emit output "classification" "ok"
                [("elapsed_ms", toJson ((← IO.monoMsNow) - classifyStart))]
          let before ← predicateCount target
          let original ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
          stage.set "flex"
          emit output "flex" "running" [("original_predicates", toJson before)]
          let attempt ← IO.mkRef 0
          let backendAttempt ← IO.mkRef 0
          let retentions ← IO.mkRef (#[] : Array Retention)
          let tacticStart ← IO.monoMsNow
          let tacticHB ← IO.getNumHeartbeats
          let goals ← Tactic.run original.mvarId! <| Flex.Portfolio.flexImpl {
            config, backends, scrape := { mode := scrapeMode }
            onPhase := fun event => do
              let isAttempt := event.phase.startsWith "attempt/"
              if isAttempt && event.status == "start" then backendAttempt.modify (· + 1)
              let index ← backendAttempt.get
              emitPhase output event (if isAttempt && !event.status.startsWith "skipped_" then
                some index else none)
            onPA := if profilePA then recordPA output else fun _ => pure ()
            onCHC := recordCHC output attempt backendAttempt
            onSynthesis := fun goal backend _ heads goals =>
              remember retentions goal.name (toString backend) heads goals
            onZap := fun heads => do
              let key ← mkFreshId
              remember retentions key "zap" (some heads.size) heads true }
          let tacticHeartbeats := ((← IO.getNumHeartbeats) - tacticHB) / 1000
          let flexMs := (← IO.monoMsNow) - tacticStart
          let retention ← retained (← retentions.get)
          let markers ← Flex.Obligations.collect
          let kind (marker : Json) := (marker.getObjValAs? String "kind").toOption.getD ""
          let callOf (marker : Json) := (marker.getObjValAs? Nat "call").toOption.getD 0
          -- A query left as a goal is proved iff that goal is now closed.
          let queries ← (markers.filter (kind · == "query")).mapM fun marker => do
            let some goal := (marker.getObjValAs? String "goal").toOption | pure marker
            let proof ← instantiateMVars (mkMVar ⟨goal.toName⟩)
            pure (marker.setObjVal! "proved" (toJson !proof.hasExprMVar))
          let obligations := markers.filter (kind · == "head") ++ queries
          -- Goals the proof oracle left unproved, with the resource limits its attempts hit.
          let limits := markers.filter (kind · == "limit")
          let unprovedGoals := (markers.filter (kind · == "unproved")).map fun marker =>
            let call := callOf marker
            let reasons := (limits.filter (callOf · == call)).filterMap fun limit =>
              (limit.getObjValAs? String "reason").toOption
            Json.mkObj [("call", toJson call), ("limits", toJson reasons.toList.eraseDups)]
          emit output "flex" "ok" [("elapsed_ms", toJson flexMs)]
          let remainingNames ← IO.mkRef (#[] : Array String)
          let after ← measure output "checkpoint/format" fun _ => do
            let mut after := 0
            let mut residuals := []
            for goal in goals do
              after := after + (← goal.withContext do predicateCount (← goal.getType))
              let names ← goal.withContext do predicateNames (← goal.getType)
              remainingNames.modify (· ++ names.map (·.toString))
              residuals := residuals ++ [(← Meta.ppGoal goal).pretty]
            IO.FS.writeFile (output / "residual.txt") (String.intercalate "\n\n---\n\n" residuals)
            return after
          emit output "checkpoint" "retained" [
            ("goals", toJson goals.length), ("original_predicates", toJson before),
            ("remaining_predicates", toJson after), ("kernel_checked", toJson false)]
          stage.set "kernel"
          emit output "kernel" "running"
          let kernelStart ← IO.monoMsNow
          let proofMetrics ← checkBridge output original target goals.toArray
          emit output "kernel" "ok" [("elapsed_ms", toJson ((← IO.monoMsNow) - kernelStart))]
          emit output "result" (if goals.isEmpty then "proved" else "partial") [
            ("retention", retention), ("proof_metrics", proofMetrics),
            ("obligations", Json.arr obligations),
            ("unproved_goals", Json.arr unprovedGoals),
            ("remaining_predicate_names", toJson (← remainingNames.get)),
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
