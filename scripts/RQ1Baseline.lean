import Flex.Tactic
import Flex.CHC
import Flex.Tactic.Automation

/-! RQ1 synthesis measurements on original VCs, without importing their proofs. -/

open Lean Meta Elab Term Tactic Flex.CHC

set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option Elab.async false

namespace RQ1Baseline

private structure Context where
  caseName : String
  declaration : Name
  variant : String
  output : System.FilePath
  deadline : Nat
  paSeconds : Nat
  solverMs : Nat
  heartbeats : Nat
  dischargeResidual : Bool
  retainedSolver : IO.Ref String
  events : IO.Ref (Array Json)

private def envNat (name : String) (fallback : Nat) : IO Nat :=
  return ((← IO.getEnv name).bind String.toNat?).getD fallback

private def publish (ctx : Context) (marker : String) (value : Json) : IO Unit := do
  let line := marker ++ value.compress
  IO.FS.withFile (ctx.output / "progress.jsonl") .append (·.putStrLn line)
  let stdout ← IO.getStdout
  stdout.putStrLn line
  stdout.flush

private def emit (ctx : Context) (phase status : String)
    (fields : List (String × Json) := []) : IO Unit := do
  let event := Json.mkObj ([
    ("case", toJson ctx.caseName), ("variant", toJson ctx.variant),
    ("phase", toJson phase), ("status", toJson status)] ++ fields)
  ctx.events.modify (·.push event)
  publish ctx "FLEX_RQ1_PHASE " event

private def restore (state : Tactic.SavedState) : TacticM Unit := do
  restoreTermState state.term
  set state.tactic

private def checkTime (ctx : Context) : TermElabM Unit := do
  if (← IO.monoMsNow) >= ctx.deadline then throwError "RQ1 case budget exhausted"

private def predicateType (type : Expr) : MetaM Bool :=
  forallTelescopeReducing type fun _ result => return result.isProp

private partial def countPredicates (expression : Expr) : MetaM Nat := do
  let expression ← whnf (← instantiateMVars expression)
  if expression.isAppOfArity ``Exists 2 then
    let domain := expression.appFn!.appArg!
    unless ← predicateType domain do return 0
    return ← withLocalDeclD `predicate domain fun predicate => do
      return 1 + (← countPredicates (mkApp expression.appArg! predicate))
  if expression.isForall then
    return ← withLocalDecl expression.bindingName! expression.bindingInfo!
      expression.bindingDomain! fun value =>
        countPredicates (expression.bindingBody!.instantiate1 value)
  return 0

private def goalPredicates (goal : MVarId) : MetaM Nat :=
  goal.withContext do countPredicates (← goal.getType)

private def totalPredicates : TacticM Nat := do
  let counts ← (← getUnsolvedGoals).mapM fun goal => goalPredicates goal
  return counts.foldl (· + ·) 0

private partial def exposePredicateGoal (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    let target ← whnf (← goal.getType)
    if target.isForall then
      let (_, next) ← goal.intro1
      exposePredicateGoal next
    else return goal

private def onPredicates (action : TacticM Unit) : TacticM Unit := do
  let mut remaining := []
  for goal in ← getUnsolvedGoals do
    if (← goalPredicates goal) > 0 then
      setGoals [← exposePredicateGoal goal]
      action
      remaining := remaining ++ (← getUnsolvedGoals)
    else remaining := remaining ++ [goal]
  setGoals remaining

private def discharge : TacticM Unit := do
  let goals ← getUnsolvedGoals
  let predicates ← goals.filterM fun goal => return (← goalPredicates goal) > 0
  setGoals (goals.filter fun goal => !predicates.contains goal)
  Flex.Automation.discharge
  setGoals (predicates ++ (← getUnsolvedGoals))

private def saveGoals (ctx : Context) (phase : String) : TacticM Unit := do
  let goals ← (← getUnsolvedGoals).mapM fun goal => return (← Meta.ppGoal goal).pretty
  IO.FS.writeFile (ctx.output / s!"{phase}-goals.txt") (String.intercalate "\n\n" goals)

/-- Compare closed goal expressions across independent backend runs. -/
private def saveCheckpoint (ctx : Context) : TacticM Unit := do
  saveGoals ctx "zap"
  let saved ← Tactic.saveState
  try
    let expressions ← (← getUnsolvedGoals).mapM fun goal => do
      let closed ← goal.revertAll
      let expression ← instantiateMVars (← closed.getType)
      if expression.hasMVar || expression.hasFVar || expression.hasLooseBVars then
        throwError "post-Zap checkpoint contains unresolved variables"
      let expression ← Core.transform expression (post := fun e => pure <| .done <|
        match e with
        | .mdata _ body => body
        | .forallE _ type body bi => .forallE .anonymous type body bi
        | .lam _ type body bi => .lam .anonymous type body bi
        | .letE _ type value body nondep => .letE .anonymous type value body nondep
        | _ => e)
      return reprStr expression
    IO.FS.writeFile (ctx.output / "post-zap-expressions.txt")
      (String.intercalate "\n\n" expressions)
  finally restore saved

private def attempt (ctx : Context) (phase : String) (action : TacticM Unit)
    : TacticM Bool := do
  let before ← totalPredicates
  let saved ← Tactic.saveState
  let messages ← Core.getMessageLog
  let start ← IO.monoMsNow
  let heartbeats ← IO.getNumHeartbeats
  emit ctx phase "running" [("predicates_before", toJson before)]
  try
    tryCatchRuntimeEx (do
      checkTime ctx
      withTheReader Core.Context (fun c => { c with maxHeartbeats := ctx.heartbeats * 1000 }) <|
        Core.withCurrHeartbeats action
      pruneSolvedGoals
      let after ← totalPredicates
      emit ctx phase (if (← getUnsolvedGoals).isEmpty then "proved" else "partial") [
        ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
        ("heartbeats", toJson (((← IO.getNumHeartbeats) - heartbeats) / 1000)),
        ("predicates_before", toJson before), ("predicates_after", toJson after),
        ("predicates_instantiated", toJson (before - after)),
        ("remaining_goals", toJson (← getUnsolvedGoals).length)]
      saveGoals ctx phase
      return true)
      (fun error => do
        let message ← error.toMessageData.toString
        restore saved
        emit ctx phase "failed" [
          ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
          ("heartbeats", toJson (((← IO.getNumHeartbeats) - heartbeats) / 1000)),
          ("predicates_before", toJson before), ("predicates_after", toJson before),
          ("predicates_instantiated", toJson (0 : Nat)), ("error", toJson message)]
        return false)
  finally Core.setMessageLog messages

private def runFix (ctx : Context) : TacticM Unit := do
  let mode := if ctx.variant.endsWith "basic" then PAScrapeMode.basic
    else if ctx.variant.endsWith "standard" then PAScrapeMode.standard else PAScrapeMode.deep
  let start ← IO.monoMsNow
  -- Synthesis stops at the case deadline or after the PA budget, whichever comes first.
  let synthDeadline := some (min ctx.deadline (start + ctx.paSeconds * 1000))
  let observe : PAObserver := fun event => match event with
    | .stageStarted mode => emit ctx "fix_stage" "start" [("mode", toJson (toString mode))]
    | .stageFinished mode accepted => emit ctx "fix_stage" "end" [
        ("mode", toJson (toString mode)), ("accepted", toJson accepted)]
    | .setup scraped standard tagged candidates => emit ctx "fix_setup" "prepared" [
        ("scraped_templates", toJson scraped), ("standard_templates", toJson standard),
        ("tagged_templates", toJson tagged),
        ("initial_candidates", toJson (candidates.foldl (fun n (_, count) => n + count) 0))]
    | .roundStarted count => emit ctx "fix_round" "running" [("candidates", toJson count)]
    | .roundFinished before after => emit ctx "fix_round" "completed" [
        ("candidates_before", toJson before), ("candidates_after", toJson after)]
    | .converged count => emit ctx "fix_converged" "candidate" [("candidates", toJson count)]
  onPredicates <| fixImpl proveLeaf { mode } (some Flex.Automation.proofOracle)
    observe (some fun targets =>
      Flex.Timeout.withDeadline synthDeadline (Flex.Automation.synthOracle targets))

/-- Solver-alone variants `spacer` and `eldarica`: exactly one solver call per CHC, with no
retries and no model fallback. Each uses the configuration that proved the most RQ1 CHCs in a
sweep over the settings the retries vary, plus quantified clauses: Spacer with its default
settings, Eldarica with quantified clauses (`flex.chc.encodeQuantifiers`). -/
private def soloBackend? : String → Option Flex.CHC.Backend
  | "spacer" => some .spacer
  | "eldarica" => some .eldarica
  | _ => none

private def runSolver (ctx : Context) (config : Flex.CHC.Config)
    (remainingHeads : IO.Ref (Option Nat)) (provedHeads : IO.Ref Nat) : TacticM Unit := do
  let label := if config.backend == Flex.CHC.Backend.spacer then "spacer" else "eldarica"
  let index ← IO.mkRef 0
  onPredicates do
    let i ← index.get
    index.modify (· + 1)
    let result ← solveGoal (← getMainGoal) config
      Flex.Automation.proofOracle (headsOnly := true)
    let solver := match result with
      | .failed failure => failure.solver
      | .solved report | .partial report => some report.solver
    let timings := match result with
      | .failed failure => failure.timings
      | .solved report | .partial report => report.timings
    let mut diagnostics := [("stage_timings", toJson (timings.map fun timing =>
      Json.mkObj [("stage", toJson (reprStr timing.stage)),
        ("elapsed_ns", toJson timing.elapsedNs)]))]
    if let some solver := solver then
      IO.FS.writeFile (ctx.output / s!"{label}-{i}.stdout") solver.process.stdout
      IO.FS.writeFile (ctx.output / s!"{label}-{i}.stderr") solver.process.stderr
      let status := match solver.outcome with
        | .sat _ => "sat" | .unsat => "unsat" | .unknown _ => "unknown"
        | .timedOut => "timeout" | .error _ => "error"
      diagnostics := diagnostics ++ [("solver_status", toJson status),
        ("solver_ms", toJson solver.process.elapsedMs)]
    match result with
    | .failed failure =>
      emit ctx (label ++ "_candidate") "failed" (diagnostics ++ [
        ("stage", toJson (reprStr failure.stage)), ("error", toJson failure.message),
        ("relations", toJson failure.relations), ("clauses", toJson failure.clauses)])
      throwError failure.message
    | .solved report | .partial report =>
      remainingHeads.modify fun total => do
        return (← total) + (← report.certificate.remainingHeads)
      provedHeads.modify (· + report.certificate.provedHeads)
      IO.FS.writeFile (ctx.output / s!"{label}-{i}.smt2") report.problem.toSMTLib
      let witnesses ← report.witnesses.toList.mapM fun witness => do
        return s!"{witness.symbol} := {(← ppExpr witness.value).pretty}"
      IO.FS.writeFile (ctx.output / s!"{label}-{i}-invariants.txt")
        (String.intercalate "\n" witnesses)
      emit ctx (label ++ "_candidate") "imported" (diagnostics ++ [
        ("witnesses", toJson report.witnesses.size),
        ("proved_heads", toJson report.certificate.provedHeads),
        ("remaining_heads", toJson report.certificate.remainingHeads),
        ("head_certification_complete", toJson (report.certificate.remainingHeads.map (· == 0))),
        ("residual_vc", toJson report.certificate.residualVC.isSome)])
      setGoals report.certificate.goals.toList

private def pipeline (ctx : Context) : TacticM Unit := do
  if let some backend := soloBackend? ctx.variant then
    -- The solver gets the original VC: no Zap, no Fix. Unfold its definition so that its
    -- binders are visible even when it has no outer quantifier.
    replaceMainGoal [← (← getMainGoal).deltaTarget (· == ctx.declaration)]
    let label := if backend == .spacer then "spacer" else "eldarica"
    let config := { backend, timeoutMs := ctx.solverMs, retrySearch := false, modelFallback := false }
    let solve := withOptions (flex.chc.encodeQuantifiers.set · (backend == .eldarica)) <|
      runSolver ctx config (← IO.mkRef (some 0)) (← IO.mkRef 0)
    if ← attempt ctx label solve then
      ctx.retainedSolver.set label
    if ctx.dischargeResidual && !(← getUnsolvedGoals).isEmpty then
      discard <| attempt ctx "discharge" discharge
    return
  discard <| attempt ctx "zap" <| onPredicates (evalTactic (← `(tactic| zap)))
  saveCheckpoint ctx
  if (← totalPredicates) > 0 then
    if ctx.variant == "zap_spacer" || ctx.variant == "zap_eldarica" then
      let backend := if ctx.variant == "zap_spacer" then Backend.spacer else Backend.eldarica
      let label := if backend == .spacer then "spacer" else "eldarica"
      let heads ← IO.mkRef (some 0)
      let proved ← IO.mkRef 0
      if ← attempt ctx label (runSolver ctx { backend, timeoutMs := ctx.solverMs } heads proved) then
        ctx.retainedSolver.set label
    else if ctx.variant == "zap_solver" then
      let entry ← Tactic.saveState
      let mut best := entry
      let mut hasBest := false
      let mut bestHeads : Option Nat := none
      let mut bestProved := 0
      for backend in #[Backend.spacer, Backend.eldarica] do
        restore entry
        let label := if backend == .spacer then "spacer" else "eldarica"
        let remainingHeads ← IO.mkRef (some 0)
        let provedHeads ← IO.mkRef 0
        if ← attempt ctx label
            (runSolver ctx { backend, timeoutMs := ctx.solverMs } remainingHeads provedHeads) then
          if ctx.dischargeResidual then
            discard <| attempt ctx (label ++ "_discharge") discharge
          let heads ← remainingHeads.get
          let proved ← provedHeads.get
          let fullyProved := (← getUnsolvedGoals).isEmpty
          let better := !hasBest || fullyProved || match heads, bestHeads with
            | some _, none => true
            | some count, some previous => count < previous || (count == previous && proved > bestProved)
            | none, none => proved > bestProved
            | none, some _ => false
          if better then
            best ← Tactic.saveState
            hasBest := true
            bestHeads := heads
            bestProved := proved
            ctx.retainedSolver.set label
          if fullyProved || heads == some 0 then return
      restore best
    else discard <| attempt ctx "fix" (runFix ctx)
  if ctx.dischargeResidual && !(← getUnsolvedGoals).isEmpty then
    discard <| attempt ctx "discharge" discharge

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
        throwError "certificate does not prove original VC"
      for name in proof.getUsedConstants do
        for axiomName in ← collectAxioms name do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "certificate depends on {axiomName}"
  finally restoreTermState saved

private def runImpl (name : Name) (variant caseName : String) : TermElabM Unit := do
  unless #["zap_fix_basic", "zap_fix_standard", "zap_fix_deep", "zap_solver",
      "zap_spacer", "zap_eldarica"].contains variant || (soloBackend? variant).isSome do
    throwError "unknown RQ1 variant {variant}"
  let saved ← Term.saveState
  let start ← IO.monoMsNow
  let heartbeats ← IO.getNumHeartbeats
  let recursionLimit ← envNat "FLEX_RQ1_RECURSION_LIMIT" 16384
  let output : System.FilePath := (← IO.getEnv "FLEX_RQ1_OUTPUT").getD "/tmp/flex-rq1"
  let ctx : Context := {
    caseName, declaration := name, variant, output := output / variant
    deadline := start + (← envNat "FLEX_RQ1_CASE_SECONDS" 180) * 1000
    paSeconds := ← envNat "FLEX_RQ1_PA_SECONDS" 60
    solverMs := ← envNat "FLEX_RQ1_SOLVER_MS" 60000
    heartbeats := ← envNat "FLEX_RQ1_PHASE_HEARTBEATS" 2000000
    dischargeResidual := (← IO.getEnv "FLEX_RQ1_DISCHARGE") == some "1"
    retainedSolver := ← IO.mkRef ""
    events := ← IO.mkRef #[] }
  IO.FS.createDirAll ctx.output
  let target := Lean.mkConst name
  let initial ← countPredicates target
  publish ctx "FLEX_RQ1_START " (Json.mkObj [
    ("case", toJson caseName), ("variant", toJson variant),
    ("initial_predicates", toJson initial)])
  let remainingPredicates ← IO.mkRef initial
  let (status, error, remaining, checked) ← try
    tryCatchRuntimeEx (do
      let original ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
      let goals ← withTheReader Core.Context (fun c => { c with maxRecDepth := recursionLimit }) <|
        Tactic.run original.mvarId! do
          pipeline ctx
          remainingPredicates.set (← totalPredicates)
      let kernelStart ← IO.monoMsNow
      checkBridge original target goals.toArray
      emit ctx "kernel" "checked" [("elapsed_ms", toJson ((← IO.monoMsNow) - kernelStart))]
      let proof ← instantiateMVars original
      let proofLabel := if goals.isEmpty then "Complete proof of the original VC."
        else "Conditional proof of the original VC; remaining metavariables are listed in residual.txt."
      IO.FS.writeFile (ctx.output / "proof-term.txt")
        (proofLabel ++ "\n\n" ++ (← ppExpr proof).pretty)
      let residuals ← goals.mapM fun goal => return (← Meta.ppGoal goal).pretty
      IO.FS.writeFile (ctx.output / "residual.txt") (String.intercalate "\n\n" residuals)
      return (if goals.isEmpty then "proved" else "partial", "", goals.length, true))
      (fun error => return ("failed", ← error.toMessageData.toString, 1, false))
  finally restoreTermState saved
  let result := Json.mkObj [
    ("case", toJson caseName), ("variant", toJson variant), ("status", toJson status),
    ("initial_predicates", toJson initial), ("remaining_predicates", toJson (← remainingPredicates.get)),
    ("retained_solver", toJson (← ctx.retainedSolver.get)),
    ("residual_discharge", toJson ctx.dischargeResidual),
    ("kernel_checked", toJson checked), ("remaining_goals", toJson remaining),
    ("elapsed_ms", toJson ((← IO.monoMsNow) - start)),
    ("heartbeats", toJson (((← IO.getNumHeartbeats) - heartbeats) / 1000)),
    ("recursion_limit", toJson recursionLimit), ("peak_recursion_depth", Json.null),
    ("phases", Json.arr (← ctx.events.get)), ("error", toJson error)]
  IO.FS.writeFile (ctx.output / "result.json") result.pretty
  publish ctx "FLEX_RQ1 " result

def run (name : Name) (variant caseName : String) : TermElabM Unit := do
  let recursionLimit ← envNat "FLEX_RQ1_RECURSION_LIMIT" 16384
  withTheReader Core.Context (fun ctx =>
      { ctx with maxHeartbeats := 0, maxRecDepth := recursionLimit }) <|
    Core.withCurrHeartbeats <| runImpl name variant caseName

end RQ1Baseline
