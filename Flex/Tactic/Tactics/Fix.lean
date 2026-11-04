import Flex.Fusion
import Flex.Tactic.Utils
import Flex.PA.Fixpoint
import Flex.PA.Cert
import Flex.PA.Scrape
import Flex.PA.Qualifier
import Flex.Tactic.Automation
import Flex.Tactic.Timeout

open Lean Elab Meta Tactic

register_option flex.fixpointTimeout : Nat := {
  defValue := 60
  descr := "Shared seconds for PA preparation, all synthesis stages and safety validation; zero disables this deadline."
}

register_option flex.reportQualifiers : Bool := {
  defValue  := false
  descr     := "Show scraped qualifier templates in the Infoview before predicate abstraction."
}

/-- Wall time includes external solver work, unlike Lean heartbeats. -/
register_option flex.benchOracles : Bool := {
  defValue  := false
  descr     :=
    "Emit fix phase wall times and candidate counts for oracle benchmarks."
}

/-- Report scraped qualifiers. -/
private def reportScrapedQualifiers (result : PAScrapeResult) : TacticM Unit := do
  let qs := result.qualifiers
  withOptions (·.setBool `pp.funBinderTypes true) do
    let header := m!"fix: scraped qualifiers ({qs.size} templates, {result.anchored.size} source instances)"
    let entries := qs.toList.mapIdx fun i q =>
      m!"  {i + 1}. {q} [{result.origins[i]!}]"
    let instances := result.anchored.toList.map fun candidate =>
      m!"  {candidate.qualifier} [{candidate.origin}; slots {candidate.slots}]"
    logInfo (MessageData.joinSep (header :: entries ++ instances) "\n")
  trace[flex.scrape] "visited={result.visitedNodes} definitions={result.inspectedDefinitions} rejected={result.rejected}"

/-- Report a phase's elapsed wall time when benchmarking is enabled. -/
private def benchFixPhase (phase : String) (act : TacticM α) : TacticM α := do
  unless flex.benchOracles.get (← getOptions) do return ← act
  let start ← IO.monoNanosNow
  IO.println s!"FIX_PHASE_START {phase}"
  let completed ← IO.mkRef false
  try
    let result ← act
    completed.set true
    return result
  finally
    IO.println s!"FIX_PHASE {phase} ns={(← IO.monoNanosNow) - start} completed={← completed.get}"

/-- Require a valid safety check; inconclusive checks may fall back to a Lean proof. -/
private def validatePASafety (synth : PASynthOracle) (prove : PAOracle) : PAOracle :=
  fun target => do
    let results ← synth #[target]
    unless results.size == 1 do
      throwError "fix: safety oracle returned the wrong number of decisions"
    match results[0]! with
    | .valid => return none
    | .invalid =>
      throwError "fix: synthesized predicates do not satisfy a safety clause; goal unchanged"
    | .unknown _ =>
      if let some proof ← prove target then return some proof
      throwError "fix: could not validate a safety clause for the synthesized predicates; goal unchanged"

/-- Reuse safety decisions and fallback proofs when the certificate revisits a clause. -/
private def cachedPASafety (oracle : PAOracle) : TermElabM PAOracle := do
  let fixed := FVarIdSet.ofArray (← getLCtx).getFVarIds
  let cache ← IO.mkRef (#[] : Array (Expr × Option Expr))
  return fun target => do
    let locals := (← getLCtx).getFVars.filter fun x => !fixed.contains x.fvarId!
    let key ← mkForallFVars locals target
    if let some (_, proof) := (← cache.get).find? (·.1 == key) then
      return proof.map (fun p => (mkAppN p locals).headBeta)
    let proof ← oracle target
    let closed ← proof.mapM (mkLambdaFVars locals ·)
    cache.modify (·.push (key, closed))
    return proof

private def scrapeForFix (body : Expr) (cfg : PAScrapeConfig) : TacticM PAScrapeResult := do
  if cfg.mode == .no && cfg.defs.isEmpty then return {}
  let result ← benchFixPhase "scrape" <| scrapePAQualifiersWithReport body cfg
  if flex.benchOracles.get (← getOptions) then
    let stats := Json.mkObj [
      ("templates", toJson result.qualifiers.size),
      ("anchored", toJson result.anchored.size),
      ("nodes", toJson result.visitedNodes),
      ("definitions", toJson result.inspectedDefinitions),
      ("rejected", toJson result.rejected),
      ("limits_hit", toJson result.limitsHit),
      ("template_origins", toJson result.origins),
      ("anchored_origins", toJson (result.anchored.map (·.origin)))]
    IO.println s!"FIX_SCRAPE {stats.compress}"
  if flex.reportQualifiers.get (← getOptions) then reportScrapedQualifiers result
  unless result.limitsHit.isEmpty do
    logWarning m!"fix: scraping reached limits {result.limitsHit}; some candidates were omitted"
  return result

/-- Validation decisions describe candidate suitability, not completed Lean proofs.
Only completed certification traversals report; rejected candidates roll back. -/
structure PACertificationReport where
  /-- Predicate heads proved or independently validated in their local context. -/
  validatedHeads : Nat := 0
  /-- Validated heads retained as explicit Lean proof obligations. -/
  remainingHeads : Nat := 0
  validatedSafety : Nat := 0
  /-- All predicate-dependent obligations were proved or validated. -/
  allValidated : Bool := true
  deriving Inhabited, Repr

/-- Prefer properties of the current state before properties of compound updated values. -/
private def directSourceCandidate (candidate : PAAnchoredQualifier) : MetaM Bool :=
  lambdaTelescope candidate.qualifier fun _ body => do
    if candidate.origin == "stateful completion" then return true
    if ← forallTelescopeReducing body fun _ tail => pure (tail.isConstOf ``True) then
      return false
    for arg in body.getAppArgs do
      if !arg.hasFVar || arg.isFVar then continue
      let type ← whnf (← inferType arg)
      if type.isSort || type.isProp || type.isConstOf ``Int || type.isConstOf ``Nat ||
          type.isConstOf ``Bool then continue
      return false
    return true

private structure PASolution where
  goal : MVarId
  body : Expr
  assignment : List (KVar × List (Expr × List Nat))
  safety : PAOracle

private def searchFix
  (oracle : PAOracle := proveLeaf)
  (scrape : PAScrapeConfig := { mode := .auto })
  (proofOracle : Option PAOracle := none)
  (observe : PAObserver := fun _ => pure ())
  (synthOracle : Option PASynthOracle := none)
  (directSources : Bool := false)
    : TacticM PASolution := withMainContext do
  let (kctx, kvarsInOrder) ← peelKVars

  -- Peeling existentials changes the goal's local context.
  withMainContext do
    let bodyGoal ← getMainGoal
    -- Scrape the original surface predicates before exposing constraint wrappers.
    let rawBody ← bodyGoal.getType
    -- Expose constraint wrappers, keeping κ-free semantic predicates intact.
    let body ← Meta.transform rawBody (pre := fun e => do
      if !e.hasExprMVar then return .done e
      if e.getAppFn.isMVar then return .continue
      let exposed ← whnf e
      return if exposed == e then .continue else .visit exposed)

    let (elimVars, _) ← benchFixPhase "partition" <| (exprPartitionKVars body).run kctx
    unless elimVars.isEmpty do
      logWarning m!"fix: {elimVars.length} non-cut κ(s) present \
        ({elimVars.map (·.name)}) — run `zap` first. Treating all κ as cut."
    let flatCs  ← (exprFlat body pure).run kctx
    let standardQualifiers ← getStandardQualifiers
    let modes := if scrape.mode == .auto then
      #[PAScrapeMode.no, .basic, .standard, .deep] else #[scrape.mode]
    let mut initial := []
    let mut seen : ExprSet := {}
    let mut selected := none
    let mut lastError := m!"fix: no suitable predicate assignment"
    for index in [:modes.size] do
      Core.checkInterrupted
      let mode := modes[index]!
      observe (.stageStarted mode)
      let cfg := { scrape with
        mode := mode
        defs := if scrape.mode == .auto && mode == .no then #[] else scrape.defs }
      let scraped ← scrapeForFix rawBody cfg
      let ordinaryCount := scraped.qualifiers.size - scraped.observationCount
      let qualifiers := if directSources then standardQualifiers else
        scraped.qualifiers.extract 0 ordinaryCount ++ standardQualifiers ++
          scraped.qualifiers.extract ordinaryCount scraped.qualifiers.size
      let mut fresh := #[]
      for q in qualifiers do
        unless seen.contains q do
          seen := seen.insert q
          fresh := fresh.push q
      let anchored ← if directSources then
          scraped.anchored.filterM (fun q => liftM (directSourceCandidate q))
        else pure scraped.anchored
      let candidateLimit := if scrape.mode == .no && scrape.defs.isEmpty then none
        else some scrape.maxCandidatesPerKappa
      let previous := initial
      initial ← benchFixPhase "candidates" <|
        buildInitialAssignment kvarsInOrder fresh candidateLimit
          (candidateLimit.map fun _ => scrape.maxInstancesPerKappa) anchored
          (previous := initial) (includeTagged := index == 0)
      observe (.setup scraped.qualifiers.size standardQualifiers.size (← getQualifiers).size
        (initial.toArray.map fun (κ, cs) => (κ.name, cs.length)))
      if index > 0 && initial == previous then
        observe (.stageFinished mode false)
        trace[flex.scrape] "{mode}: no new candidates"
        continue
      let saved ← Tactic.saveState
      let attempt ← tryCatchRuntimeEx (do
        let aStar ← benchFixPhase "synthesis" <|
          solveFixpoint kctx flatCs initial oracle observe synthOracle
        if flex.benchOracles.get (← getOptions) then
          let count := fun (a : List (KVar × List (Expr × List Nat))) =>
            a.foldl (fun n (_, qs) => n + qs.length) 0
          IO.println s!"FIX_CANDIDATES initial={count initial} surviving={count aStar}"
        -- Keep `body` uninstantiated so validation and certification recognize heads.
        for (κ, sol) in ← finalizeSolutions aStar do κ.assignSol sol
        let safety ← cachedPASafety <| validatePASafety (synthOracle.getD oracle.toSynth)
          (proofOracle.getD oracle)
        benchFixPhase "safety" <| checkPASafety aStar body safety
        return Except.ok (aStar, safety)) (fun error => do
          Flex.CHC.restoreTermState saved.term
          set saved.tactic
          if error.isInterrupt then throw error
          Core.checkInterrupted
          return .error error.toMessageData)
      match attempt with
      | .ok result =>
        observe (.stageFinished mode true)
        selected := some result
        break
      | .error error =>
        observe (.stageFinished mode false)
        trace[flex.scrape] "{mode}: {error}"
        lastError := error
    let some (aStar, checkedSafety) := selected | throwError lastError
    return { goal := bodyGoal, body, assignment := aStar, safety := checkedSafety }

private def runFix (oracle : PAOracle) (scrape : PAScrapeConfig)
    (proofOracle : Option PAOracle) (observe : PAObserver)
    (synthOracle : Option PASynthOracle) (allowUnprovedHeads : Bool)
    (onCertification : PACertificationReport → TacticM Unit)
    (directSources : Bool) : TacticM Unit := do
  let seconds := flex.fixpointTimeout.get (← getOptions)
  let deadline ← if seconds == 0 then pure none else
    pure (some ((← IO.monoMsNow) + seconds * 1000))
  let some result ← Flex.Timeout.run deadline <|
      searchFix oracle scrape proofOracle observe synthOracle directSources
    | throwError "fix: shared synthesis budget exhausted ({seconds}s); goal unchanged"
  withMainContext do
    let { goal := bodyGoal, body, assignment := aStar, safety := checkedSafety } := result

    let residualOut ← IO.mkRef (#[] : Array MVarId)
    let certification ← IO.mkRef ({} : PACertificationReport)
    let certificateCalls ← IO.mkRef 0
    let certify : PAOracle := fun target => do
      certificateCalls.modify (· + 1)
      (proofOracle.getD oracle) target
    let validateSafety : PAOracle := fun target => do
      let proof ← checkedSafety target
      certification.modify fun r => { r with validatedSafety := r.validatedSafety + 1 }
      return proof
    let unprovedHead : Option (Expr → TermElabM Expr) :=
      if allowUnprovedHeads then
        some fun target => do
          let target ← instantiateMVars target
          let results ← (synthOracle.getD oracle.toSynth) #[target]
          unless results.size == 1 do
            throwError "fix: head validation oracle returned the wrong number of decisions"
          match results[0]! with
          | .valid =>
            let residual ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
            residualOut.modify (·.push residual.mvarId!)
            certification.modify fun r => { r with remainingHeads := r.remainingHeads + 1 }
            return residual
          | .invalid =>
            throwError "fix: synthesized predicates do not satisfy a head clause; goal unchanged"
          | .unknown _ =>
            throwError "fix: could not validate an unproved predicate head; goal unchanged"
      else none
    let onHead : TermElabM Unit :=
      certification.modify fun r => { r with validatedHeads := r.validatedHeads + 1 }
    let proof ← benchFixPhase "certificate" <|
      walkPAProof aStar body residualOut certify validateSafety
        (unprovedHead := unprovedHead) (onHead := onHead)
    bodyGoal.assign proof
    if flex.benchOracles.get (← getOptions) then
      IO.println s!"FIX_CERTIFICATE calls={← certificateCalls.get}"

    let residual := (← residualOut.get).toList
    setGoals residual
    logInfo m!"fix: bridge built and assigned; \
      {residual.length} residual proof goal(s) left as c′."
    onCertification (← certification.get)

/-- Keep predicate assignments only after head certification and safety validation.
With `allowUnprovedHeads`, independently valid head clauses may remain as explicit
proof goals. Unknown or refuted heads reject the candidate. Validation decisions
never enter the proof term. Any failure restores the entry goal. -/
def fixImpl
  (oracle : PAOracle := proveLeaf)
  (scrape : PAScrapeConfig := { mode := .auto })
  (proofOracle : Option PAOracle := none)
  (observe : PAObserver := fun _ => pure ())
  (synthOracle : Option PASynthOracle := none)
  (allowUnprovedHeads : Bool := false)
  (onCertification : PACertificationReport → TacticM Unit := fun _ => pure ())
  (directSources : Bool := false) : TacticM Unit := do
  let saved ← Tactic.saveState
  tryCatchRuntimeEx
      (runFix oracle scrape proofOracle observe synthOracle allowUnprovedHeads onCertification directSources)
      (fun error => do
    Flex.CHC.restoreTermState saved.term
    set saved.tactic
    throw error)

private declare_config_elab elabScrapeLimits PAScrapeLimits

/-- Parse a `scrape := …` mode; `tactic` names the caller in the error. -/
def parseScrapeMode (tactic : String) : Option Ident → TacticM PAScrapeMode
  | none => pure .auto
  | some mode => match mode.getId.eraseMacroScopes with
    | `no => pure .no
    | `basic => pure .basic
    | `standard => pure .standard
    | `deep => pure .deep
    | `auto => pure .auto
    | _ => throwErrorAt mode "{tactic}: scrape must be `auto`, `no`, `basic`, `standard`, or `deep`"

/-- Solve existential predicates by PA, retaining only safety-validated candidates.
    Rejected or inconclusive candidates leave the entry goal unchanged.
    Validated candidates may leave unproved residual goals.
    Uses the standard qualifier bank unless `flex.standardQualifiers` is disabled.
    Default synthesis batches SMT decisions; certification and residual goals use
    kernel-checked SMT proofs and Lean automation.
    `scrape`: `auto` grows the bank through Basic, Standard, and Deep until validated;
    explicit levels run once. `basic` extracts heads; `standard` adds premises, guarded arithmetic,
    definitions, and relations between semantic observations;
    `deep` also explores helpers and generalizes numeric templates.
    `defs`: also scrape the listed definitions. Automatic escalation is the default.
    All synthesis stages share `flex.fixpointTimeout` (60 seconds).
    `oracle`: fallback after default Lean automation, shared by both phases.
    `synth` / `proof`: override that phase with a tactic tried before Lean.
    Only proof-phase evidence enters the certificate. -/
syntax "fix" (atomic("(" &"scrape" ":=") ident ")")?
  (atomic("(" &"defs" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"scrapeConfig" ":=") term ")")?
  (atomic("(" &"oracle" ":=") tacticSeq ")")?
  (atomic("(" &"synth" ":=") tacticSeq ")")?
  (atomic("(" &"proof" ":=") tacticSeq ")")? : tactic

elab_rules : tactic
  | `(tactic| fix $[(scrape := $mode:ident)]? $[(defs := [$defs:ident,*])]?
      $[(scrapeConfig := $limits:term)]? $[(oracle := $fallback:tacticSeq)]? $[(synth := $synth:tacticSeq)]?
      $[(proof := $proof:tacticSeq)]?) => do
    -- Parse scraping options and resolve definition names.
    let mode ← parseScrapeMode "fix" mode
    let defs ← match defs with
      | none => pure #[]
      | some names => names.getElems.mapM fun name =>
        realizeGlobalConstNoOverloadWithInfo name

    let limits ← match limits with
      | none => pure ({} : PAScrapeLimits)
      | some value => do
        let stx ← `(Lean.Parser.Term.optConfig| (config := $value))
        elabScrapeLimits stx (logExceptions := false)

    -- Preserve explicit oracle overrides; the default proof phase uses checked automation.
    let defaultOracle ← match fallback with
      | none => pure proveLeaf
      | some tac => pure (withPAFallback (← `(tactic| ($tac:tacticSeq))))
    let synthOracle ← match synth with
      | none => pure defaultOracle
      | some tac => pure (withPAPriority (← `(tactic| ($tac:tacticSeq))))
    let proofOracle ← match proof with
      | none => pure (if fallback.isSome then defaultOracle else Flex.Automation.proofOracle)
      | some tac => pure (withPAPriority (← `(tactic| ($tac:tacticSeq))))
    let batchOracle := if synth.isNone && fallback.isNone then
      some Flex.Automation.synthOracle else none
    fixImpl synthOracle { limits with mode, defs } (some proofOracle)
      (synthOracle := batchOracle)

    -- Use the proof oracle on residual goals; keep those it cannot close.
    benchFixPhase "residual" do
      let remaining ← (← getGoals).filterM fun goal =>
        goal.withContext do
          match ← proofOracle (← instantiateMVars (← goal.getType)) with
          | some proof =>
            goal.assign proof
            pure false
          | none => pure true
      setGoals remaining
