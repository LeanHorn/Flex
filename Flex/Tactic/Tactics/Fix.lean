import Flex.Fusion
import Flex.Tactic.Utils
import Flex.PA.Fixpoint
import Flex.PA.Cert
import Flex.PA.Scrape
import Flex.PA.Qualifier

open Lean Elab Meta Tactic

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
    let header := m!"fix: scraped qualifiers ({qs.size})"
    let entries := qs.toList.mapIdx fun i q =>
      m!"  {i + 1}. {q} [{result.origins[i]!}]"
    logInfo (MessageData.joinSep (header :: entries) "\n")
  trace[flex.scrape] "visited={result.visitedNodes} definitions={result.inspectedDefinitions} rejected={result.rejected}"

/-- Report a phase's elapsed wall time when benchmarking is enabled. -/
private def benchFixPhase (phase : String) (act : TacticM α) : TacticM α := do
  unless flex.benchOracles.get (← getOptions) do return ← act
  let start ← IO.monoNanosNow
  let result ← act
  let stop ← IO.monoNanosNow
  IO.println s!"FIX_PHASE {phase} ns={stop - start}"
  return result

/-- Run predicate abstraction and build its certificate, leaving residual goals. -/
def fixImpl
  (oracle : PAOracle := proveLeaf)
  (scrape : PAScrapeConfig := {})
  (proofOracle : Option PAOracle := none)
  (observe : PAObserver := fun _ => pure ())
    : TacticM Unit := withMainContext do
  let (kctx, kvarsInOrder) ← peelKVars

  -- Peeling existentials changes the goal's local context.
  withMainContext do
    let bodyGoal ← getMainGoal
    -- Scrape before `reduce` erases surface predicates and unfolds definitions.
    let rawBody ← bodyGoal.getType
    let extraQualifiers ←
      if scrape.mode != .no || !scrape.defs.isEmpty then do
        let result ← scrapePAQualifiersWithReport rawBody scrape
        if flex.reportQualifiers.get (← getOptions) then
          reportScrapedQualifiers result
        unless result.limitsHit.isEmpty do
          logWarning m!"fix: scraping reached limits {result.limitsHit}; some candidates were omitted"
        pure result.qualifiers
      else pure #[]
    let body ← reduce rawBody

    let (acyclic, _) ← (exprPartitionKVars body).run kctx
    unless acyclic.isEmpty do
      logWarning m!"fix: {acyclic.length} acyclic κ(s) present \
        ({acyclic.map (·.name)}) — run `fusion` first. Treating all κ as cut."
    let flatCs  ← (exprFlat body).run kctx
    let candidateLimit := if scrape.mode == .no && scrape.defs.isEmpty then none
      else some scrape.maxCandidatesPerKappa
    let instanceLimit := candidateLimit.map fun _ => scrape.maxInstancesPerKappa
    let standardQualifiers ← getStandardQualifiers
    let qualifiers := extraQualifiers ++ standardQualifiers
    let initial ← buildInitialAssignment kvarsInOrder qualifiers candidateLimit instanceLimit
    observe (.setup extraQualifiers.size standardQualifiers.size (← getQualifiers).size
      (initial.toArray.map fun (κ, cs) => (κ.name, cs.length)))
    let aStar ← benchFixPhase "synthesis" <| solveFixpoint kctx flatCs initial oracle observe
    if flex.benchOracles.get (← getOptions) then
      let count := fun (a : List (KVar × List (Expr × List Nat))) =>
        a.foldl (fun n (_, qs) => n + qs.length) 0
      IO.println s!"FIX_CANDIDATES initial={count initial} surviving={count aStar}"

    -- Keep `body` uninstantiated so `walkPAProof` can recognize κ-heads.
    let sols ← finalizeSolutions aStar
    for (κ, sol) in sols do
      κ.assignSol sol

    let residualOut ← IO.mkRef (#[] : Array MVarId)
    let proof ← benchFixPhase "certificate" <|
      walkPAProof aStar body residualOut (proofOracle.getD oracle)
    bodyGoal.assign proof

    let residual := (← residualOut.get).toList
    setGoals residual
    logInfo m!"fix: bridge built and assigned; \
      {residual.length} κ-free residual goal(s) left as c′."

private declare_config_elab elabScrapeLimits PAScrapeLimits

/-- Solve existential predicates by PA, leaving any unproved residual goals.
    Uses the standard qualifier bank unless `flex.standardQualifiers` is disabled.
    `scrape`: `basic` extracts heads; `standard` adds premises and definition discovery;
    `deep` also explores helpers and generalizes numeric templates.
    `defs`: also scrape the listed definitions. Scraping is off by default.
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
    let mode ← match mode.map (·.getId) with
      | none | some `no => pure PAScrapeMode.no
      | some `basic => pure PAScrapeMode.basic
      | some `standard => pure PAScrapeMode.standard
      | some `deep => pure PAScrapeMode.deep
      | _ => throwError "fix: scrape must be `no`, `basic`, `standard`, or `deep`"
    let defs ← match defs with
      | none => pure #[]
      | some names => names.getElems.mapM fun name =>
        realizeGlobalConstNoOverloadWithInfo name

    let limits ← match limits with
      | none => pure ({} : PAScrapeLimits)
      | some value => do
        let stx ← `(Lean.Parser.Term.optConfig| (config := $value))
        elabScrapeLimits stx (logExceptions := false)

    -- Each phase inherits the shared oracle unless explicitly overridden.
    let defaultOracle ← match fallback with
      | none => pure proveLeaf
      | some tac => pure (withPAFallback (← `(tactic| ($tac:tacticSeq))))
    let synthOracle ← match synth with
      | none => pure defaultOracle
      | some tac => pure (withPAPriority (← `(tactic| ($tac:tacticSeq))))
    let proofOracle ← match proof with
      | none => pure defaultOracle
      | some tac => pure (withPAPriority (← `(tactic| ($tac:tacticSeq))))
    fixImpl synthOracle { limits with mode, defs } (some proofOracle)

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
