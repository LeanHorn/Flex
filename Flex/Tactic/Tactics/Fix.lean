import Flex.Fusion
import Flex.Tactic.Utils
import Flex.PA.Fixpoint
import Flex.PA.Cert
import Flex.PA.Scrape

open Lean Elab Meta Tactic

register_option flex.reportQualifiers : Bool := {
  defValue := true
  descr := "Show scraped qualifier templates in the Infoview before predicate abstraction."
}

private def reportScrapedQualifiers (cfg : PAScrapeConfig) (qs : Array Expr) : TacticM Unit := do
  unless flex.reportQualifiers.get (← getOptions) do return
  if cfg.mode == .no && cfg.defs.isEmpty then return
  withOptions (·.setBool `pp.funBinderTypes true) do
    let header := m!"fix: scraped qualifiers ({qs.size})"
    let entries := qs.toList.mapIdx fun i q => m!"  {i + 1}. {q}"
    logInfo (MessageData.joinSep (header :: entries) "\n")

/-- Wall time includes external solver work, unlike Lean heartbeats. -/
register_option flex.benchOracles : Bool := {
  defValue := false
  descr := "Emit fix phase wall times and candidate counts for oracle benchmarks."
}

private def benchFixPhase (phase : String) (act : TacticM α) : TacticM α := do
  unless flex.benchOracles.get (← getOptions) do return ← act
  let start ← IO.monoNanosNow
  let result ← act
  let stop ← IO.monoNanosNow
  IO.println s!"FIX_PHASE {phase} ns={stop - start}"
  return result

/-- Synthesize predicates and certify their heads, leaving κ-free goals.
    Uses `proofOracle` for certification when supplied, otherwise `oracle`. -/
def paCertImpl (oracle : PAOracle := proveLeaf) (scrape : PAScrapeConfig := {})
    (proofOracle : Option PAOracle := none)
    : TacticM Unit := withMainContext do
  let (kctx, kvarsInOrder) ← peelKVars

  -- Peeling existentials changes the goal's local context.
  withMainContext do
    let bodyGoal ← getMainGoal
    -- Scrape before `reduce` erases surface predicates and unfolds definitions.
    let rawBody ← bodyGoal.getType
    let extraQualifiers ← scrapePAQualifiers rawBody scrape
    reportScrapedQualifiers scrape extraQualifiers
    let body ← reduce rawBody

    let (acyclic, _) ← (exprPartitionKVars body).run kctx
    unless acyclic.isEmpty do
      logWarning m!"pa_cert: {acyclic.length} acyclic κ(s) present \
        ({acyclic.map (·.name)}) — run `fusion` first. Treating all κ as cut."
    let flatCs  ← (exprFlat body).run kctx
    let initial ← buildInitialAssignment kvarsInOrder extraQualifiers
    let aStar ← benchFixPhase "synthesis" <| solveFixpoint kctx flatCs initial oracle
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
    logInfo m!"pa_cert: bridge built and assigned; \
      {residual.length} κ-free residual goal(s) left as c′."

syntax "pa_cert" : tactic
elab_rules : tactic
  | `(tactic| pa_cert) => paCertImpl

/-- `oracle` runs after Lean; `synth` and `proof` override it and run before Lean.
    Synthesis proofs are discarded; certificate proofs use the proof oracle. -/
syntax "fix" (atomic("(" &"scrape" ":=") ident ")")?
  (atomic("(" &"defs" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"oracle" ":=") tacticSeq ")")?
  (atomic("(" &"synth" ":=") tacticSeq ")")?
  (atomic("(" &"proof" ":=") tacticSeq ")")? : tactic

elab_rules : tactic
  | `(tactic| fix $[(scrape := $mode:ident)]? $[(defs := [$defs:ident,*])]?
      $[(oracle := $fallback:tacticSeq)]? $[(synth := $synth:tacticSeq)]?
      $[(proof := $proof:tacticSeq)]?) => do
    let mode ← match mode.map (·.getId) with
      | none | some `no => pure PAScrapeMode.no
      | some `head => pure PAScrapeMode.head
      | some `both => pure PAScrapeMode.both
      | _ => throwError "fix: scrape must be `no`, `head`, or `both`"
    let defs ← match defs with
      | none => pure #[]
      | some names => names.getElems.mapM fun name =>
        realizeGlobalConstNoOverloadWithInfo name
    let oracle ← match fallback with
      | none => pure proveLeaf
      | some tac => pure (withPAFallback (← `(tactic| ($tac:tacticSeq))))
    let synthOracle ← match synth with
      | none => pure oracle
      | some tac => pure (withPAPriority (← `(tactic| ($tac:tacticSeq))))
    let proofOracle ← match proof with
      | none => pure oracle
      | some tac => pure (withPAPriority (← `(tactic| ($tac:tacticSeq))))
    paCertImpl synthOracle { mode, defs } (some proofOracle)
    benchFixPhase "residual" do
      let remaining ← (← getGoals).filterM fun goal =>
        goal.withContext do
          match ← proofOracle (← instantiateMVars (← goal.getType)) with
          | some proof => goal.assign proof; pure false
          | none => pure true
      setGoals remaining
