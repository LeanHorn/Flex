import Lean
import Aesop

import Flex.Core
import Flex.Fusion
import Flex.Tactic.Utils
import Flex.PA.Fixpoint
import Flex.PA.Cert
import Flex.PA.Scrape

open Lean Elab Meta Tactic

/-- Wall time includes external solver work, unlike Lean heartbeats. -/
register_option flex.benchOracles : Bool := {
  defValue := false
  descr := "Emit fix phase wall times and candidate counts for oracle benchmarks."
}

private def benchFixPhase {m : Type → Type} {α : Type}
    [Monad m] [MonadLiftT IO m] [MonadOptions m]
    (phase : String) (act : m α) : m α := do
  if flex.benchOracles.get (← getOptions) then
    let start ← (IO.monoNanosNow : IO Nat)
    let result ← act
    let stop ← (IO.monoNanosNow : IO Nat)
    (IO.println s!"FIX_PHASE {phase} ns={stop - start}" : IO Unit)
    return result
  else act

/-!
  ## `pa_cert` — certifying Predicate Abstraction (paper §5)

  Cut-only certifier. Given `∃κ̄. c` whose ∃-bound κ's are all solved by
  predicate abstraction (e.g. `cyc0`, `FibFibFast` — the post-Zap residual),
  `pa_cert`:

  1. peels the ∃-chain into κ-mvars (`Exists.intro` scaffolding);
  2. runs the weakening fixpoint to `A*` (reused PA pipeline);
  3. assigns each κ-mvar its witness λ `σ_{A*}(κ)`;
  4. emits the §5 `glue`/`bridge` proof of the body via `walkPAProof`, where
     every κ-head leaf is discharged by an `And.intro` over per-survivor oracle
     proofs and every κ-free leaf becomes a residual goal `c′`.

  Unlike `solve_fixpoint`, the κ-heads are certified by structured proof terms
  the kernel re-checks (not thrown wholesale at `grind`), and the residual `c′`
  is LEFT as user goals rather than auto-closed. A non-cut (acyclic) κ-head
  aborts with a hint to run `fusion` first.
-/
def paCertImpl (oracle : PAOracle := proveLeaf) (scrape : PAScrapeConfig := {})
    (proofOracle : Option PAOracle := none)
    : TacticM Unit := withMainContext do
  let (kctx, kvarsInOrder) ← peelKVars

  -- Refresh the LCtx after `peelExistentialsAndIntro` mutated the main goal.
  withMainContext do
    let bodyGoal ← getMainGoal
    -- Scrape before `reduce` erases surface predicates and unfolds definitions.
    let rawBody ← bodyGoal.getType
    let extraQualifiers ← scrapePAQualifiers rawBody scrape
    let body ← reduce rawBody

    -- Cut-only: every ∃-bound κ is solved by PA. Warn (don't fail) if an
    -- acyclic κ leaked in — it would want a fusion solution, not a qualifier
    -- conjunction, and likely leaves an unprovable residual.
    let (acyclic, _cyclic) ← (exprPartitionKVars body).run kctx
    unless acyclic.isEmpty do
      logWarning m!"pa_cert: {acyclic.length} acyclic κ(s) present \
        ({acyclic.map (·.name)}) — run `fusion` first. Treating all κ as cut."
    let paSet := kvarsInOrder

    -- Weakening fixpoint A* (reused PA pipeline, identical to `solve_fixpoint`).
    let flatCs  ← (exprFlat body).run kctx
    let initial ← buildInitialAssignment paSet extraQualifiers
    let aStar ← benchFixPhase "synthesis" <| solveFixpoint kctx flatCs initial oracle
    if flex.benchOracles.get (← getOptions) then
      let count := fun (a : List (KVar × List (Expr × List Nat))) =>
        a.foldl (fun n (_, qs) => n + qs.length) 0
      IO.println s!"FIX_CANDIDATES initial={count initial} surviving={count aStar}"

    -- Assign each cut κ-mvar its witness λ `σ_{A*}(κ)`. After this, `body`'s
    -- κ-mvars instantiate to their solutions at kernel-check time, but `body`
    -- stays SYNTACTICALLY κ-headed so `walkPAProof` can still detect the heads.
    let sols ← finalizeSolutions aStar
    for (κ, sol) in sols do
      κ.assignSol sol

    -- Emit the §5 bridge proof of the body; collect κ-free residuals = c′.
    let residualOut ← IO.mkRef (#[] : Array MVarId)
    let proof ← benchFixPhase "certificate" <|
      walkPAProof aStar body residualOut (proofOracle.getD oracle)
    bodyGoal.assign proof

    -- Leave c′ as user goals (purist §5: the certified bridge is built; the
    -- κ-free residual queries remain for the user / a follow-up tactic).
    let residual := (← residualOut.get).toList
    setGoals residual
    logInfo m!"pa_cert: bridge built and assigned; \
      {residual.length} κ-free residual goal(s) left as c′."

syntax "pa_cert" : tactic
elab_rules : tactic
  | `(tactic| pa_cert) => paCertImpl

/-- `oracle` preserves the legacy Lean-first fallback for every phase.
    `synth` and `proof` independently override it with an external-first oracle
    for weakening and proof construction respectively. Each falls back to Lean.
    Evidence from synthesis is discarded; only the proof oracle enters the
    resulting certificate. External tactics require their package imports. -/
syntax "fix" (atomic("(" &"scrape" ":=") ident ")")?
  (atomic("(" &"defs" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"oracle" ":=") tacticSeq ")")?
  (atomic("(" &"synth" ":=") tacticSeq ")")?
  (atomic("(" &"proof" ":=") tacticSeq ")")?
  (atomic("(" &"trust" ":=") ident ")")? : tactic

elab_rules : tactic
  | `(tactic| fix $[(scrape := $mode:ident)]? $[(defs := [$defs:ident,*])]?
      $[(oracle := $fallback:tacticSeq)]? $[(synth := $synth:tacticSeq)]?
      $[(proof := $proof:tacticSeq)]? $[(trust := $trust:ident)]?) => do
    let mode ← match mode.map (·.getId) with
      | none | some `no => pure PAScrapeMode.no
      | some `head => pure PAScrapeMode.head
      | some `both => pure PAScrapeMode.both
      | _ => throwError "fix: scrape must be `no`, `head`, or `both`"
    let trust ← match trust.map (·.getId) with
      | none | some `false => pure false
      | some `true => pure true
      | _ => throwError "fix: trust must be `true` or `false`"
    let defs ← match defs with
      | none => pure #[]
      | some names => names.getElems.mapM fun name =>
        realizeGlobalConstNoOverloadWithInfo name
    if trust && fallback.isNone && synth.isNone && proof.isNone then
      throwError "fix: `trust := true` requires an explicit oracle"
    let oracle ← match fallback with
      | none => pure proveLeaf
      | some tac => pure (withPAFallback (← `(tactic| ($tac:tacticSeq))) trust)
    let synthOracle ← match synth with
      | none => pure oracle
      | some tac => pure (withPAPriority (← `(tactic| ($tac:tacticSeq))) trust)
    let proofOracle ← match proof with
      | none => pure oracle
      | some tac => pure (withPAPriority (← `(tactic| ($tac:tacticSeq))) trust)
    paCertImpl synthOracle { mode, defs } (some proofOracle)
    benchFixPhase "residual" do
      let mut remaining := []
      for goal in ← getGoals do
        let closed ← goal.withContext do
          match ← proofOracle (← instantiateMVars (← goal.getType)) with
          | some proof => goal.assign proof; pure true
          | none => pure false
        unless closed do remaining := remaining ++ [goal]
      setGoals remaining
