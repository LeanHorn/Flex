import Flex.Tactic.Tactics.ZapWith
import Flex.Tactic.Tactics.Fix
import Flex.Tactic.Tactics.Eldarica
import Flex.Preprocess.Cleanup
import Flex.Preprocess.Nesting
import Flex.Tactic.Residual
import Flex.Tactic.Timeout

open Lean Meta Elab Tactic

namespace Flex.Portfolio

initialize registerTraceClass `flex
initialize registerTraceClass `flex.timing

structure PhaseEvent where
  phase : String
  status : String
  elapsedMs : Nat := 0
  budgetMs : Option Nat := none
  deadlineMs : Option Nat := none

inductive Backend where
  | fix | spacer | eldarica
  deriving BEq, Repr

instance : ToString Backend where
  toString
    | .fix => "fix"
    | .spacer => "spacer"
    | .eldarica => "eldarica"

def Backend.all : List Backend := [.fix, .spacer, .eldarica]

/-- How Zap proves predicate heads; all choices use the same strongest solutions. -/
inductive ZapCertificate where
  | constructive | grind | aesop
  deriving BEq, Repr

/-- Pipeline switches, heartbeat limits, and a shared deadline in seconds. -/
structure Config where
  preprocess : Bool := true
  nesting : Bool := false
  zap : Bool := true
  /-- Try CHC backends before Zap and Fix, retaining any accepted invariants. -/
  chcFirst : Bool := false
  /-- Cap the Zap/Fix and CHC stages in either order; zero uses only the shared deadline. -/
  stageTimeout : Nat := 0
  /-- Separate Zap from Fix and cap its preparation/elimination stage in seconds.
  Zero keeps the existing stage allocation. -/
  zapTimeout : Nat := 0
  /-- Cap the separate Fix stage, including escalation, certification, and discharge.
  Zero keeps the existing stage allocation. Both caps remain within `totalTimeout`. -/
  paTimeout : Nat := 0
  zapCertificate : ZapCertificate := .constructive
  /-- Simplify equality-bound witnesses once after Zap; disabled by default. -/
  postprocess : Bool := false
  closeLeaves : Bool := true
  /-- Separate κ-free clauses before synthesis; disabled by default. -/
  splitFree : Bool := false
  /-- Expose unvalidated solver candidates for manual exploration. Refuted ones are rejected. -/
  keepCandidates : Bool := false
  report : Bool := false
  /-- Optional common override; zero uses the individual phase limits. -/
  heartbeats : Nat := 0
  preprocessHeartbeats : Nat := 2000000
  zapHeartbeats : Nat := 200000
  paHeartbeats : Nat := 1500000
  solverHeartbeats : Nat := 500000
  dischargeHeartbeats : Nat := 500000
  /-- Shared wall-clock budget for the whole tactic; zero disables the deadline. -/
  totalTimeout : Nat := 60
  /-- Maximum seconds for one CHC solver, within the shared deadline. Zero removes this cap. -/
  solverTimeout : Nat := 30
  scrapeLimits : PAScrapeLimits := {}

structure Setup where
  config : Config := {}
  backends : List Backend := Backend.all
  scrape : PAScrapeConfig := { mode := .auto }
  synth : Option (TSyntax `tactic) := none
  proof : Option (TSyntax `tactic) := none
  closer : Option (TSyntax `tactic) := none
  /-- Optional live timing events, including interrupted phases. -/
  onPhase : PhaseEvent → IO Unit := fun _ => pure ()
  /-- Observe PA candidate counts and weakening rounds, including speculative attempts. -/
  onPA : PAObserver := fun _ => pure ()
  /-- Observe CHC artifacts independently of candidate acceptance and proof search. -/
  onCHC : Backend → Flex.CHC.Event → TermElabM Unit := fun _ _ => pure ()
  /-- Observe a candidate in the state being saved; later alternatives may replace it. -/
  onSynthesis : MVarId → Backend → Bool → Option Nat → Array MVarId → TermElabM Unit :=
    fun _ _ _ _ _ => pure ()
  /-- Remaining head obligations after a successful Zap reduction. -/
  onZap : Array MVarId → TacticM Unit := fun _ => pure ()

private structure Context where
  setup : Setup
  deadline : Option Nat
  reserve : Nat
  checkpoint : IO.Ref Tactic.SavedState

private def restore (saved : Tactic.SavedState) : TacticM Unit := do
  let traces ← getTraceState
  Flex.CHC.restoreTermState saved.term
  set saved.tactic
  modifyTraceState fun _ => traces

/-- Speculation restores assignments, helper declarations, goals, and messages. -/
private def guarded (act : TacticM α) (quiet : Bool := true) : TacticM (Except MessageData α) := do
  let saved ← Tactic.saveState
  let messages ← Core.getMessageLog
  try
    tryCatchRuntimeEx (.ok <$> act) fun error => do
      restore saved
      if error.isInterrupt then throw error
      Core.checkInterrupted
      return .error error.toMessageData
  finally
    if quiet then Core.setMessageLog messages

private def withBudget (ctx : Context) (heartbeats : Nat) (act : TacticM α) : TacticM α := do
  let configured := if ctx.setup.config.heartbeats == 0 then heartbeats
    else ctx.setup.config.heartbeats
  let mut limit := configured * 1000
  if (← getMaxHeartbeats) != 0 then
    let remaining ← getRemainingHeartbeats
    if remaining <= ctx.reserve then throwError "flex: heartbeat budget exhausted"
    let available := remaining - ctx.reserve
    limit := if limit == 0 then available else min limit available
  withTheReader Core.Context (fun context => { context with maxHeartbeats := limit }) <|
    Core.withCurrHeartbeats act

private def phase (ctx : Context) (name : String) (heartbeats : Nat)
    (act : TacticM α) : TacticM (Except MessageData α) := do
  let start ← IO.monoMsNow
  ctx.setup.onPhase { phase := name, status := "start" }
  let status ← IO.mkRef "interrupted"
  try
    let result ← guarded <| withBudget ctx heartbeats do
      Flex.Timeout.checkDeadline
      act
    status.set (match result with | .ok _ => "ok" | .error _ => "failed")
    if let .error message := result then trace[flex] "{name}: {message}"
    return result
  finally
    let elapsedMs := (← IO.monoMsNow) - start
    ctx.setup.onPhase { phase := name, status := ← status.get, elapsedMs }

/-- Save the full frontier, including siblings hidden by the current local operation. -/
private def checkpoint (ctx : Context) (siblings : List MVarId) : TacticM Unit := do
  let active ← getUnsolvedGoals
  setGoals (active ++ siblings)
  ctx.checkpoint.set (← Tactic.saveState)
  setGoals active

private def isKGoal (goal : MVarId) : MetaM Bool := goal.withContext do
  let type ← whnf (← instantiateMVars (← goal.getType))
  let .app (.app (.const ``Exists _) domain) _ := type | return false
  forallTelescopeReducing domain fun _ body => return body.isProp

private def isTrueProp (e : Expr) : Bool := e.isConstOf ``True

private def mkAndOpt (a b : Expr) : Expr :=
  if isTrueProp a then b else if isTrueProp b then a else mkApp2 (mkConst ``And) a b

private def mkForallOpt (x body : Expr) : MetaM Expr :=
  if isTrueProp body then pure (mkConst ``True) else mkForallFVars #[x] body

/-- Proofs of both sides of `mkAndOpt a b` from a proof `p` of it. -/
private def unpairOpt (a b p : Expr) : Expr × Expr :=
  if isTrueProp a then (mkConst ``True.intro, p)
  else if isTrueProp b then (p, mkConst ``True.intro)
  else (mkApp3 (mkConst ``And.left) a b p, mkApp3 (mkConst ``And.right) a b p)

/-- `(K, F)` for `e`; `isK` recognizes the κ fvars. -/
private partial def splitClauses (isK : FVarId → Bool) (e : Expr) : MetaM (Expr × Expr) := do
  let e := e.consumeMData
  if !e.hasAnyFVar isK then return (mkConst ``True, e)
  if let some (a, b) := e.and? then
    let (ka, fa) ← splitClauses isK a
    let (kb, fb) ← splitClauses isK b
    return (mkAndOpt ka kb, mkAndOpt fa fb)
  if e.isForall && !e.bindingDomain!.hasAnyFVar isK then
    return ← withLocalDecl e.bindingName! e.bindingInfo! e.bindingDomain! fun x => do
      let (k, f) ← splitClauses isK (e.bindingBody!.instantiate1 x)
      return (← mkForallOpt x k, ← mkForallOpt x f)
  return (e, mkConst ``True)

/-- A proof of `e` from proofs `pk : K` and `pf : F` of its split. -/
private partial def joinClauses (isK : FVarId → Bool) (e pk pf : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if !e.hasAnyFVar isK then return pf
  if let some (a, b) := e.and? then
    let (ka, fa) ← splitClauses isK a
    let (kb, fb) ← splitClauses isK b
    let (pka, pkb) := unpairOpt ka kb pk
    let (pfa, pfb) := unpairOpt fa fb pf
    return mkApp4 (mkConst ``And.intro) a b
      (← joinClauses isK a pka pfa) (← joinClauses isK b pkb pfb)
  if e.isForall && !e.bindingDomain!.hasAnyFVar isK then
    return ← withLocalDecl e.bindingName! e.bindingInfo! e.bindingDomain! fun x => do
      let body := e.bindingBody!.instantiate1 x
      let (k, f) ← splitClauses isK body
      let pk := if isTrueProp k then mkConst ``True.intro else mkApp pk x
      let pf := if isTrueProp f then mkConst ``True.intro else mkApp pf x
      mkLambdaFVars #[x] (← joinClauses isK body pk pf)
  return pk

/-- Open the `∃`-prefix of `e` as local κs. -/
private partial def peelExists (e : Expr) (κs : Array Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let e ← whnf e
  if e.isAppOfArity ``Exists 2 then
    if let .lam name α body _ := e.appArg! then
      return ← withLocalDeclD name α fun κ => peelExists (body.instantiate1 κ) (κs.push κ) k
  k κs e

/-- A proof of the `∃`-chain `type` with witnesses `κs` and body proof `p`. -/
private def introExists (type : Expr) (κs : List Expr) (p : Expr) : MetaM Expr := do
  match κs with
  | [] => return p
  | κ :: rest =>
    let type ← whnf type
    let pred := type.appArg!
    mkAppOptM ``Exists.intro
      #[type.appFn!.appArg!, pred, κ, ← introExists (pred.beta #[κ]) rest p]

/-- Eliminate the first `n` `∃`s of `p : type` into `motive`. -/
private partial def elimExists (n : Nat) (p type motive : Expr) (κs : Array Expr)
    (k : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  if n == 0 then return ← k κs p
  let type ← whnf type
  let α := type.appFn!.appArg!
  let pred := type.appArg!
  withLocalDeclD `κ α fun κ => do
    let rest := pred.beta #[κ]
    withLocalDeclD `h rest fun h => do
      let inner ← elimExists (n - 1) h rest motive (κs.push κ) k
      mkAppOptM ``Exists.elim #[α, pred, motive, p, ← mkLambdaFVars #[κ, h] inner]

/-- Replace the κ goal with `∃ κs, K` and the κ-free `F`; `none` if either is empty. -/
private def separateFree (goal : MVarId) : MetaM (Option (MVarId × MVarId)) :=
  goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    -- Everything returned from the scope is closed over the κs.
    let split? ← peelExists type #[] fun κs body => do
      let isK := fun id => κs.any (·.fvarId! == id)
      let (k, f) ← splitClauses isK body
      if isTrueProp k || isTrueProp f then return none
      let mut kType := k
      for κ in κs.reverse do
        kType ← mkAppM ``Exists #[← mkLambdaFVars #[κ] kType]
      let build ← withLocalDeclD `hk k fun hk => withLocalDeclD `hf f fun hf => do
        let proof ← introExists type κs.toList (← joinClauses isK body hk hf)
        mkLambdaFVars (κs ++ #[hk, hf]) proof
      return some (κs.size, kType, f, build)
    let some (n, kType, f, build) := split? | return none
    let kGoal ← mkFreshExprSyntheticOpaqueMVar kType
    let fGoal ← mkFreshExprSyntheticOpaqueMVar f
    goal.assign (← elimExists n kGoal kType type #[] fun κs hk =>
      return build.beta (κs ++ #[hk, fGoal]))
    return some (kGoal.mvarId!, fGoal.mvarId!)

/-- Bundle privately introduced binders and obligations into one visible VC. -/
private def tidy (ctx : Context) (parent : MVarId) : TacticM Unit := do
  discard <| phase ctx "cleanup" ctx.setup.config.zapHeartbeats do
    let goals ← Flex.Residual.bundle parent (← getUnsolvedGoals)
    setGoals (← goals.filterM fun goal => return !(← goal.isAssignedOrDelayedAssigned))

/-- Stages and backend attempts run under `Flex.Timeout.run`, which passes their deadline to
the automation below; it checks the deadline and caps its external calls by it. -/
private def proofOracle (ctx : Context) : PAOracle := fun target => do
  if let some tactic := ctx.setup.proof then
    if let some proof ← Flex.Automation.proveWith tactic target then return some proof
  Flex.Automation.proofOracle target

private def synthOracle (ctx : Context) : PASynthOracle := fun targets =>
  match ctx.setup.synth with
  | none => Flex.Automation.synthOracle targets
  | some tactic => (withPAPriority tactic).toSynth targets

private def close (ctx : Context) : TacticM Unit := do
  unless ctx.setup.config.closeLeaves do return
  let oracle : PAOracle := match ctx.setup.closer with
    | none => proofOracle ctx
    | some tactic => fun target => do
        Flex.Timeout.checkDeadline
        Flex.Automation.proveWith tactic target
  let mut remaining := []
  for goal in ← getGoals do
    setGoals [goal]
    discard <| phase ctx "discharge" ctx.setup.config.dischargeHeartbeats do
      let before ← Tactic.saveState
      let provedLeaf ← IO.mkRef false
      Flex.Automation.discharge fun target => do
        let proof ← oracle target
        if proof.isSome then provedLeaf.set true
        return proof
      -- Failed search need not leave hundreds of split goals to reassemble.
      if !(← provedLeaf.get) && !(← getUnsolvedGoals).isEmpty then restore before
    remaining := remaining ++ (← getUnsolvedGoals)
  setGoals remaining

private partial def validate (ctx : Context) (target : Expr) : TermElabM PASynthResult := do
  Flex.Timeout.checkDeadline
  let target ← instantiateMVars target
  if target.isConstOf ``True then return .valid
  if target.isForall then
    return ← withLocalDecl target.bindingName! target.bindingInfo! target.bindingDomain! fun x =>
      validate ctx (target.bindingBody!.instantiate1 x)
  if let some (left, right) := target.and? then
    let a ← validate ctx left
    if a == .invalid then return a
    let b ← validate ctx right
    if b == .invalid then return b
    return if a == .valid && b == .valid then .valid else .unknown "unvalidated obligations"
  let results ← synthOracle ctx #[target]
  if results.size != 1 then throwError "flex: invalid validation response"
  return results[0]!

private structure Candidate where
  backend : Backend
  validated : Bool
  remainingHeads : Option Nat

private inductive PASearch where
  | full | sources
  deriving BEq

private def runPA (ctx : Context) (scrape : PAScrapeConfig)
    (allowUnprovedHeads : Bool) (search : PASearch := .full) : TacticM Candidate := do
  let directSources := search != .full
  let report ← IO.mkRef ({} : PACertificationReport)
  let decision : PASynthOracle := fun queries => do
    let options ← getOptions
    let limit := min (if search == .sources then 5000 else 2000)
      (flex.automation.proofHeartbeats.get options)
    withOptions (fun opts => if directSources then
        opts.set `flex.automation.proofHeartbeats limit else opts) <|
      synthOracle ctx queries
  withOptions (fun opts =>
      -- An explicit PA stage owns the synthesis deadline as well as certification.
      let opts := if ctx.setup.config.paTimeout > 0 then
          flex.fixpointTimeout.set opts 0 else opts
      if search == .sources && !opts.contains `flex.automation.equationHeartbeats then
        opts.set `flex.automation.equationHeartbeats (5000 : Nat) else opts) <|
    fixImpl proveLeaf scrape (some (proofOracle ctx)) (observe := ctx.setup.onPA)
      (synthOracle := some decision) (allowUnprovedHeads := allowUnprovedHeads)
      (onCertification := fun result => report.set result) (directSources := directSources)
  let report ← report.get
  return {
    backend := .fix
    validated := report.allValidated
    remainingHeads := some report.remainingHeads }

/-- Prefer source instances when unrestricted slot permutations exceed the search budget. -/
private partial def largeTemplateSearch (type : Expr) (limits : PAScrapeLimits) : MetaM Bool := do
  let type ← whnf type
  unless type.isAppOfArity ``Exists 2 do return false
  let domain := type.getArg! 0
  let arity ← forallTelescopeReducing domain fun parameters _ => pure parameters.size
  let permutations := (List.range (min arity limits.maxParams)).foldl
    (fun count index => count * (arity - index)) 1
  if permutations > limits.maxInstancesPerKappa then return true
  withLocalDeclD `κ domain fun κ =>
    largeTemplateSearch (type.appArg!.beta #[κ]) limits

private def runBackend (ctx : Context) (backend : Backend)
    (onCandidate : MVarId → TermElabM PASynthResult) : TacticM Candidate := do
  match backend with
  | .fix =>
    -- Try source instances before enumerating templates. A failed attempt rolls back;
    -- only certified heads and validated safety clauses can commit the smaller pool.
    if (ctx.setup.scrape.mode == .standard || ctx.setup.scrape.mode == .deep) &&
        ctx.setup.scrape.maxCandidatesPerKappa > 0 &&
        (← withMainContext do largeTemplateSearch (← getMainTarget) ctx.setup.scrape.toPAScrapeLimits) then
      let sourceCtx := { ctx with
        setup := { ctx.setup with config := { ctx.setup.config with heartbeats := 0 } } }
      let budget := if ctx.setup.config.paHeartbeats == 0 then 500000 else
        max 1 (ctx.setup.config.paHeartbeats / 3)
      let budget ← if (← getMaxHeartbeats) == 0 then pure budget else do
        pure (min budget (max 1 ((← getRemainingHeartbeats) / 3000)))
      let result ← phase sourceCtx "fix source candidates" budget <|
        runPA sourceCtx { ctx.setup.scrape with maxCandidatesPerKappa := 0 } false
      if let .ok candidate := result then
        trace[flex] "fix: source candidates certified"
        return candidate
    if ctx.setup.scrape.mode == .deep && ctx.setup.scrape.maxStatefulCandidatesPerKappa > 0 &&
        (← withMainContext do Flex.Automation.Equations.hasStatefulRecursion (← getMainTarget)) then
      let result ← guarded <| runPA ctx
        { ctx.setup.scrape with maxCandidatesPerKappa := 0 } true .sources
      if let .ok candidate := result then
        trace[flex] "fix: stateful source candidates validated"
        return candidate
      if let .error message := result then trace[flex] "fix stateful sources: {message}"
    runPA ctx ctx.setup.scrape true
  | .spacer | .eldarica =>
    let name := if backend == .spacer then flex.spacer.executable else flex.eldarica.executable
    let validated ← IO.mkRef false
    -- The attempt's deadline (this backend's share), not the stage's.
    let deadline ← Flex.Timeout.deadline?
    let remaining ← Flex.Timeout.capMs (UInt64.size - 1)
    let timeout := if ctx.setup.config.solverTimeout == 0 then remaining else
      min remaining (ctx.setup.config.solverTimeout * 1000)
    let searchAttempts := if backend == .spacer then 3 else 2
    let result ← Flex.CHC.solveGoal (← getMainGoal) {
      backend := if backend == .spacer then .spacer else .eldarica
      executable := some (name.get (← getOptions))
      -- Leave the next backend a chance when retries would exhaust the deadline.
      retrySearch := deadline.isNone || remaining > searchAttempts * timeout
      deadlineMs := deadline
      timeoutMs := timeout } (proofOracle ctx) (headsOnly := true)
      (onPhase := fun stage elapsed => do
        let name := match stage with
          | .prepare => "prepare" | .exporting => "export" | .solver => "solver"
          | .importing => "import" | .certificate => "certificate"
        ctx.setup.onPhase {
          phase := s!"{backend}/{name}"
          status := if elapsed.isSome then "end" else "start"
          elapsedMs := elapsed.getD 0 })
      (onCandidate := some fun goal => do
        let answer ← onCandidate goal
        validated.set (answer == .valid)
        return answer)
      (onEvent := ctx.setup.onCHC backend)
      (retryInconclusiveCandidates := true)
    let report ← match result with
      | .failed failure => throwError "{failure.message}"
      | .solved report | .partial report => pure report
    setGoals report.certificate.goals.toList
    return {
      backend := backend
      validated := (← validated.get) || report.certificate.goals.isEmpty
      remainingHeads := report.certificate.remainingHeads }

private def better (candidate best : Candidate) : Bool :=
  if candidate.validated != best.validated then candidate.validated
  else match candidate.remainingHeads, best.remainingHeads with
    | some count, some old => count < old
    | some _, none => true
    | _, _ => false

/-- Reserve a share of the remaining CHC time for each untried backend. -/
private def backendContext (ctx : Context) (backend : Backend) (later : List Backend)
    : TacticM Context := do
  let some deadline := ctx.deadline | return ctx
  -- An unsplit, legacy portfolio keeps its PA cap; staged portfolios isolate PA already.
  if backend == .fix then return ctx
  let now ← IO.monoMsNow
  let slots := 1 + (later.filter (· != .fix)).length
  return { ctx with deadline := some (now + (deadline - now) / slots) }

/-- All alternatives start before predicate assignment. Only accepted branches survive. -/
private def solveKGoal (ctx : Context) (goal : MVarId) (siblings : List MVarId) : TacticM Unit := do
  setGoals [goal]
  let entry ← Tactic.saveState
  let best ← IO.mkRef (none : Option (Candidate × Tactic.SavedState))
  let retain (candidate : Candidate) : TacticM Unit := do
    if (← best.get).all (fun (previous, _) => better candidate previous ||
        (candidate.backend == previous.backend && candidate.validated == previous.validated &&
          candidate.remainingHeads == previous.remainingHeads)) then
      ctx.setup.onSynthesis goal candidate.backend candidate.validated candidate.remainingHeads
        (← getGoals).toArray
      best.set (some (candidate, ← Tactic.saveState))
      checkpoint ctx siblings
  let skip (backends : List Backend) (reason : String) := do
    for backend in backends do
      ctx.setup.onPhase { phase := s!"attempt/{backend}", status := reason }
  let search : TacticM Bool := do
    let mut backends := ctx.setup.backends
    while let backend :: later := backends do
      backends := later
      restore entry
      let attemptCtx ← backendContext ctx backend later
      let started ← IO.monoMsNow
      let allowance := attemptCtx.deadline.map (· - started)
      if allowance == some 0 then
        skip (backend :: later) "skipped_budget"
        break
      let pending ← IO.mkRef (none : Option (Candidate × Tactic.SavedState))
      let run : TacticM Unit := do
        let ctx := attemptCtx
        let tacticState ← getThe Tactic.State
        -- Save validated instantiations before certification can exhaust the budget.
        let onCandidate : MVarId → TermElabM PASynthResult := fun residual => do
          let start ← IO.monoMsNow
          let status ← IO.mkRef "interrupted"
          ctx.setup.onPhase { phase := s!"{backend}/validate", status := "start" }
          try
            tryCatchRuntimeEx (do
              -- Check the whole instantiated VC once, not each invariant conjunct separately.
              let answers ← synthOracle ctx #[← instantiateMVars (← residual.getType)]
              unless answers.size == 1 do throwError "flex: invalid validation response"
              let answer := answers[0]!
              status.set (match answer with
                | .valid => "valid" | .invalid => "invalid" | .unknown _ => "unknown")
              unless answer == .valid do return answer
              let candidate : Candidate := {
                backend, validated := true, remainingHeads := none }
              ctx.setup.onSynthesis goal backend true none #[residual]
              let state : Tactic.SavedState := {
                term := ← Term.saveState, tactic := { tacticState with goals := [residual] } }
              pending.set (some (candidate, state))
              if (← best.get).all (fun (previous, _) => better candidate previous) then
                ctx.checkpoint.set { state with
                  tactic := { state.tactic with goals := residual :: siblings } }
              return .valid) fun error => do
                if error.isInterrupt then throw error
                Core.checkInterrupted
                status.set "failed"
                trace[flex] "{backend}: candidate validation failed: {error.toMessageData}"
                return .unknown "candidate validation failed"
          finally
            ctx.setup.onPhase {
              phase := s!"{backend}/validate"
              status := ← status.get
              elapsedMs := (← IO.monoMsNow) - start }
        let budget := if backend == .fix then ctx.setup.config.paHeartbeats
          else ctx.setup.config.solverHeartbeats
        let result ← phase ctx s!"{backend}" budget (runBackend ctx backend onCandidate)
        let candidate ← match result with
          | .ok candidate => pure candidate
          | .error _ =>
            let some (candidate, state) ← pending.get | return
            restore state
            pure candidate
        if candidate.validated then retain candidate
        -- Closing is separate: a failed proof search cannot undo synthesis.
        discard <| guarded (close ctx)
        let goals ← getUnsolvedGoals
        if goals.isEmpty then
          checkpoint ctx siblings
          if ctx.setup.config.report then logInfo m!"flex: {backend} completed the predicate goal"
          return
        let mut valid := candidate.validated
        let mut refuted := false
        unless valid do
          let validation ← phase ctx "validate candidate" ctx.setup.config.solverHeartbeats do
            let mut allValid := true
            for pending in goals do
              let answer ← pending.withContext do validate ctx (← pending.getType)
              if answer == .invalid then return (false, true)
              if answer != .valid then allValid := false
            return (allValid, false)
          if let .ok (checked, invalid) := validation then
            valid := checked
            refuted := invalid
        if refuted || (!valid && !ctx.setup.config.keepCandidates) then
          trace[flex] "{backend}: candidate {if refuted then "refuted" else "unvalidated"}"
          return
        let candidate := { candidate with validated := valid }
        retain candidate
        tidy ctx goal
        retain candidate
      ctx.setup.onPhase {
        phase := s!"attempt/{backend}", status := "start"
        budgetMs := allowance, deadlineMs := attemptCtx.deadline }
      let result ← Flex.Timeout.run attemptCtx.deadline run
      if result.isNone then
        -- The shared checkpoint includes siblings hidden during this attempt.
        let saved ← ctx.checkpoint.get
        restore { saved with tactic := { saved.tactic with
          goals := saved.tactic.goals.take (saved.tactic.goals.length - siblings.length) } }
        if let some (candidate, _) ← pending.get then retain candidate
      let solved ← getUnsolvedGoals
      let inferred := (← best.get).any fun (candidate, _) =>
        candidate.validated && candidate.remainingHeads == some 0
      let accepted := (← best.get).any fun (candidate, _) => candidate.backend == backend
      ctx.setup.onPhase {
        phase := s!"attempt/{backend}"
        status := if result.isNone then "timeout"
          else if accepted || solved.isEmpty then "ok" else "failed"
        elapsedMs := (← IO.monoMsNow) - started
        budgetMs := allowance, deadlineMs := attemptCtx.deadline }
      if solved.isEmpty then
        skip later "skipped_solved"
        return true
      if inferred then
        skip later "skipped_inferred"
        break
    return false
  let completed ← tryCatchRuntimeEx search fun error => do
    if error.isInterrupt then
      restore entry
      throw error
    Core.checkInterrupted
    trace[flex] "portfolio stopped: {error.toMessageData}"
    return false
  if completed then return
  match ← best.get with
  | none => restore entry
  | some (candidate, state) =>
    restore state
    if ctx.setup.config.report then
      let status := if candidate.validated then "validated invariant" else "provisional candidate"
      logInfo m!"flex: {candidate.backend} retained a {status}; remaining obligations are shown"

private def transform (ctx : Context) (name : String) (siblings : List MVarId)
    (act : TacticM Unit) : TacticM Unit := do
  discard <| phase ctx name ctx.setup.config.zapHeartbeats act
  checkpoint ctx siblings

private def cleanup (ctx : Context) (parent : MVarId) (siblings : List MVarId) : TacticM Unit := do
  checkpoint ctx siblings
  tidy ctx parent
  checkpoint ctx siblings

private def solveResidual (ctx : Context) (goal : MVarId) (siblings : List MVarId)
    : TacticM (List MVarId) := do
  setGoals [goal]
  let split ← if ctx.setup.config.splitFree then
      phase ctx "separate clauses" ctx.setup.config.zapHeartbeats (separateFree goal)
    else pure (.ok none)
  let (predicate, free) := match split with
    | .ok (some (k, f)) => (k, [f])
    | _ => (goal, [])
  setGoals [predicate]
  checkpoint ctx (free ++ siblings)
  discard <| guarded (solveKGoal ctx predicate (free ++ siblings)) (quiet := false)
  let residual ← getUnsolvedGoals
  setGoals free
  close ctx
  let free ← getUnsolvedGoals
  setGoals (residual ++ free)
  cleanup ctx goal siblings
  getUnsolvedGoals

/-- Discover predicate goals under positive quantifiers and conjunctions. -/
private partial def walk (ctx : Context) (goal : MVarId) (siblings : List MVarId)
    (prepared : Bool := false) : TacticM (List MVarId) := do
  setGoals [goal]
  let mut prepared := prepared
  let mut zapPrepared := !ctx.setup.config.preprocess
  if ctx.setup.config.preprocess then
    let result ← phase ctx "preprocess" ctx.setup.config.preprocessHeartbeats do
      let next ← Flex.Preprocess.prepareGoal goal (simplify := !prepared)
      setGoals (if ← next.isAssignedOrDelayedAssigned then [] else [next])
    checkpoint ctx siblings
    if result matches .ok _ then
      prepared := true
      zapPrepared := true
  if (← getGoals).isEmpty then return []
  let current ← getMainGoal
  if ← isKGoal current then
    if ctx.setup.config.nesting then
      transform ctx "nesting" siblings do
        let result ← current.withContext do
          Flex.Preprocess.Nesting.nest (← whnf (← current.getType))
        let next ← current.withContext do mkFreshExprSyntheticOpaqueMVar result.expr
        current.assign (← mkAppM ``Iff.mpr #[result.proof, next])
        setGoals [next.mvarId!]
    -- Other backends may still run if preparation failed, but Zap must not.
    if ctx.setup.config.zap && zapPrepared then
      let strategy ← match ctx.setup.config.zapCertificate with
        | .constructive => pure emitStrategy
        | .grind => pure (searchStrategy (← `(tactic| grind)) "zap_grind")
        | .aesop => pure (searchStrategy (← `(tactic| aesop)) "zap_aesop")
      let before ← getGoals
      transform ctx "zap" siblings do
        zapImpl strategy (preprocess := false) (postprocess := false)
        let after ← getGoals
        if after != before then ctx.setup.onZap after.tail.toArray
      if ctx.setup.config.postprocess && (← getGoals) != before then
        transform ctx "postprocess" siblings do
          setGoals (← (← getUnsolvedGoals).mapM fun goal => do Flex.Preprocess.cleanupGoal goal)
    let mut outputs := []
    let mut pending ← getUnsolvedGoals
    while let next :: rest := pending do
      pending := rest
      let tail := outputs ++ pending ++ siblings
      if ← isKGoal next then
        outputs := outputs ++ (← solveResidual ctx next tail)
      else
        setGoals [next]
        close ctx
        cleanup ctx next tail
        outputs := outputs ++ (← getUnsolvedGoals)
    setGoals outputs
  else
    let type ← current.withContext do whnf (← current.getType)
    if type.isForall || type.isAppOfArity ``And 2 then
      let exposed ← phase ctx "expose goal" ctx.setup.config.zapHeartbeats do
        let children ← if type.isForall then do
          let (_, child) ← current.intro1
          pure [child]
        else current.apply (mkConst ``And.intro)
        setGoals children
        return children
      if let .ok children := exposed then
        checkpoint ctx siblings
        let mut outputs := []
        let mut pending := children
        while let child :: rest := pending do
          pending := rest
          outputs := outputs ++ (← walk ctx child (outputs ++ pending ++ siblings) prepared)
        setGoals outputs
      else close ctx
    else close ctx
  cleanup ctx goal siblings
  getUnsolvedGoals

/-- Run a stage on the current frontier; interruption preserves committed progress. -/
private def runStage (ctx : Context) (name : String) : TacticM Unit := do
  let start ← IO.monoMsNow
  let allowance := ctx.deadline.map (· - start)
  ctx.setup.onPhase {
    phase := name, status := "start"
    budgetMs := allowance, deadlineMs := ctx.deadline }
  let result ← Flex.Timeout.run ctx.deadline do
    tryCatchRuntimeEx (do
      let mut outputs := []
      let mut pending ← getUnsolvedGoals
      while let goal :: rest := pending do
        pending := rest
        outputs := outputs ++ (← walk ctx goal (outputs ++ pending))
      setGoals outputs) fun error => do
        restore (← ctx.checkpoint.get)
        if error.isInterrupt then throw error
        Core.checkInterrupted
        trace[flex] "stopped at checkpoint: {error.toMessageData}"
  if result.isNone then
    restore (← ctx.checkpoint.get)
    trace[flex] "time budget exhausted; retained the last checkpoint"
  ctx.setup.onPhase {
    phase := name
    status := if result.isSome then "ok" else "timeout"
    elapsedMs := (← IO.monoMsNow) - start
    budgetMs := allowance, deadlineMs := ctx.deadline }

/-- Preserve the latest committed frontier even when a later traversal reaches a limit. -/
def flexImpl (setup : Setup) : TacticM Unit := focus do
  let timingEnabled ← isTracingEnabledFor `flex.timing
  let events ← IO.mkRef (#[] : Array PhaseEvent)
  let notify := setup.onPhase
  let setup := { setup with onPhase := fun event => do
    if timingEnabled then events.modify (·.push event)
    notify event }
  let parent ← getMainGoal
  let initial ← Tactic.saveState
  let saved ← IO.mkRef initial
  let deadline ← if setup.config.totalTimeout == 0 then pure none else
    pure (some ((← IO.monoMsNow) + setup.config.totalTimeout * 1000))
  let reserve ← if (← getMaxHeartbeats) == 0 then pure 0 else
    pure (min 20000000 ((← getRemainingHeartbeats) / 20))
  let ctx : Context := { setup, deadline, reserve, checkpoint := saved }
  let separatePA := setup.config.zapTimeout > 0 || setup.config.paTimeout > 0
  if setup.config.chcFirst || setup.config.stageTimeout > 0 || separatePA then
    let external := setup.backends.filter (· != .fix)
    let internal := setup.backends.filter (· == .fix)
    let se : Setup := { setup with
      backends := external
      config := { setup.config with zap := false, nesting := false } }
    let pa : Setup := { setup with backends := internal }
    let hasInternal := setup.config.zap || setup.config.nesting || !internal.isEmpty
    let internalStages := if separatePA then Id.run do
        let zap : Setup := { setup with
          backends := []
          config := { setup.config with closeLeaves := false } }
        let fix : Setup := { pa with
          config := { pa.config with zap := false, nesting := false } }
        let stages := if setup.config.zap || setup.config.nesting then
            [("stage/zap", zap, setup.config.zapTimeout)] else []
        return stages ++ (if !internal.isEmpty || setup.config.closeLeaves then
          [("stage/fix", fix, setup.config.paTimeout)] else [])
      else [("stage/zap_fix", pa, 0)]
    let mut stages := if external.isEmpty then internalStages
      else if !hasInternal then [("stage/se", se, 0)]
      else if setup.config.chcFirst then [("stage/se", se, 0)] ++ internalStages
      else internalStages ++ [("stage/se", se, 0)]
    while let (name, stageSetup, cap) :: later := stages do
      stages := later
      if (← getUnsolvedGoals).isEmpty then break
      let now ← IO.monoMsNow
      let remaining := deadline.map (· - now)
      let share := remaining.map (· / (1 + later.length))
      -- Explicit component caps are maxima, not equal shares of the total budget.
      let allowance := if cap > 0 then
          some (remaining.map (min (cap * 1000)) |>.getD (cap * 1000))
        else if setup.config.stageTimeout == 0 then share else
        some (share.map (min (setup.config.stageTimeout * 1000)) |>.getD
          (setup.config.stageTimeout * 1000))
      runStage { ctx with setup := stageSetup, deadline := allowance.map (now + ·) } name
  else
    runStage ctx "search"
  -- Bundling is optional; keep the same frontier if its remaining budget expires.
  let bundled ← Flex.Timeout.run deadline do
    discard <| phase ctx "bundle residual" setup.config.zapHeartbeats do
      setGoals (← Flex.Residual.bundle parent (← getUnsolvedGoals))
  if bundled.isNone then restore (← saved.get)
  for event in ← events.get do
    if event.status != "start" then
      trace[flex.timing] "{event.phase}: {event.status}, {event.elapsedMs} ms"

end Flex.Portfolio

private declare_config_elab elabFlexConfig Flex.Portfolio.Config

declare_syntax_cat flexBackend
syntax "fix" : flexBackend
syntax "spacer" : flexBackend
syntax "eldarica" : flexBackend

/-- Eliminate predicates and prove what can be discharged, leaving ordinary Lean goals.
PA escalates scraping by default. `proof` certifies candidates; `closer` proves residuals. -/
syntax "flex" (atomic("(" &"backends" ":=") "[" flexBackend,* "]" ")")?
  (atomic("(" &"scrape" ":=") ident ")")?
  (atomic("(" &"defs" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"synth" ":=") tacticSeq ")")?
  (atomic("(" &"proof" ":=") tacticSeq ")")?
  (atomic("(" &"closer" ":=") tacticSeq ")")?
  (atomic("(" &"config" ":=") term ")")? : tactic

elab_rules : tactic
  | `(tactic| flex $[(backends := [$backends:flexBackend,*])]? $[(scrape := $mode:ident)]?
      $[(defs := [$defs:ident,*])]?
      $[(synth := $synth:tacticSeq)]? $[(proof := $proof:tacticSeq)]?
      $[(closer := $closer:tacticSeq)]? $[(config := $config:term)]?) => do
    let backends ← match backends with
      | none => pure Flex.Portfolio.Backend.all
      | some names => (names.getElems.toList.map (·.raw)).mapM fun
        | `(flexBackend| fix) => pure Flex.Portfolio.Backend.fix
        | `(flexBackend| spacer) => pure .spacer
        | `(flexBackend| eldarica) => pure .eldarica
        | stx => throwErrorAt stx "flex: unknown backend"
    let resolve (names : Array Ident) : TacticM (Array Name) :=
      names.mapM fun name => realizeGlobalConstNoOverloadWithInfo name
    let defs ← resolve (defs.map (·.getElems) |>.getD #[])
    let config ← match config with
      | none => pure ({} : Flex.Portfolio.Config)
      | some value => do
        let stx ← `(Lean.Parser.Term.optConfig| (config := $value))
        elabFlexConfig stx (logExceptions := false)
    let mode ← parseScrapeMode "flex" mode
    let tactic := fun (stx : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) =>
      stx.mapM fun tac => `(tactic| ($tac:tacticSeq))
    Flex.Portfolio.flexImpl {
      config, backends
      scrape := { config.scrapeLimits with mode, defs }
      synth := ← tactic synth, proof := ← tactic proof, closer := ← tactic closer }
