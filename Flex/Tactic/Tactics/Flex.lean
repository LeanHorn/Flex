import Flex.Tactic.Tactics.Zap
import Flex.Tactic.Tactics.Fix
import Flex.Tactic.Tactics.Eldarica
import Flex.Preprocess.Cleanup
import Flex.Preprocess.Nesting
import Flex.Tactic.Residual

open Lean Meta Elab Tactic

namespace Flex.Portfolio

initialize registerTraceClass `flex

inductive Backend where
  | fix | spacer | eldarica
  deriving BEq, Repr

instance : ToString Backend where
  toString
    | .fix => "fix"
    | .spacer => "spacer"
    | .eldarica => "eldarica"

def Backend.all : List Backend := [.fix, .spacer, .eldarica]

/-- Phase limits remain subject to the caller's heartbeat limit. Times are seconds. -/
structure Config where
  preprocess : Bool := true
  nesting : Bool := false
  zap : Bool := true
  postprocess : Bool := true
  closeLeaves : Bool := true
  splitFree : Bool := true
  /-- Expose unvalidated solver candidates for manual exploration. Refuted ones are rejected. -/
  keepCandidates : Bool := false
  report : Bool := false
  /-- Optional common override; zero uses the individual phase limits. -/
  heartbeats : Nat := 0
  zapHeartbeats : Nat := 200000
  paHeartbeats : Nat := 1500000
  solverHeartbeats : Nat := 500000
  dischargeHeartbeats : Nat := 500000
  paTimeout : Nat := 60
  solverTimeout : Nat := 60
  /-- Cooperative overall deadline; zero disables it. -/
  totalTimeout : Nat := 180
  scrapeLimits : PAScrapeLimits := {}

structure Setup where
  config : Config := {}
  backends : List Backend := Backend.all
  scrape : PAScrapeConfig := { mode := .deep }
  facts : Flex.CHC.Facts.Config := {}
  synth : Option (TSyntax `tactic) := none
  proof : Option (TSyntax `tactic) := none
  closer : Option (TSyntax `tactic) := none

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

private def checkTime (ctx : Context) : TermElabM Unit := do
  Core.checkInterrupted
  if let some deadline := ctx.deadline then
    if (← IO.monoMsNow) >= deadline then throwError "flex: time budget exhausted"

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
  let result ← guarded <| withBudget ctx heartbeats do
    checkTime ctx
    act
  if let .error message := result then trace[flex] "{name}: {message}"
  return result

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
  discard <| guarded do
    let goals ← Flex.Residual.bundle parent (← getUnsolvedGoals)
    let goals ← if ctx.setup.config.postprocess then
      goals.mapM fun goal => Flex.Preprocess.cleanupGoal goal else pure goals
    setGoals (← goals.filterM fun goal => return !(← goal.isAssignedOrDelayedAssigned))

private def proofOracle (ctx : Context) : PAOracle := fun target => do
  checkTime ctx
  if let some tactic := ctx.setup.proof then
    if let some proof ← Flex.Automation.proveWith tactic target then return some proof
  Flex.Automation.proofOracle target

private def synthOracle (ctx : Context) : PASynthOracle := fun targets => do
  checkTime ctx
  let result ← match ctx.setup.synth with
    | none => Flex.Automation.synthOracle (checkTime ctx) targets
    | some tactic => (withPAPriority tactic).toSynth targets
  checkTime ctx
  return result

private def close (ctx : Context) : TacticM Unit := do
  unless ctx.setup.config.closeLeaves do return
  let oracle : PAOracle := match ctx.setup.closer with
    | none => proofOracle ctx
    | some tactic => fun target => do
        checkTime ctx
        Flex.Automation.proveWith tactic target
  let mut remaining := []
  for goal in ← getGoals do
    setGoals [goal]
    discard <| phase ctx "discharge" ctx.setup.config.dischargeHeartbeats do
      Flex.Automation.discharge oracle
    remaining := remaining ++ (← getUnsolvedGoals)
  setGoals remaining

private partial def validate (ctx : Context) (target : Expr) : TermElabM PASynthResult := do
  checkTime ctx
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

private def runBackend (ctx : Context) (backend : Backend) : TacticM Candidate := do
  match backend with
  | .fix =>
    let report ← IO.mkRef ({} : PACertificationReport)
    let now ← IO.monoMsNow
    let deadline := now + ctx.setup.config.paTimeout * 1000
    let paCtx := if ctx.setup.config.paTimeout == 0 then ctx else
      { ctx with deadline := some (ctx.deadline.map (min deadline) |>.getD deadline) }
    fixImpl proveLeaf ctx.setup.scrape (some (proofOracle paCtx))
      (synthOracle := some (synthOracle paCtx)) (allowUnprovedHeads := true)
      (onCertification := fun result => report.set result)
    let report ← report.get
    return { backend, validated := report.allValidated, remainingHeads := some report.remainingHeads }
  | .spacer | .eldarica =>
    let name := if backend == .spacer then flex.spacer.executable else flex.eldarica.executable
    let mut timeout := ctx.setup.config.solverTimeout * 1000
    if timeout == 0 then throwError "flex: CHC solvers disabled by timeout"
    if let some deadline := ctx.deadline then
      timeout := min timeout (deadline - (← IO.monoMsNow))
      if timeout == 0 then throwError "flex: time budget exhausted"
    let result ← Flex.CHC.solveGoal (← getMainGoal) {
      backend := if backend == .spacer then .spacer else .eldarica
      executable := some (name.get (← getOptions))
      timeoutMs := timeout } (proofOracle ctx) (headsOnly := true) (facts := ctx.setup.facts)
    let report ← match result with
      | .failed failure => throwError "{failure.message}"
      | .solved report | .partial report => pure report
    setGoals report.certificate.goals.toList
    return {
      backend := backend
      validated := report.certificate.goals.isEmpty
      remainingHeads := report.certificate.remainingHeads }

private def better (candidate best : Candidate) : Bool :=
  if candidate.validated != best.validated then candidate.validated
  else match candidate.remainingHeads, best.remainingHeads with
    | some count, some old => count < old
    | some _, none => true
    | _, _ => false

/-- All alternatives start before predicate assignment. Only accepted branches survive. -/
private def solveKGoal (ctx : Context) (goal : MVarId) : TacticM Unit := do
  setGoals [goal]
  let entry ← Tactic.saveState
  let best ← IO.mkRef (none : Option (Candidate × Tactic.SavedState))
  let search : TacticM Bool := do
    for backend in ctx.setup.backends do
      restore entry
      let budget := if backend == .fix then ctx.setup.config.paHeartbeats
        else ctx.setup.config.solverHeartbeats
      let result ← phase ctx s!"{backend}" budget (runBackend ctx backend)
      let .ok candidate := result | continue
      -- Closing is separate: a failed proof search cannot undo synthesis.
      discard <| guarded (close ctx)
      let goals ← getUnsolvedGoals
      if goals.isEmpty then
        if ctx.setup.config.report then logInfo m!"flex: {backend} completed the predicate goal"
        return true
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
        continue
      tidy ctx goal
      let candidate := { candidate with validated := valid }
      if (← best.get).all (fun (previous, _) => better candidate previous) then
        best.set (some (candidate, ← Tactic.saveState))
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
  discard <| guarded (solveKGoal ctx predicate) (quiet := false)
  let residual ← getUnsolvedGoals
  setGoals free
  close ctx
  let free ← getUnsolvedGoals
  setGoals (residual ++ free)
  cleanup ctx goal siblings
  getUnsolvedGoals

/-- Discover predicate goals under positive quantifiers and conjunctions. -/
private partial def walk (ctx : Context) (goal : MVarId) (siblings : List MVarId)
    : TacticM (List MVarId) := do
  setGoals [goal]
  if ctx.setup.config.preprocess then
    transform ctx "preprocess" siblings do
      let next ← Flex.Preprocess.prepareGoal goal
      setGoals (if ← next.isAssignedOrDelayedAssigned then [] else [next])
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
    if ctx.setup.config.zap then
      transform ctx "zap" siblings (zapImpl emitStrategy (preprocess := false))
    if ctx.setup.config.postprocess then
      transform ctx "postprocess" siblings do
        setGoals (← (← getUnsolvedGoals).mapM fun goal => Flex.Preprocess.cleanupGoal goal)
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
          outputs := outputs ++ (← walk ctx child (outputs ++ pending ++ siblings))
        setGoals outputs
      else close ctx
    else close ctx
  cleanup ctx goal siblings
  getUnsolvedGoals

/-- Preserve the latest committed frontier even when a later traversal reaches a limit. -/
def flexImpl (setup : Setup) : TacticM Unit := focus do
  let parent ← getMainGoal
  let initial ← Tactic.saveState
  let saved ← IO.mkRef initial
  let deadline ← if setup.config.totalTimeout == 0 then pure none else
    pure (some ((← IO.monoMsNow) + setup.config.totalTimeout * 1000))
  let reserve ← if (← getMaxHeartbeats) == 0 then pure 0 else
    pure (min 20000000 ((← getRemainingHeartbeats) / 20))
  let ctx : Context := { setup, deadline, reserve, checkpoint := saved }
  tryCatchRuntimeEx
    (discard <| walk ctx parent [])
    (fun error => do
      restore (← saved.get)
      if error.isInterrupt then throw error
      Core.checkInterrupted
      trace[flex] "stopped at checkpoint: {error.toMessageData}")
  -- Reserved resources are for presenting the retained obligations, even after timeout.
  tidy ctx parent

end Flex.Portfolio

private declare_config_elab elabFlexConfig Flex.Portfolio.Config

declare_syntax_cat flexBackend
syntax "fix" : flexBackend
syntax "spacer" : flexBackend
syntax "eldarica" : flexBackend

/-- Preprocess, eliminate predicates, and discharge what can be proved.
Deep scraping is the default. Unproved obligations remain as one structured VC.
`proof` customizes certification; `closer` customizes residual proof search.
`config` controls preparation, nesting, phases, budgets, and optional reporting. -/
syntax "flex" (atomic("(" &"backends" ":=") "[" flexBackend,* "]" ")")?
  (atomic("(" &"scrape" ":=") ident ")")?
  (atomic("(" &"defs" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"lemmas" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"synth" ":=") tacticSeq ")")?
  (atomic("(" &"proof" ":=") tacticSeq ")")?
  (atomic("(" &"closer" ":=") tacticSeq ")")?
  (atomic("(" &"config" ":=") term ")")? : tactic

elab_rules : tactic
  | `(tactic| flex $[(backends := [$backends:flexBackend,*])]? $[(scrape := $mode:ident)]?
      $[(defs := [$defs:ident,*])]? $[(lemmas := [$lemmas:ident,*])]?
      $[(synth := $synth:tacticSeq)]? $[(proof := $proof:tacticSeq)]?
      $[(closer := $closer:tacticSeq)]? $[(config := $config:term)]?) => do
    let backends ← match backends with
      | none => pure Flex.Portfolio.Backend.all
      | some names => names.getElems.toList.mapM fun
        | `(flexBackend| fix) => pure Flex.Portfolio.Backend.fix
        | `(flexBackend| spacer) => pure .spacer
        | `(flexBackend| eldarica) => pure .eldarica
        | stx => throwErrorAt stx "flex: unknown backend"
    let resolve (names : Array Ident) : TacticM (Array Name) :=
      names.mapM fun name => realizeGlobalConstNoOverloadWithInfo name
    let defs ← resolve (defs.map (·.getElems) |>.getD #[])
    let lemmas ← resolve (lemmas.map (·.getElems) |>.getD #[])
    let config ← match config with
      | none => pure ({} : Flex.Portfolio.Config)
      | some value => do
        let stx ← `(Lean.Parser.Term.optConfig| (config := $value))
        elabFlexConfig stx (logExceptions := false)
    let mode ← if mode.isNone then pure PAScrapeMode.deep else parseScrapeMode "flex" mode
    let tactic := fun (stx : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) =>
      stx.mapM fun tac => `(tactic| ($tac:tacticSeq))
    Flex.Portfolio.flexImpl {
      config, backends
      scrape := { config.scrapeLimits with mode, defs }
      facts := { lemmas, defs }
      synth := ← tactic synth, proof := ← tactic proof, closer := ← tactic closer }
