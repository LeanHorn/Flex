import Flex.Tactic.Tactics.Zap
import Flex.Tactic.Tactics.Fix
import Flex.Tactic.Tactics.Eldarica

open Lean Meta Elab Tactic

/-! ## `flex` — `zap`, then a portfolio of invariant backends

  1. `zap` eliminates the acyclic κs (skipped when the goal has none). If it
     fails, `flex` continues on the original goal.
  2. Clauses of the remaining `∃ κs, …` goal that mention no κ are split off
     into their own goal: they hold or fail regardless of the invariant.
  3. The κ goal goes to the backends in order (default `fix`, `spacer`,
     `eldarica`), each solving all its κs at once. An attempt counts only if the
     closer then discharges every goal it left; otherwise the invariant was too
     weak (or the goal is false) and the attempt is rolled back before the next
     backend.
  4. The closer tries the κ-free goals (split-off clauses and `zap`'s leftover
     leaves), keeping what it cannot close.

  Every step runs under the same heartbeat budget, and any failure — including
  heartbeat exhaustion and `maxRecDepth` — restores the state from before that
  step. When no backend succeeds, the κ goal is left as `zap` produced it, minus
  its κ-free clauses, so the proof can continue by hand. Interrupts propagate. -/

namespace Flex.Portfolio

inductive Backend where
  | fix | spacer | eldarica

instance : ToString Backend where
  toString
    | .fix => "fix"
    | .spacer => "spacer"
    | .eldarica => "eldarica"

/-- The default backends, in the order they are tried. -/
def Backend.all : List Backend := [.fix, .spacer, .eldarica]

/-- Knobs that are not syntax arguments of `flex`. -/
structure Config where
  /-- Eliminate acyclic κs with `zap` before calling the backends. -/
  zap : Bool := true
  /-- Heartbeats (in thousands, like `maxHeartbeats`) for each step: `zap`, each
  backend attempt with its closer, and closing the κ-free goals. Zero splits
  what remains at entry equally among the steps, keeping one share for the rest
  of the proof. -/
  heartbeats : Nat := 0
  /-- Wall-clock seconds for each external CHC solver call. -/
  solverTimeout : Nat := 30
  /-- Try the closer on the κ-free goals: split-off clauses and `zap`'s leftover
  leaves. -/
  closeLeaves : Bool := true
  /-- Move clauses that mention no κ out of each κ goal before the backends run,
  so only clauses that depend on the invariant must be closed to accept it. -/
  splitFree : Bool := true
  /-- Scraping limits for `fix`; the mode comes from `scrape := …`. -/
  scrapeLimits : PAScrapeLimits := {}

/-- Backend inputs shared by every κ goal. -/
structure Setup where
  config : Config := {}
  backends : List Backend := Backend.all
  scrape : PAScrapeConfig := {}
  facts : Flex.CHC.Facts.Config := {}
  /-- Replaces `flex_discharge` as the closer when present. -/
  closer : Option (TSyntax `tactic) := none

/-- Raw heartbeats for every step, fixed at entry so each step gets the same
amount. Zero means unlimited. -/
private def stepBudget (setup : Setup) : TacticM Nat := do
  let configured := setup.config.heartbeats * 1000
  if (← getMaxHeartbeats) == 0 then return configured
  let remaining ← getRemainingHeartbeats
  if configured != 0 then return max 1 (min configured remaining)
  let steps := (if setup.config.zap then 1 else 0) + setup.backends.length +
    (if setup.config.closeLeaves then 1 else 0)
  return max 1 (remaining / (steps + 1))

/-- Run `act` with its own heartbeat budget, capped by what the caller has left. -/
private def withBudget (budget : Nat) (act : TacticM α) : TacticM α := do
  let mut limit := budget
  if (← getMaxHeartbeats) != 0 then
    limit := max 1 (min limit (← getRemainingHeartbeats))
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := limit }) <|
    Core.withCurrHeartbeats act

/-- Run `act`; on any failure, including runtime limits, restore the entry state
and return the error. Interrupts propagate after restoring. -/
private def guarded (act : TacticM α) : TacticM (Except MessageData α) := do
  let saved ← Tactic.saveState
  tryCatchRuntimeEx (.ok <$> act) fun error => do
    Flex.CHC.restoreTermState saved.term
    set saved.tactic
    if error.isInterrupt then throw error
    return .error error.toMessageData

/-- Whether the goal is an `∃ κ, …` over a predicate. -/
private def isKGoal (goal : MVarId) : MetaM Bool := goal.withContext do
  let type ← whnf (← instantiateMVars (← goal.getType))
  let .app (.app (.const ``Exists _) α) _ := type | return false
  forallTelescopeReducing α fun _ body => return body.isProp

/-! ### Separating κ-free clauses

  `∀`/`→` distribute over `∧`, so `∃ κs, body` follows from `∃ κs, K` and `F`,
  where `F` collects the clauses mentioning no κ (in hypotheses or conclusion)
  and `K` the rest. A clause under a κ-mentioning hypothesis stays in `K`.
  `True` marks an empty side. -/

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

/-- Close what the closer can, keeping the rest. A user closer runs per goal and
must close it. -/
private def close (closer : Option (TSyntax `tactic)) : TacticM Unit := do
  let some tac := closer | Flex.Automation.discharge
  let mut remaining := #[]
  for goal in ← getGoals do
    if ← goal.isAssigned then continue
    setGoals [goal]
    if let .error _ ← guarded do
        evalTactic tac
        unless (← getGoals).isEmpty do throwError "closer left goals" then
      remaining := remaining.push goal
  setGoals remaining.toList

private def runBackend (setup : Setup) : Backend → TacticM Unit
  | .fix =>
    -- The defaults of a bare `fix`.
    fixImpl proveLeaf setup.scrape (some Flex.Automation.proofOracle)
      (synthOracle := some Flex.Automation.synthOracle)
  | .spacer => chc .spacer flex.spacer.executable
  | .eldarica => chc .eldarica flex.eldarica.executable
where
  chc (backend : Flex.CHC.Backend) (executable : Lean.Option String) : TacticM Unit := do
    Flex.CHC.solverTactic {
      backend
      executable := some (executable.get (← getOptions))
      timeoutMs := setup.config.solverTimeout * 1000 } setup.facts

/-- Try each backend on a κ goal; keep the first that, with the closer, leaves
nothing. Returns whether one did, plus a note per failed attempt. -/
private def solveKGoal (setup : Setup) (budget : Nat) (goal : MVarId) :
    TacticM (Option Backend × Array MessageData) := do
  let mut notes := #[]
  for backend in setup.backends do
    setGoals [goal]
    let attempt ← guarded <| withBudget budget do
      runBackend setup backend
      close setup.closer
      let left := (← getGoals).length
      unless left == 0 do
        throwError "{left} goal(s) left after closing; the invariant is too weak \
          or the goal is not provable"
    match attempt with
    | .ok () => return (some backend, notes)
    | .error error => notes := notes.push m!"{backend}: {error}"
  return (none, notes)

def flexImpl (setup : Setup) : TacticM Unit := focus do
  let budget ← stepBudget setup
  let mut notes : Array MessageData := #[]
  -- Without κs there is nothing for `zap` to do; it would only fail.
  if setup.config.zap && (← isKGoal (← getMainGoal)) then
    if let .error error ← guarded (withBudget budget (zapImpl emitStrategy)) then
      notes := notes.push m!"zap failed, continuing on the original goal: {error}"
  -- Clauses that mention no κ cannot tell a weak invariant from a strong one.
  let mut goals := #[]
  let mut splitGoals : Array MVarId := #[]
  for goal in ← getGoals do
    if setup.config.splitFree && !(← goal.isAssigned) && (← isKGoal goal) then
      match ← guarded (separateFree goal) with
      | .ok (some (kGoal, fGoal)) =>
        goals := goals.push kGoal |>.push fGoal
        splitGoals := splitGoals.push kGoal
        continue
      | .ok none => pure ()
      | .error error => notes := notes.push m!"splitting off κ-free clauses failed: {error}"
    goals := goals.push goal
  let mut remaining := #[]
  let mut leaves := #[]
  for goal in goals do
    if ← goal.isAssigned then continue
    unless ← isKGoal goal do
      leaves := leaves.push goal
      continue
    let (solved, failures) ← solveKGoal setup budget goal
    notes := notes ++ failures
    match solved with
    | some backend => notes := notes.push m!"{backend} closed a κ goal"
    | none =>
      let split := if splitGoals.contains goal then " (minus its κ-free clauses)" else ""
      notes := notes.push m!"no backend closed the κ goal; left as after zap{split}"
      remaining := remaining.push goal
  -- Closing the κ-free goals is a single step: they share one budget.
  if setup.config.closeLeaves && !leaves.isEmpty then
    let (rest, failures) ← withBudget budget do
      let mut rest := #[]
      let mut failures := #[]
      for goal in leaves do
        setGoals [goal]
        if let .error error ← guarded (close setup.closer) then
          failures := failures.push m!"closer on a κ-free goal: {error}"
        rest := rest ++ (← getGoals)
      return (rest, failures)
    leaves := rest
    notes := notes ++ failures
  setGoals (remaining ++ leaves).toList
  unless notes.isEmpty do
    logInfo (MessageData.joinSep (m!"flex:" :: notes.toList.map (m!"  " ++ ·)) "\n")

end Flex.Portfolio

private declare_config_elab elabFlexConfig Flex.Portfolio.Config

declare_syntax_cat flexBackend
syntax "fix" : flexBackend
syntax "spacer" : flexBackend
syntax "eldarica" : flexBackend

/-- `zap`, then solve the cyclic κs with `fix`, `spacer`, or `eldarica`, accepting
a backend only if the closer then proves every clause that mentions a κ. Clauses
that mention no κ become separate goals for the closer. On failure the κ goal is
left as `zap` produced it, minus those clauses.

`backends`: which backends to try, in order (default `[fix, spacer, eldarica]`).
`scrape` / `defs`: `fix`'s qualifier scraping (off by default); `defs` also
supplies equations to the CHC backends. `lemmas`: proved facts for the CHC backends.
`closer`: replaces `flex_discharge`; it must close a goal to count.
`config`: a `Flex.Portfolio.Config`, e.g.
`(config := { heartbeats := 100000, solverTimeout := 10, zap := false })`. -/
syntax "flex" (atomic("(" &"backends" ":=") "[" flexBackend,* "]" ")")?
  (atomic("(" &"scrape" ":=") ident ")")?
  (atomic("(" &"defs" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"lemmas" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"closer" ":=") tacticSeq ")")?
  (atomic("(" &"config" ":=") term ")")? : tactic

elab_rules : tactic
  | `(tactic| flex $[(backends := [$backends:flexBackend,*])]? $[(scrape := $mode:ident)]?
      $[(defs := [$defs:ident,*])]? $[(lemmas := [$lemmas:ident,*])]?
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
    let mode ← parseScrapeMode "flex" mode
    let closer ← closer.mapM fun tac => `(tactic| ($tac:tacticSeq))
    Flex.Portfolio.flexImpl {
      config, backends, closer
      scrape := { config.scrapeLimits with mode, defs }
      facts := { lemmas, defs } }
