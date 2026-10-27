import Flex.Tactic.Tactics.Fusion
import Flex.Tactic.Tactics.Fix
import Flex.Tactic.Tactics.Eldarica

open Lean Meta Elab Tactic

/-! ## `flex` — `zap`, then a portfolio of invariant backends

  1. `zap` eliminates the acyclic κs. Without acyclic κs it only normalizes the
     goal; if it fails, `flex` continues on the original goal.
  2. Each remaining `∃ κ, …` goal is handed to the backends in order (default
     `fix`, `spacer`, `eldarica`). An attempt counts only if the closer then
     discharges *every* goal it left; otherwise the invariant was too weak (or
     the goal is false) and the attempt is rolled back before the next backend.
  3. `zap`'s κ-free leaf obligations are tried with the closer independently;
     unclosed ones are kept.

  Every attempt runs under its own heartbeat budget, and any failure —
  including heartbeat exhaustion and `maxRecDepth` — restores the state from
  before that attempt. When nothing works, the goals are left exactly as `zap`
  produced them, so the proof can continue by hand. Interrupts propagate. -/

namespace Flex.Portfolio

inductive Backend where
  | fix | spacer | eldarica
  deriving BEq, Inhabited

instance : ToString Backend where
  toString
    | .fix => "fix"
    | .spacer => "spacer"
    | .eldarica => "eldarica"

/-- Knobs that are not syntax arguments of `flex`. -/
structure Config where
  /-- Eliminate acyclic κs with `zap` before calling the backends. -/
  zap : Bool := true
  /-- Heartbeats (in thousands, like `maxHeartbeats`) for each step: `zap`, each
  backend attempt with its closer, and closing `zap`'s leaves. Zero splits what
  remains at entry equally among the steps, keeping one share for the rest of
  the proof. -/
  heartbeats : Nat := 0
  /-- Wall-clock seconds for each external CHC solver call. -/
  solverTimeout : Nat := 30
  /-- Try the closer on `zap`'s κ-free leaf obligations. -/
  closeLeaves : Bool := true
  /-- Scraping limits for `fix`; the mode comes from `scrape := …`. -/
  scrapeLimits : PAScrapeLimits := {}

/-- Backend inputs shared by every κ goal. -/
structure Setup where
  config : Config := {}
  backends : List Backend := [.fix, .spacer, .eldarica]
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
private def guarded (act : TacticM Unit) : TacticM (Option MessageData) := do
  let saved ← Tactic.saveState
  tryCatchRuntimeEx (do act; return none) fun error => do
    Flex.CHC.restoreTermState saved.term
    set saved.tactic
    if error.isInterrupt then throw error
    return some error.toMessageData

/-- Whether the goal is an `∃ κ, …` over a predicate. -/
private def isKGoal (goal : MVarId) : MetaM Bool := goal.withContext do
  let type ← whnf (← instantiateMVars (← goal.getType))
  let .app (.app (.const ``Exists _) α) _ := type | return false
  forallTelescopeReducing α fun _ body => return body.isProp

/-- Close what the closer can, keeping the rest. A user closer runs per goal and
must close it. -/
private def close (closer : Option (TSyntax `tactic)) : TacticM Unit := do
  let some tac := closer | Flex.Automation.discharge
  let mut remaining := #[]
  for goal in ← getGoals do
    if ← goal.isAssigned then continue
    setGoals [goal]
    let failure ← guarded do
      evalTactic tac
      unless (← getGoals).isEmpty do throwError "closer left goals"
    if failure.isSome then remaining := remaining.push goal
  setGoals remaining.toList

private def runBackend (setup : Setup) : Backend → TacticM Unit
  | .fix =>
    -- The defaults of a bare `fix`.
    fixImpl proveLeaf setup.scrape (some Flex.Automation.proofOracle)
      (synthOracle := some Flex.Automation.synthOracle)
  | .spacer => do
    Flex.CHC.solverTactic {
      backend := .spacer
      executable := some (flex.spacer.executable.get (← getOptions))
      timeoutMs := setup.config.solverTimeout * 1000 } setup.facts
  | .eldarica => do
    Flex.CHC.solverTactic {
      backend := .eldarica
      executable := some (flex.eldarica.executable.get (← getOptions))
      timeoutMs := setup.config.solverTimeout * 1000 } setup.facts

/-- Try each backend on a κ goal; keep the first that, with the closer, leaves
nothing. Returns whether one did, plus a note per failed attempt. -/
private def solveKGoal (setup : Setup) (budget : Nat) (goal : MVarId) :
    TacticM (Option Backend × Array MessageData) := do
  let mut notes := #[]
  for backend in setup.backends do
    setGoals [goal]
    let failure ← guarded <| withBudget budget do
      runBackend setup backend
      close setup.closer
      let left := (← getGoals).length
      unless left == 0 do
        throwError "{left} goal(s) left after closing; the invariant is too weak \
          or the goal is not provable"
    match failure with
    | none => return (some backend, notes)
    | some error => notes := notes.push m!"{backend}: {error}"
  return (none, notes)

def flexImpl (setup : Setup) : TacticM Unit := focus do
  let budget ← stepBudget setup
  let mut notes : Array MessageData := #[]
  if setup.config.zap then
    if let some error ← guarded (withBudget budget (zapImpl emitStrategy)) then
      notes := notes.push m!"zap failed, continuing on the original goal: {error}"
  let mut remaining := #[]
  for goal in ← getGoals do
    if ← goal.isAssigned then continue
    if ← isKGoal goal then
      let (solved, failures) ← solveKGoal setup budget goal
      notes := notes ++ failures
      match solved with
      | some backend => notes := notes.push m!"{backend} closed a κ goal"
      | none =>
        notes := notes.push m!"no backend closed the κ goal; left as after zap"
        remaining := remaining.push goal
    else if setup.config.closeLeaves then
      setGoals [goal]
      if let some error ← guarded (withBudget budget (close setup.closer)) then
        notes := notes.push m!"closer on a κ-free goal: {error}"
      remaining := remaining ++ (← getGoals)
    else
      remaining := remaining.push goal
  setGoals remaining.toList
  unless notes.isEmpty do
    logInfo (MessageData.joinSep (m!"flex:" :: notes.toList.map (m!"  " ++ ·)) "\n")

end Flex.Portfolio

private declare_config_elab elabFlexConfig Flex.Portfolio.Config

declare_syntax_cat flexBackend
syntax "fix" : flexBackend
syntax "spacer" : flexBackend
syntax "eldarica" : flexBackend

/-- `zap`, then solve the cyclic κs with `fix`, `spacer`, or `eldarica`, accepting
a backend only if the closer then proves every remaining goal. On failure the
goals are left as `zap` produced them.

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
      | none => pure [.fix, .spacer, .eldarica]
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
