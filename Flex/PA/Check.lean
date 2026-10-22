import Lean
import Aesop
import Flex.Tactic.Utils

open Lean Meta Elab Tactic

/-- Return type for oracle of PA.
    success if `proof` returned, or `none` if failure. -/
abbrev PAOracle := Expr → TermElabM (Option Expr)

/-- Synthesis decisions carry no proof and never enter a certificate. -/
inductive PASynthResult where
  | unknown (reason : String)
  | valid
  | invalid
  deriving BEq, Repr, Inhabited

/-- Check related candidate implications together, preserving their order. -/
abbrev PASynthOracle := Array Expr → TermElabM (Array PASynthResult)

/-- A failed proof attempt is unknown, not a counterexample. -/
def PAOracle.toSynth (oracle : PAOracle) : PASynthOracle := fun targets =>
  targets.mapM fun target => do
    return if (← oracle target).isSome then .valid else .unknown "proof search failed"

/-- The default tactic oracle used by PA, before any per-call fallback.
    No `aesop`: it can hit `maxRecDepth` (uncatchable) and over-weakens solutions. -/
syntax "pa_oracle" : tactic
macro_rules
  | `(tactic| pa_oracle) => `(tactic| first | omega | grind | (constructor <;> grind))

initialize Lean.registerTraceClass `flex.oracle

/-- Suppress messages from speculative PA checks,
    since failed attempts to prove candidate qualifiers
    would otherwise clutter the Infoview. -/
private def withSilencedMessages {α} (k : TermElabM α) : TermElabM α := do
  let saved ← Core.getMessageLog
  try
    k
  finally
    Core.setMessageLog saved

/-- Try to prove `goal` using `tac`, suppressing intermediate messages.
    Return `some proof` on success or `none` on failure. -/
def proveLeafWith
  (tac : TSyntax `tactic)
  (goal : Expr)
  : TermElabM (Option Expr) := do
    withSilencedMessages <| withNewMCtxDepth do
      let saved ← saveState
      try
        -- create a new meta-variable where will do the proof
        let mvar ← mkFreshExprMVar (some goal) (kind := .syntheticOpaque)
        let remainingGoals ← Tactic.run mvar.mvarId! do
          -- intro binders
          evalTactic (← `(tactic| intros))
          evalTactic tac
        -- check if remaining goals are fully done
        -- if not, consider failure
        if !remainingGoals.isEmpty then
          saved.restore
          return none
        -- extract the proof
        let proof ← instantiateMVars mvar
        -- Reject unresolved metavariables and explicit admissions.
        if proof.hasExprMVar || proof.hasSorry then
          saved.restore
          return none
        return some proof
      catch e =>
        saved.restore
        if e.isInterrupt then throw e
        return none

/-- Try to prove `goal` with the default PA oracle. -/
def proveLeaf (goal : Expr) : TermElabM (Option Expr) := do
  proveLeafWith (← `(tactic| pa_oracle)) goal

/-- Try the existing PA Lean oracle first, then the supplied tactic on failure. -/
def withPAFallback (tac : TSyntax `tactic) : PAOracle :=
  fun goal => do
    if let some proof   ← proveLeaf goal then return some proof
    let result          ← proveLeafWith tac goal
    trace[flex.oracle] "fallback accepted={result.isSome}: {tac}"
    return result

/-- Try `tac` first, then the default PA oracle. -/
def withPAPriority (tac : TSyntax `tactic) : PAOracle :=
  fun goal => do
    if let some proof ← proveLeafWith tac goal then return some proof
    proveLeaf goal

/-- Return whether the oracle proves `prop`. -/
def checkExprVC (prop : Expr) (oracle : PAOracle := proveLeaf) : TermElabM Bool := do
  return (← oracle prop).isSome

/-- Check a clause whose conclusion has been replaced with `False`. -/
def checkExprUnsat (clause : Expr) (oracle : PAOracle := proveLeaf)
    : TermElabM Bool :=
  checkExprVC clause oracle
