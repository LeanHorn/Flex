import Lean
import Aesop
import Flex.Tactic.Utils

open Lean Meta Elab Tactic

/-- Run `k` and throw away every message it logged, whether it succeeded or
    not. Needed because `grind`/`omega` report failures through the message
    log, not as exceptions, so `try`/`first` alone would leak them. -/
private def withSilencedMessages {α} (k : TermElabM α) : TermElabM α := do
  let saved ← Core.getMessageLog
  try
    let r ← k
    Core.setMessageLog saved
    return r
  catch e =>
    Core.setMessageLog saved
    throw e

/-- The tactic oracle used by all of PA. Change it here only.
    No `aesop`: it can hit `maxRecDepth` (uncatchable) and over-weakens solutions. -/
syntax "pa_oracle" : tactic
macro_rules
  | `(tactic| pa_oracle) => `(tactic| first | omega | grind | (constructor <;> grind))

/-- Try to prove `goal` with `tac`. Returns the proof term, or `none` if the
    tactic failed or left anything unproved. -/
def proveLeafWith (tac : TSyntax `tactic) (goal : Expr) : TermElabM (Option Expr) :=
  withSilencedMessages do
    let mvar ← mkFreshExprMVar (some goal) (kind := .syntheticOpaque)
    try
      let goals   ← Tactic.run mvar.mvarId! (evalTactic tac)
      if !goals.isEmpty then return none
      let proof   ← instantiateMVars mvar
      -- No goals left is not enough: `constructor <;> grind` hides unsolved
      -- subgoals behind `sorry`.
      if proof.hasSorry || proof.hasExprMVar then return none
      return some proof
    catch _ =>
      return none

/-- Prove one qualifier `q(x̄)` with the PA oracle and return the proof term.
    Used by `walkPAProof` to build the certificate. The hypotheses are already
    in the local context, so no `intros` (unlike `checkExprVC`). -/
def proveLeaf (goal : Expr) : TermElabM (Option Expr) := do
  proveLeafWith (← `(tactic| pa_oracle)) goal

/-- Can the oracle prove the clause `prop`? Same check as `proveLeaf`, but
    the goal is a whole clause, so `intros` first. -/
def checkExprVC (prop : Expr) : TermElabM Bool := do
  return (← proveLeafWith (← `(tactic| (intros; pa_oracle))) prop).isSome

/-- Sat-guard: is the clause body contradictory? The caller has already
    replaced the head with `False` (`specializeClauseAsNeg`), so this is just
    `checkExprVC` on that clause. -/
def checkExprUnsat (propWithFalseConclusion : Expr) : TermElabM Bool :=
  checkExprVC propWithFalseConclusion
