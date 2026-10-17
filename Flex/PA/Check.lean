import Lean
import Aesop
import Flex.Tactic.Utils

open Lean Meta Elab Tactic

/-- A PA query returns evidence on success and `none` on failure/unknown.
    Keeping this per invocation avoids changing other proofs' oracle settings. -/
abbrev PAOracle := Expr → TermElabM (Option Expr)

initialize Lean.registerTraceClass `flex.oracle

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

/-- The default tactic oracle used by PA, before any per-call fallback.
    No `aesop`: it can hit `maxRecDepth` (uncatchable) and over-weakens solutions. -/
syntax "pa_oracle" : tactic
macro_rules
  | `(tactic| pa_oracle) => `(tactic| first | omega | grind | (constructor <;> grind))

/-- Introduce a query's binders and run `tac` in an isolated metavariable scope.
    Reject failure and remaining goals; admitted evidence requires `trust`.
    Named axioms retain their ordinary Lean semantics. -/
def proveLeafWith (tac : TSyntax `tactic) (goal : Expr)
    (trust : Bool := false) : TermElabM (Option Expr) :=
  withSilencedMessages <| withNewMCtxDepth do
    let saved ← saveState
    let mvar ← mkFreshExprMVar (some goal) (kind := .syntheticOpaque)
    try
      let goals ← Tactic.run mvar.mvarId! do
        evalTactic (← `(tactic| intros))
        evalTactic tac
      if !goals.isEmpty then
        saved.restore
        trace[flex.oracle] "oracle left subgoals: {tac}"
        return none
      let proof   ← instantiateMVars mvar
      -- No goals left is not enough: `constructor <;> grind` hides unsolved
      -- subgoals behind `sorry`.
      if (!trust && proof.hasSorry) || proof.hasExprMVar then
        saved.restore
        trace[flex.oracle] "oracle returned incomplete evidence: {tac}"
        return none
      return some proof
    catch e =>
      saved.restore
      trace[flex.oracle] "oracle failed: {tac}\n{e.toMessageData}"
      return none

/-- Prove one qualifier `q(x̄)` with the PA oracle and return the proof term.
    Used by `walkPAProof` to build the certificate, and by `checkExprVC` on
    whole clauses. `proveLeafWith` introduces any remaining binders. -/
def proveLeaf (goal : Expr) : TermElabM (Option Expr) := do
  proveLeafWith (← `(tactic| pa_oracle)) goal

/-- Try the existing Lean oracle first, then an optional imported tactic.
    `trust` permits admitted evidence from that fallback (e.g. an SMT backend
    without reconstruction). Such results retain their backend's trust model. -/
def withPAFallback (tac : TSyntax `tactic) (trust : Bool := false) : PAOracle :=
  fun goal => do
    if let some proof ← proveLeaf goal then return some proof
    let result ← proveLeafWith tac goal trust
    trace[flex.oracle] "fallback accepted={result.isSome}: {tac}"
    return result

/-- Prefer an external oracle, falling back to Lean on failure/unknown.
    Used by the independent `synth` and `proof` options of `fix`. -/
def withPAPriority (tac : TSyntax `tactic) (trust : Bool := false) : PAOracle :=
  fun goal => do
    if let some proof ← proveLeafWith tac goal trust then return some proof
    proveLeaf goal

/-- Can the oracle establish the whole clause `prop`? -/
def checkExprVC (prop : Expr) (oracle : PAOracle := proveLeaf) : TermElabM Bool := do
  return (← oracle prop).isSome

/-- Sat-guard: is the clause body contradictory? The caller has already
    replaced the head with `False` (`specializeClauseAsNeg`), so this is just
    `checkExprVC` on that clause. -/
def checkExprUnsat (propWithFalseConclusion : Expr) (oracle : PAOracle := proveLeaf)
    : TermElabM Bool :=
  checkExprVC propWithFalseConclusion oracle
