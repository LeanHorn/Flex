import Lean
import Aesop
import Flex.Tactic.Utils
import Flex.Tactic.Oracles.Stats

open Lean Meta Elab Tactic

/-- A PA query returns evidence on success and `none` on failure/unknown.
    Keeping this per invocation avoids changing other proofs' oracle settings. -/
abbrev PAOracle := Expr → TermElabM (Option Expr)

initialize Lean.registerTraceClass `flex.oracle

/-- Run `k` and throw away every message it logged, whether it succeeded or
    not. Needed because `grind`/`omega` report failures through the message
    log, not as exceptions, so `try`/`first` alone would leak them. -/
def withSilencedMessages {α} (k : TermElabM α) : TermElabM α := do
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
  Flex.OracleStats.reportCall ((← getOptions).getBool `flex.benchOracles) "lean"
    (fun r => if r.isSome then "proved" else "refuted") do
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

/-! ## Synthesis oracles: one call per clause visit

  Houdini weakening asks, per clause visit, whether the hypotheses are
  contradictory (the clause with head `False`) and then whether each candidate
  holds. These queries share the clause's binders and hypotheses; only the
  head differs. A `PASynthOracle` receives them together, so a backend can
  translate the shared part once (see `flex_auto`). Tactic oracles answer them
  one at a time via `PASynthOracle.ofOracle`. Synthesis needs verdicts only;
  proofs are rebuilt by the proof oracle. -/

/-- `checkClause vacuity candidates` returns `none` if `vacuity` (the clause
    with head `False`) is valid, leaving the candidates unchecked; otherwise
    whether each candidate VC is valid. -/
structure PASynthOracle where
  checkClause : (vacuity : Expr) → (candidates : Array Expr) → TermElabM (Option (Array Bool))

namespace PASynthOracle

/-- One oracle call per query, in the order weakening used to issue them. -/
def ofOracle (oracle : PAOracle) : PASynthOracle where
  checkClause vacuity candidates := do
    if (← oracle vacuity).isSome then return none
    return some (← candidates.mapM fun vc => return (← oracle vc).isSome)

/-- Lean first, external on whatever Lean does not establish (`withPAFallback`).
    The external oracle still decides vacuity when Lean cannot, as before. -/
def fallback (ext : PASynthOracle) (lean : PAOracle := proveLeaf) : PASynthOracle where
  checkClause vacuity candidates := do
    if (← lean vacuity).isSome then return none
    let leanOk ← candidates.mapM fun vc => return (← lean vc).isSome
    let failed := (List.range candidates.size).toArray.filter (!leanOk[·]!)
    let some extOk ← ext.checkClause vacuity (failed.map (candidates[·]!)) | return none
    let mut ok := leanOk
    for (i, extI) in failed.zip extOk do
      ok := ok.set! i extI
    return some ok

end PASynthOracle

/-- Builds a batched synthesis oracle for one tactic (given with `trust`), or
    `none` to use per-query calls. Registered per syntax kind by backends. -/
abbrev PASynthBuilder := Syntax → Bool → TermElabM (Option PASynthOracle)

initialize synthBuildersRef : IO.Ref (Array (SyntaxNodeKind × PASynthBuilder)) ← IO.mkRef #[]

def registerPASynthBuilder (kind : SyntaxNodeKind) (builder : PASynthBuilder) : IO Unit :=
  synthBuildersRef.modify (·.push (kind, builder))

/-- The single tactic of a tactic sequence, if it has exactly one. -/
private def singleTactic? (seq : Syntax) : Option Syntax :=
  let inner := seq[0]
  let tacs :=
    if inner.getKind == ``Parser.Tactic.tacticSeq1Indented then inner[0].getSepArgs
    else if inner.getKind == ``Parser.Tactic.tacticSeqBracketed then inner[1].getSepArgs
    else #[]
  if tacs.size == 1 then tacs[0]? else none

/-- Synthesis oracle for an external tactic sequence: a registered batched
    backend when `seq` is a single tactic of a registered kind, otherwise one
    `proveLeafWith` call per query. -/
def PASynthOracle.ofTactic (seq : TSyntax ``Parser.Tactic.tacticSeq) (trust : Bool)
    : TermElabM PASynthOracle := do
  if let some tac := singleTactic? seq then
    for (kind, builder) in ← synthBuildersRef.get do
      if tac.getKind == kind then
        if let some o ← builder tac trust then return o
  let tac ← `(tactic| ($seq:tacticSeq))
  return .ofOracle (proveLeafWith tac · trust)
