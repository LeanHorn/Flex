import Lean

import Flex.Core
import Flex.PA.Qualifier
import Flex.PA.Check
import Flex.Zap.Emit

open Lean Meta Elab Term Tactic

/-!
  ## Certifying Predicate Abstraction — the `glue`/`bridge` (paper §5)

  After weakening reaches the greatest inductive fixpoint `A*`
  (`solveFixpoint`), the cut κ-mvars are assigned their witness λ's
  (`σ_{A*}`). This file builds the §5 `glue` term: a proof of the body
  `c[σ_{A*}]` in which every κ-head leaf `κ(x̄)` is discharged by an
  `And.intro` over per-survivor oracle proofs, and every κ-free leaf is left
  as a residual obligation (a query of `c′`).

  Structurally `walkPAProof` mirrors Zap's `cert`
  (`Flex/Zap/Cert.lean`) — ∀↦λ, ∧↦`And.intro`, κ-free leaf↦residual
  mvar — differing only at the κ-head leaf, where Zap emits its strongest
  ∃-tree solution (`nav`) and PA emits the survivor conjunction
  (`emitPALeaf`). No binder/guard bookkeeping is needed: each survivor
  conjunct is an atom proved by the ambient-context oracle `proveLeaf`.
-/

/-- κ-head detector for the PA glue, analogous to `kHead?` but keyed by the PA
    assignment. If `goal` is `?κ a₁ … aₙ` for some κ recorded in `assign`,
    returns that κ, its surviving candidates, and the argument array. -/
def paHead?
    (assign : List (KVar × List (Expr × List Nat)))
    (goal : Expr) :
    Option (KVar × List (Expr × List Nat) × Array Expr) :=
  let fn := goal.getAppFn
  if fn.isMVar then
    (assign.find? (fun (κ, _) => κ.mvarId == fn.mvarId!)).map
      (fun (κ, survivors) => (κ, survivors, goal.getAppArgs))
  else none

/-- Fold `(conjunctType, proof)` pairs into one proof, mirroring `conjoinExprs`
    (`Flex/PA/Weaken.lean`) EXACTLY: left-nested `And`, `[]` ↦
    `True.intro`, `[p]` ↦ `p`. The result inhabits
    `conjoinExprs (pairs.map (·.1))`, i.e. the β-reduced witness body
    `σ_{A*}(κ)(x̄)` assigned to the κ-mvar — so the κ-head leaf typechecks. -/
def conjProofs : List (Expr × Expr) → Expr
  | []           => mkConst ``True.intro
  | [(_, p)]     => p
  | (e0, p0) :: rest =>
    (rest.foldl
      (fun (acc cur : Expr × Expr) =>
        let (accE, accP) := acc
        let (curE, curP) := cur
        (mkApp2 (mkConst ``And) accE curE, mkAndIntro accE curE accP curP))
      (e0, p0)).2

/-- Prove the survivor conjunction `⋀_{(q,ρ) ∈ survivors} q[ρ](args)` at a
    κ-head leaf. Each conjunct `q[ρ](args)` is built exactly as
    `specializeClauseForHead`'s headRepl (β-apply `q` at the chosen κ-slots) and
    discharged by the proof-returning oracle `proveLeaf` under the ambient
    context Γ; the proofs are then `And.intro`-folded in the SAME order and
    association as `conjoinExprs` (hence as the witness λ assigned to κ).

    Errors loudly if a survivor fails: at a true weakening fixpoint every
    survivor must re-prove, so a failure signals the glue oracle and the
    weakening oracle (`checkExprVC`) have diverged. -/
def emitPALeaf
    (κ : KVar)
    (survivors : List (Expr × List Nat))
    (args : Array Expr) :
    TermElabM Expr := do
  let pairs ← survivors.mapM fun (q, slots) => do
    let chosen : Array Expr := (slots.map fun i => args[i]!).toArray
    let φ ← Expr.instQualifier q chosen
    match ← proveLeaf φ with
    | some p => pure (φ, p)
    | none   =>
      throwError "pa_cert: oracle failed to prove survivor{indentExpr φ}\n\
        at head κ '{κ.name}' — weakening fixpoint and glue oracle disagree."
  return conjProofs pairs

/-- The §5 `glue`. Nav the body `goal` (with cut κ-mvars still SYNTACTICALLY
    present — never `instantiateMVars` it), emitting the bridge proof term:

    · κ-head leaf `?κ x̄`   → `emitPALeaf` (survivor conjunction via oracle)
    · ∀ (binder or guard)  → intro fvar, recurse, λ-wrap
    · ∧                    → recurse both sides, `And.intro`
    · κ-free leaf          → fresh residual mvar (a query collected into `c′`)

    A κ-head whose κ is NOT in `assign` is a non-cut κ — abort and tell the user
    to eliminate acyclic κ's with `fusion` first. Once the cut κ-mvars are
    assigned `σ_{A*}`, the emitted term inhabits `c[σ_{A*}]`; together with the
    `Exists.intro` scaffolding from `peelExistentialsAndIntro` it is the §5
    `bridge`, which the kernel re-checks. -/
partial def walkPAProof
    (assign : List (KVar × List (Expr × List Nat)))
    (goal : Expr)
    (residualOut : IO.Ref (Array MVarId)) :
    TermElabM Expr := do
  -- (a) κ-headed leaf — check before ∀/∧ since the leaf is an application.
  if let some (κ, survivors, args) := paHead? assign goal then
    return ← emitPALeaf κ survivors args
  -- A κ-mvar head not under PA (non-cut) — abort with guidance.
  if goal.getAppFn.isMVar then
    throwError "pa_cert: head metavariable{indentExpr goal.getAppFn}\nis not a \
      cut variable handled by PA. Eliminate acyclic κ's with `fusion` first."
  -- (b) ∀ (value binder or Prop guard) — intro, recurse, λ-wrap.
  if goal.isForall then
    let dom  := goal.bindingDomain!
    let name := goal.bindingName!
    let bi   := goal.bindingInfo!
    return ← withLocalDecl name bi dom fun fv => do
      let body  := goal.bindingBody!.instantiate1 fv
      let inner ← walkPAProof assign body residualOut
      mkLambdaFVars #[fv] inner
  -- (c) ∧ — split, recurse, And.intro.
  if let some (l, r) := goal.and? then
    let pL ← walkPAProof assign l residualOut
    let pR ← walkPAProof assign r residualOut
    return mkAndIntro l r pL pR
  -- (d) κ-free leaf — residual mvar (a query of c′). Created in the ambient
  --     LCtx, so it carries its context Γ (binders + guard hyps) as a goal.
  let m ← mkFreshExprMVar (some goal) (kind := .syntheticOpaque)
  residualOut.modify (·.push m.mvarId!)
  return m
