import Lean
import Flex.Core
import Flex.Zap.Utils
import Flex.Zap.Nav

open Lean Meta Elab

/-- Type describing the leafHandler for `cert`.
  Gets the κ, the σ-instantiated body, and binders / guards / ∨-path info.
  Then, constructs the proof and returns. -/
abbrev LeafHandler :=
  KVar
  → (lamBody : Expr)
  → (binders guards : List (Name × Expr × FVarId))
  → (orPath : List Bool)
  → TermElabM Expr

/-- Zap's leaf: a proof term from `nav`. Drops the above-LCA prefix first,
    since the LCA-scoped σ̂ folded it into κ-params. -/
def emitLeaf (prefixInfo : Std.HashMap MVarId (Nat × Nat × Nat))
    (residualOut : IO.Ref (Array MVarId)) : LeafHandler :=
  fun κ lamBody binders guards orPath => do
    let (nB, nG, nOr) := prefixInfo.getD κ.mvarId (0, 0, 0)
    nav lamBody (binders.drop nB) (guards.drop nG) (orPath.drop nOr) residualOut

/-- `Cert` (paper Fig. 12): walk the original constraint `goal` in lockstep
    with `hCprime`, a proof of the reduced constraint `c′`, and produce a proof
    of `goal`. `c′` differs from `goal` only at κ-applications, so at every
    `∀` / `∧` the matching piece of `hCprime` is transferred; at a
    head-acyclic-κ leaf `hCprime` is `True` and `leaf` (e.g. `emitLeaf`, which
    runs `nav`) rebuilds a proof of `σ̂(t)` instead. -/
partial def cert
    (leaf : LeafHandler)
    (kLams : List (KVar × Expr))
    (goal  : Expr)
    (hCprime : Expr)
    (binders guards : List (Name × Expr × FVarId))
    (orPath : List Bool) :
    TermElabM Expr := do
  -- (a) Head-acyclic-κ leaf → whatever `leaf` decides.
  if let some (κLeaf, lam, args) := kHead? kLams goal then
    return ← leaf κLeaf (lam.beta args) binders guards orPath
  -- (b) ∀ — intro fv, beta-apply hCprime to fv, recurse, λ-wrap.
  if goal.isForall then
    let dom := goal.bindingDomain!
    let name := goal.bindingName!
    let bi := goal.bindingInfo!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    return ← withLocalDecl name bi dom fun fv => do
      let body := goal.bindingBody!.instantiate1 fv
      let hCprime' := mkApp hCprime fv
      let inner ←
        if domSort.isProp then
          cert leaf kLams body hCprime' binders
            (guards ++ [(name, dom, fv.fvarId!)]) orPath
        else
          cert leaf kLams body hCprime'
            (binders ++ [(name, dom, fv.fvarId!)]) guards orPath
      mkLambdaFVars #[fv] inner
  -- (c) ∧ — project hCprime via And.left / And.right, recurse, And.intro.
  if let some (l, r) := goal.and? then
    let hL ← mkAppM ``And.left  #[hCprime]
    let hR ← mkAppM ``And.right #[hCprime]
    let pL ← cert leaf kLams l hL binders guards (orPath ++ [false])
    let pR ← cert leaf kLams r hR binders guards (orPath ++ [true])
    return mkAndIntro l r pL pR
  -- (d) Anything else (non-κ atom OR cyclic-κ-head app) — direct transfer.
  return hCprime
