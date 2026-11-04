import Lean
import Flex.Core

open Lean Meta Elab Tactic

-- Creates a proof for `∃ x : α, p x`
def mkExistsIntro (α predLam w proof : Expr) : MetaM Expr := do
  let u ← getLevel α
  return mkApp4 (mkConst ``Exists.intro [u]) α predLam w proof

-- Creates a proof for `a ∧ b`
def mkAndIntro (a b ha hb : Expr) : Expr :=
  mkApp4 (mkConst ``And.intro) a b ha hb

-- Creates a left-injection proof for `a ∨ b`
def mkOrInl (a b h : Expr) : Expr :=
  mkApp3 (mkConst ``Or.inl) a b h

-- Creates right-injection proof for `a ∨ b`
def mkOrInr (a b h : Expr) : Expr :=
  mkApp3 (mkConst ``Or.inr) a b h

-- Creates a proof for `x = x`
def mkEqRefl (ty x : Expr) : MetaM Expr := do
  let u ← getLevel ty
  return mkApp2 (mkConst ``Eq.refl [u]) ty x

/-
  Build a proof of an Eq / And-of-Eqs / True / False expression.
  Eq leaves auto-discharge via `isDefEq` when LHS/RHS are syntactically
  equal up to defeq (the common case: every eq comes from `zᵢ = aᵢ` where
  both sides reduce to the same value-binder fvar). Non-rfl eqs and
  `False` leaves become residual mvars.
-/
partial def buildEqProof
  (e : Expr)
  (residualOut : IO.Ref (Array MVarId)) : MetaM Expr := do

    if e.isConstOf ``True then return mkConst ``True.intro

    else if let some (p, q) := e.and? then
      let pProof ← buildEqProof p residualOut
      let qProof ← buildEqProof q residualOut
      return mkAndIntro p q pProof qProof

    else if e.isAppOfArity ``Eq 3 then
      let ty  := e.appFn!.appFn!.appArg!
      let lhs := e.appFn!.appArg!
      let rhs := e.appArg!
      let isRfl ←
        try
          withNewMCtxDepth (isDefEq lhs rhs)
        catch _ =>
          pure false
      if isRfl then mkEqRefl ty rhs
      else
        let m ← mkFreshExprMVar (some e) (kind := .syntheticOpaque)
        residualOut.modify (·.push m.mvarId!)
        return m
    else
      let m ← mkFreshExprMVar (some e) (kind := .syntheticOpaque)
      residualOut.modify (·.push m.mvarId!)
      return m
