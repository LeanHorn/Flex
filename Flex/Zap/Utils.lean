import Lean
import Flex.Core

open Lean Meta Elab Tactic

-- Solution cleanup.

/-- Recognize structurally false formulas under `∧`, `∨`, and `∃`. -/
partial def isLogicallyFalse (e : Expr) : Bool :=
  if e.isConstOf ``False then true
  else if e.isAppOfArity ``And 2 then
    isLogicallyFalse e.appFn!.appArg! || isLogicallyFalse e.appArg!
  else if e.isAppOfArity ``Or 2 then
    isLogicallyFalse e.appFn!.appArg! && isLogicallyFalse e.appArg!
  else if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam _ _ b _ => isLogicallyFalse b
    | _            => false
  else false

/-- Simplify `True`/`False` conjunctions and false existential bodies.
Preserve disjunction nodes so certification retains the original branch positions. -/
partial def simplifyAndExists (e : Expr) : Expr :=
  if e.isAppOfArity ``And 2 then
    let l := simplifyAndExists (e.appFn!.appArg!)
    let r := simplifyAndExists (e.appArg!)
    if isLogicallyFalse l || isLogicallyFalse r then mkConst ``False
    else if l.isConstOf ``True then r
    else if r.isConstOf ``True then l
    else mkApp2 (mkConst ``And) l r
  else if e.isAppOfArity ``Or 2 then
    -- Keep branch positions aligned with the certificate traversal.
    let l := simplifyAndExists (e.appFn!.appArg!)
    let r := simplifyAndExists (e.appArg!)
    mkApp2 (mkConst ``Or) l r
  else if e.isAppOfArity ``Exists 2 then
    let ty := e.appFn!.appArg!
    let body := e.appArg!
    let univrs := e.getAppFn.constLevels!
    match body with
    | .lam n t b bi =>
      let b' := simplifyAndExists b
      if isLogicallyFalse b' then mkConst ``False
      else mkApp2 (mkConst ``Exists univrs) ty (.lam n t b' bi)
    | _ => e
  else if e.isForall then
    match e with
    | .forallE n t b bi =>
      let t' := simplifyAndExists t
      let b' := simplifyAndExists b
      .forallE n t' b' bi
    | _ => e
  else e

-- Certificate helpers.

/-- Replace metavariables in `e` with the expressions mapped by `subst`.
Zap uses this to restore cyclic predicate locals before rebuilding binders and proofs. -/
def replaceKMvarsWithFvars (subst : List (MVarId × Expr)) (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.isMVar then
      subst.findSome? fun (m, fv) =>
        if m == sub.mvarId! then some fv else none
    else none

/-- Find a known predicate head and return its solution and arguments. -/
def kHead? (kLams : List (KVar × Expr)) (goal : Expr) :
    Option (KVar × Expr × Array Expr) :=
  let fn := goal.getAppFn
  if fn.isMVar then
    let filtered := kLams.find? (fun (κ, _) => κ.mvarId == fn.mvarId!)
    filtered.map (fun (κ, lam) => (κ, lam, goal.getAppArgs))
  else none
