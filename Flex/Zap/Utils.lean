import Lean
import Flex.Core

open Lean Meta Elab Tactic

private theorem exists_forced_false (C : Prop → Prop)
    (forced : ∀ p, C p → ¬p) : (∃ p, C p) ↔ C False := by
  constructor
  · rintro ⟨p, h⟩
    have eq : p = False := propext ⟨forced p h, False.elim⟩
    simpa only [eq] using h
  · intro h
    exact ⟨False, h⟩

/-- Find an unconditional `p → False` conjunct, including under witness binders.
Guarded implications and quantifiers over possibly empty types do not suffice. -/
private partial def forcedFalseProof? (p type proof : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  if type.isForall && type.bindingDomain! == p && type.bindingBody!.isConstOf ``False then
    return some proof
  if let some (left, right) := type.and? then
    if let some found ← forcedFalseProof? p left (← mkAppM ``And.left #[proof]) then
      return some found
    return ← forcedFalseProof? p right (← mkAppM ``And.right #[proof])
  if type.isAppOfArity ``Exists 2 then
    let domain := type.getArg! 0
    let predicate := type.getArg! 1
    return ← withLocalDeclD `witness domain fun x =>
      withLocalDeclD `body (predicate.beta #[x]) fun h => do
        let some found ← forcedFalseProof? p (predicate.beta #[x]) h | return none
        return some (← mkAppM ``Exists.elim #[proof, ← mkLambdaFVars #[x, h] found])
  if type.isForall then
    if !type.bindingBody!.hasLooseBVars && !(← isProp type.bindingDomain!) then
      let witness? ← observing? (mkDefault type.bindingDomain!)
      if let some witness := witness? then
        return ← forcedFalseProof? p type.bindingBody! (mkApp proof witness)
  return none

private partial def inlineFalsePredicatesImpl (input : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf input
  unless type.isAppOfArity ``Exists 2 do return (input, mkApp (mkConst ``Iff.rfl) input)
  let domain := type.getArg! 0
  let predicate := type.getArg! 1
  let name := if predicate.isLambda then predicate.bindingName! else `predicate
  withLocalDeclD name domain fun p => do
    let body := predicate.beta #[p]
    if domain.isProp then
      let forced? ← withLocalDeclD `body body fun h => do
        let some proof ← forcedFalseProof? p body h | return none
        return some (← mkLambdaFVars #[p, h] proof)
      if let some forced := forced? then
        let instantiated := predicate.beta #[mkConst ``False]
        let (result, rest) ← inlineFalsePredicatesImpl instantiated
        let step ← mkAppM ``exists_forced_false #[predicate, forced]
        return (result, ← mkAppM ``Iff.trans #[step, rest])
    let (body', proof) ← inlineFalsePredicatesImpl body
    if body' == body then return (input, mkApp (mkConst ``Iff.rfl) input)
    let predicate' ← mkLambdaFVars #[p] body'
    return (mkApp2 (mkConst ``Exists [← getLevel domain]) domain predicate',
      ← mkAppM ``exists_congr #[← mkLambdaFVars #[p] proof])

/-- Inline existential propositions forced to `False`, with an equivalence proof.
The decision uses their clauses, never the predicate's name. -/
def inlineFalsePredicates (input : Expr) : MetaM (Expr × Expr) := withNewMCtxDepth do
  let (result, proof) ← inlineFalsePredicatesImpl input
  return (← instantiateMVars result, ← instantiateMVars proof)

/--
  Replace every MVar reference in `e` whose mvarId is in `subst` with the
  matching expression (typically a fvar). Used to swap cyclic-κ-mvars in
  `curr` for the corresponding ∃-binder fvars so the result can be
  abstracted into a new ∃-chain.

  Example:

1. Takes ∃ κₓ κₐ: T, P(κₓ, κₐ)
2. Turns it into one with FVar:
    Free Vars: [fκₓ, fκₐ]
    P(fκₓ, fκₐ)
3. The core fusion engine works on MVars instead — FVars are scope-bound,
  so if an acyclic κ's solution references a cyclic κ, that cyclic-κ-fvar
  would escape its introducing scope and break elaboration. MVars live
  in the global MetavarContext and don't have this problem.
4. Substitute fvars → fresh mvars, stashing the correspondence:
    Pairs:   [(?mκ_cyc, fκ_cyc), (?mκ_acy, fκ_acy)]
    Body:    P(?mκ_cyc, ?mκ_acy)
5. Solve for ?mκ_acy (acyclic). Its solution may reference ?mκ_cyc —
  that's fine, ?mκ_cyc is global and the unifier will resolve it later.
6. Residual:
    Body:    P'(?mκ_cyc)        -- ?mκ_acy is now assigned
7. ← THIS FUNCTION: feed the stashed pairs as `subst` to swap MVars → FVars:
    Body:    P'(fκ_cyc)
8. Abstract fκ_cyc into ∃:
    ∃ κ : T, P'(κ)
-/
def replaceKMvarsWithFvars
  (subst : List (MVarId × Expr)) --
  (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.isMVar then
      subst.findSome? fun (m, fv) =>
        if m == sub.mvarId! then some fv else none
    else none

-- Is `e` *logically* ⊥? Sees through `∧` (⊥ if either side is ⊥), `∃` (⊥ if
-- the body is ⊥), and `∨` (⊥ only if BOTH branches are ⊥). This recognises an
-- all-dead Or-subtree like `False ∨ False` as ⊥ even though it is not the
-- literal constant `False` — the paper works modulo this equivalence (`σ̂`
-- keeps ⊥-disjuncts, and `g ∧ ⊥ ≡ ⊥` is what annihilates κ-uses in σ̂).
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

-- simplifyAndExists — collapse `_ ∧ ⊥ / ⊥ ∧ _ → False`, `∃ x, ⊥ → False`,
-- `True ∧ X → X`, but DO NOT collapse Or-nodes (only recurse into branches).
-- `⊥` here is `isLogicallyFalse`, so a consumer-clause branch like
-- `(κy y x) ∧ (∃ ν, (ν=y+1 ∧ False) ∨ (… ∧ False))` collapses to False —
-- dropping the dead κ-reference — while a live Or-branch (one that reaches a
-- κ-head) is preserved, keeping the goal's And-tree ↔ sol's Or-tree mirror.
partial def simplifyAndExists (e : Expr) : Expr :=
  if e.isAppOfArity ``And 2 then
    let l := simplifyAndExists (e.appFn!.appArg!)
    let r := simplifyAndExists (e.appArg!)
    if isLogicallyFalse l || isLogicallyFalse r then mkConst ``False
    else if l.isConstOf ``True then r
    else if r.isConstOf ``True then l
    else mkApp2 (mkConst ``And) l r
  else if e.isAppOfArity ``Or 2 then
    -- Recurse into Or branches but keep the Or-node — path-mirror requires
    -- positional preservation. Branches may collapse to False internally;
    -- that's the desired "dead branch" shape.
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

-- Checks whether the goal `e` Expr has form `?κ a₁ a₂ .. aₙ`
def kHead? (kLams : List (KVar × Expr)) (goal : Expr) :
    Option (KVar × Expr × Array Expr) :=
  let fn := goal.getAppFn
  if fn.isMVar then
    let filtered := kLams.find? (fun (κ, _) => κ.mvarId == fn.mvarId!)
    filtered.map (fun (κ, lam) => (κ, lam, goal.getAppArgs))
  else none
