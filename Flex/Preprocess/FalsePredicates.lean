import Lean

open Lean Meta

namespace Flex.Preprocess

private theorem exists_forced_false
  (C : Prop → Prop) (forced : ∀ p, C p → ¬p)
  : (∃ p, C p) ↔ C False := by
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

end Flex.Preprocess
