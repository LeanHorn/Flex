import Lean

open Lean Meta

namespace Flex.Preprocess

private theorem existsFalse (α : Sort u) : (∃ _ : α, False) ↔ False :=
  ⟨fun ⟨_, h⟩ => h, False.elim⟩

private def unchanged (e : Expr) : Expr × Expr :=
  (e, mkApp (mkConst ``Iff.refl) e)

private def trans (a b c ab bc : Expr) : Expr :=
  if a == b then bc else mkApp5 (mkConst ``Iff.trans) a b c ab bc

private def rewriteEq (input middle proof result eq : Expr) : Expr × Expr :=
  (result, trans input middle result proof (mkApp3 (mkConst ``Iff.of_eq) middle result eq))

/-- One structural pass over logical connectives; theory expressions stay opaque. -/
partial def simplifyTrueFalse (input : Expr) : MetaM (Expr × Expr) := withIncRecDepth do
  let e := input.consumeMData.headBeta
  if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then
    let isAnd := e.isAppOfArity ``And 2
    let a := e.getArg! 0
    let b := e.getArg! 1
    if isAnd && (a.isConstOf ``False || b.isConstOf ``False) then
      let eq := if a.isConstOf ``False then mkApp (mkConst ``false_and) b else
        mkApp (mkConst ``and_false) a
      return rewriteEq e e (unchanged e).2 (mkConst ``False) eq
    if !isAnd && (a.isConstOf ``True || b.isConstOf ``True) then
      let eq := if a.isConstOf ``True then mkApp (mkConst ``true_or) b else
        mkApp (mkConst ``or_true) a
      return rewriteEq e e (unchanged e).2 (mkConst ``True) eq
    let (a', ha) ← simplifyTrueFalse a
    let (b', hb) ← if (isAnd && a'.isConstOf ``False) || (!isAnd && a'.isConstOf ``True) then
      pure (unchanged b) else simplifyTrueFalse b
    let changed := a != a' || b != b'
    if !changed && !a'.isConstOf ``True && !a'.isConstOf ``False &&
        !b'.isConstOf ``True && !b'.isConstOf ``False then return unchanged input
    let middle := mkApp2 (mkConst (if isAnd then ``And else ``Or)) a' b'
    let proof := if changed then
        mkApp6 (mkConst (if isAnd then ``and_congr else ``or_congr)) a a' b b' ha hb
      else (unchanged e).2
    let rules := if isAnd then
        #[(a'.isConstOf ``False, mkConst ``False, ``false_and, b'),
          (b'.isConstOf ``False, mkConst ``False, ``and_false, a'),
          (a'.isConstOf ``True, b', ``true_and, b'),
          (b'.isConstOf ``True, a', ``and_true, a')]
      else
        #[(a'.isConstOf ``True, mkConst ``True, ``true_or, b'),
          (b'.isConstOf ``True, mkConst ``True, ``or_true, a'),
          (a'.isConstOf ``False, b', ``false_or, b'),
          (b'.isConstOf ``False, a', ``or_false, a')]
    for (applies, result, lemma, arg) in rules do
      if applies then return rewriteEq e middle proof result (mkApp (mkConst lemma) arg)
    return (middle, proof)
  if e.isAppOfArity ``Not 1 then
    let a := e.appArg!
    let (a', ha) ← simplifyTrueFalse a
    let middle := mkApp (mkConst ``Not) a'
    let proof := if a == a' then (unchanged e).2 else
      mkApp3 (mkConst ``not_congr) a a' ha
    if a'.isConstOf ``True then
      return rewriteEq e middle proof (mkConst ``False) (mkConst ``not_true_eq_false)
    if a'.isConstOf ``False then
      return rewriteEq e middle proof (mkConst ``True) (mkConst ``not_false_eq_true)
    return if a == a' then unchanged input else (middle, proof)
  if e.isAppOfArity ``Exists 2 then
    let domain := e.getArg! 0
    let predicate := e.appArg!
    let name := if predicate.isLambda then predicate.bindingName! else `witness
    return ← withLocalDeclD name domain fun x => do
      let body := predicate.beta #[x]
      let (body', proof) ← simplifyTrueFalse body
      let u ← getLevel domain
      let predicate' ← if body == body' then pure predicate else mkLambdaFVars #[x] body'
      let middle := mkApp2 (mkConst ``Exists [u]) domain predicate'
      let congr ← if body == body' then pure (unchanged e).2 else
        pure (mkApp4 (mkConst ``exists_congr [u]) domain predicate predicate'
          (← mkLambdaFVars #[x] proof))
      if body'.isConstOf ``False then
        return (mkConst ``False, trans e middle (mkConst ``False) congr
          (mkApp (mkConst ``existsFalse [u]) domain))
      return if body == body' then unchanged input else (middle, congr)
  if let .forallE name domain body bi := e then
    if !body.hasLooseBVar 0 && (← isProp domain) then
      let body := body.instantiate1 (mkConst ``True.intro)
      let (domain', hd) ← simplifyTrueFalse domain
      let (body', hb) ← simplifyTrueFalse body
      let changed := domain != domain' || body != body'
      let middle := mkForall name bi domain' body'
      let proof := if changed then
          mkApp6 (mkConst ``imp_congr) domain body domain' body' hd hb
        else (unchanged e).2
      if body'.isConstOf ``True then
        return (mkConst ``True, trans e middle (mkConst ``True) proof
          (mkApp (mkConst ``imp_true_iff [.zero]) domain'))
      if domain'.isConstOf ``False then
        return rewriteEq e middle proof (mkConst ``True) (mkApp (mkConst ``false_implies) body')
      if domain'.isConstOf ``True then
        return rewriteEq e middle proof body' (mkApp (mkConst ``true_implies) body')
      return if changed then (middle, proof) else unchanged input
    return ← withLocalDecl name bi domain fun x => do
      let body := body.instantiate1 x
      let (body', proof) ← simplifyTrueFalse body
      if body == body' && !body'.isConstOf ``True then return unchanged input
      let u ← getLevel domain
      let middle ← mkForallFVars #[x] body'
      let congr ← if body == body' then pure (unchanged e).2 else
        pure (mkApp4 (mkConst ``forall_congr' [u]) domain
          (← mkLambdaFVars #[x] body) (← mkLambdaFVars #[x] body')
          (← mkLambdaFVars #[x] proof))
      if body'.isConstOf ``True then
        return (mkConst ``True, trans e middle (mkConst ``True) congr
          (mkApp (mkConst ``imp_true_iff [u]) domain))
      return (middle, congr)
  return unchanged input

/-- Replace the target using the structural equivalence, closing `True` immediately. -/
def simplifyGoal (goal : MVarId) : MetaM MVarId := goal.withContext do
  if ← goal.isAssignedOrDelayedAssigned then return goal
  let target ← instantiateMVars (← goal.getType)
  let (result, proof) ← simplifyTrueFalse target
  let goal ← if result == target then pure goal else
    goal.replaceTargetEq result (mkApp3 (mkConst ``propext) target result proof)
  if result.isConstOf ``True then goal.assign (mkConst ``True.intro)
  return goal

end Flex.Preprocess
