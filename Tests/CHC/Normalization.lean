import Flex.CHC.Goal

/-! Compact guard normalization, export agreement, and checked proof bridges. -/

open Lean Meta Elab Term Flex.CHC

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let result ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars result

private def expectClauses (term : TSyntax `term) (count : Nat)
    : TermElabM Unit := do
  let goal ← mkFreshExprMVar (← elaborate term)
  let prepared ← prepareGoal goal.mvarId! count
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  unless problem.clauseCount == count do
    throwError "expected {count} clauses, got {problem.clauseCount}"
  for kvar in prepared.kvars do
    if ← kvar.mvarId.isAssignedOrDelayedAssigned then
      throwError "normalization assigned a predicate witness"

run_elab do
  expectClauses
    (← `(∃ k : Int → Prop, ∀ x : Int, (k x ∧ (x = 0 ∨ x = 1)) → k (x + 1))) 1
  expectClauses
    (← `(∃ k : Int → Prop, ∀ x : Int, ((x = 0 → x ≤ 1) ∨ x = 2) → k x)) 1
  expectClauses
    (← `(∃ k : Int → Prop, ∀ x : Int, ((k x ∨ x = 0) ∧ (x = 0 ∨ x = 1)) → k (x + 1))) 2
  expectClauses
    (← `(∃ p q : Prop, (p ∨ q) → p)) 2
  expectClauses
    (← `(∃ k : Int → Prop, ((k 0 ∨ k 1 ∨ k 2) → True) ∧ ((k 0 ∨ k 1) → k 2))) 2
  expectClauses
    (← `(∃ k : Int → Prop, ∀ x : Int, ((∃ y : Int, y = x) ∨ x = 0) → k x)) 2
  let target ← withLocalDeclD `k (← mkArrow (mkConst ``Int) (.sort .zero)) fun k =>
    withLocalDeclD `x (mkConst ``Int) fun x => do
      let choice := mkApp2 (mkConst ``Or) (← mkEq x (mkIntLit 0)) (← mkEq x (mkIntLit 1))
      let mut guard := choice
      for _ in [:11] do guard := mkApp2 (mkConst ``And) guard choice
      let body ← mkForallFVars #[x] (← mkArrow guard (mkApp k x))
      mkAppM ``Exists #[← mkLambdaFVars #[k] body]
  let prepared ← prepareGoal (← mkFreshExprMVar target).mvarId! 1
  unless (← exportConstraints prepared.kvars (← prepared.exportGoal.getType)).clauseCount == 1 do
    throwError "theory choices were distributed"

run_elab do
  let target ← elaborate
    (← `(∃ k : Int → Prop,
      k 0 ∧
      (∀ x : Int, (∃ y : Int, (k y ∨ y = 0) ∧ x = y + 1) → k x) ∧
      (∀ x : Int, k x → 0 ≤ x)))
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  unless problem.clauseCount == 4 do throwError "existential/disjunction expansion lost clauses"
  let value ← elaborate (← `(fun x : Int => 0 ≤ x))
  let witnesses := problem.relations.map fun relation =>
    { symbol := relation.symbol, mvarId := relation.kvar.mvarId, value : Witness }
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun target => do proveLeafWith (← `(tactic| omega)) target)
  unless certificate.goals.isEmpty do throwError "normalized constraints could not be certified"
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "normalization proof escaped a binder or left an obligation"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do
    throwError "normalization proof changed the original proposition"

run_elab do
  let target ← elaborate
    (← `(∃ k : Int → Prop, ∀ x : Int, (k x ∨ x = 0) → k (x + 1)))
  let prepared ← prepareGoal (← mkFreshExprMVar target).mvarId! (headsOnly := true)
  let original ← prepared.bodyGoal.getType
  let exported ← prepared.exportGoal.getType
  if ← prepared.bodyGoal.isAssignedOrDelayedAssigned then
    throwError "heads-only normalization assigned the original body"
  if original == exported then throwError "relation disjunction was not expanded for export"
  unless (← exportConstraints prepared.kvars exported).clauseCount == 2 do
    throwError "heads-only export lost a branch"
  let target ← elaborate
    (← `(∃ k : Int → Prop, ∀ x : Int, (¬ k x ∨ x = 0) → k (x + 1)))
  let prepared ← prepareGoal (← mkFreshExprMVar target).mvarId!
  let error ← try
    discard <| exportConstraints prepared.kvars (← prepared.exportGoal.getType)
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  let some error := error | throwError "negative predicate premise was accepted"
  unless (error.splitOn "relation inside").length > 1 do
    throwError "unexpected negative-predicate rejection: {error}"
  let target ← elaborate
    (← `(∃ k : Int → Prop, (∀ x : Int, x = x) → k 0))
  let prepared ← prepareGoal (← mkFreshExprMVar target).mvarId!
  let error ← try
    discard <| exportConstraints prepared.kvars (← prepared.exportGoal.getType)
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  let some error := error | throwError "quantified theory guard was accepted"
  unless (error.splitOn "quantifiers").length > 1 do
    throwError "unexpected quantified-guard rejection: {error}"
