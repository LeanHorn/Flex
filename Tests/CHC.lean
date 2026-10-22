import Flex.CHC.Goal

/-! Small checks for model import and certification; solver coverage lives in the benchmarks. -/

open Lean Meta Elab Term Flex.CHC

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let result ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars result

private def response (model : String) : SolverResult :=
  SolverResult.ofProcess { completion := .exited 0, stdout := "sat\n" ++ model }

-- The normalization bridge must prove the original existential/disjunctive guard.
run_elab do
  let target ← elaborate (← `(∃ k : Int → Prop,
    k 0 ∧ (∀ x : Int, (∃ y : Int, (k y ∨ y = 0) ∧ y = x) → k x) ∧
    (∀ x : Int, k x → 0 ≤ x)))
  let goal ← mkFreshExprMVar target
  let cleaned ← compactGoal goal.mvarId! []
  let prepared ← prepareGoal cleaned
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let witnesses ← importWitnesses problem
    (response "(model (define-fun k_0 ((x Int)) Bool (<= 0 x)))")
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun target => do proveLeafWith (← `(tactic| omega)) target)
  unless certificate.goals.isEmpty do throwError "normalized clauses were not certified"
  let proof ← instantiateMVars goal
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do throwError "normalization changed the goal"

-- Import an invariant, remove its heads, and finish the original goal from the residual.
run_elab do
  let target ← elaborate
    (← `(∃ unused : Prop, ∃ k : Int → Prop,
      k 0 ∧ (∀ x : Int, (k x ∨ x = 0) → k (x + 1)) ∧
      (∀ x : Int, k x → x + 1 > 0)))
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId! (headsOnly := true)
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  unless problem.clauseCount == 4 do throwError "guard normalization lost a branch"
  let witnesses ← importWitnesses problem
    (response "(model (define-fun k_1 ((x Int)) Bool (<= 0 x)))")
  unless witnesses.map (·.defaulted) == #[true, false] do
    throwError "unused predicate completion changed witness order"
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun target => do proveLeafWith (← `(tactic| omega)) target) (headsOnly := true)
  unless certificate.provedHeads == 2 && certificate.obligations.isEmpty do
    throwError "predicate heads were not removed cleanly"
  let some residual := certificate.residualVC | throwError "missing residual VC"
  residual.withContext do
    let expected ← elaborate (← `(∀ x : Int, 0 ≤ x → x + 1 > 0))
    unless ← isDefEq (← residual.getType) expected do
      throwError "unexpected residual VC: {← residual.getType}"
    let some proof ← proveLeafWith (← `(tactic| omega)) expected
      | throwError "could not finish residual VC"
    residual.assign proof
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "certificate contains unresolved or admitted evidence"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do
    throwError "certificate changed the original proposition"

-- Missing or ill-typed model definitions must not assign predicates or the body.
run_elab do
  let goal ← mkFreshExprMVar (← elaborate (← `(∃ k : Int → Prop, k 0)))
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  for model in #["(model)", "(model (define-fun k_0 ((x Bool)) Bool true))"] do
    let accepted ← try
      discard <| importWitnesses problem (response model)
      pure true
    catch _ => pure false
    if accepted then throwError "invalid model was accepted"
    for relation in problem.relations do
      if ← relation.kvar.mvarId.isAssignedOrDelayedAssigned then
        throwError "failed import assigned a predicate"
    if ← prepared.bodyGoal.isAssignedOrDelayedAssigned then
      throwError "failed import assigned the body"

-- A claimed proof of the wrong proposition must leave the false VC unproved.
run_elab do
  let goal ← mkFreshExprMVar (← elaborate (← `(∃ k : Prop, k ∧ (k → False))))
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let witnesses ← importWitnesses problem
    (response "(model (define-fun k_0 () Bool true))")
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun _ => pure (some (mkConst ``True.intro)))
  unless certificate.goals.size == 1 do throwError "invalid evidence closed the VC"
  let residual := certificate.goals[0]!
  residual.withContext do
    unless ← isDefEq (← residual.getType) (mkConst ``False) do
      throwError "invalid evidence changed the residual"
    if ← residual.isAssignedOrDelayedAssigned then
      throwError "invalid evidence proved False"
