import Flex.CHC.Goal

/-! Omitted model predicates are completed only when the assertions do not use them. -/

open Lean Meta Elab Term Flex.CHC

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let result ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars result

private def response (text : String) : SolverResult :=
  SolverResult.ofProcess { completion := .exited 0, stdout := text }

private def checkUnassigned (problem : ExportedProblem) (body : MVarId) : MetaM Unit := do
  for relation in problem.relations do
    if ← relation.kvar.mvarId.isAssignedOrDelayedAssigned then
      throwError "model import assigned a caller's predicate"
  if ← body.isAssignedOrDelayedAssigned then
    throwError "model import assigned the caller's goal"

private def checkProof (goal target : Expr) : MetaM Unit := do
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "certificate contains unresolved or admitted evidence"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do
    throwError "certificate changed the original proposition"

private def expectRejected (term : TSyntax `term) (model message : String)
    : TermElabM Unit := do
  let goal ← mkFreshExprMVar (← elaborate term)
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let error ← try
    discard <| importWitnesses problem (response model)
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  let some error := error | throwError "invalid model unexpectedly imported"
  unless (error.splitOn message).length > 1 do
    throwError "expected '{message}', got '{error}'"
  checkUnassigned problem prepared.bodyGoal

run_elab do
  let target ← elaborate
    (← `(∃ unused : Prop, ∃ k : Int → Prop, ∃ unusedArgs : Prop → Bool → Int → Prop,
      k 0 ∧ (∀ x : Int, k x → 0 ≤ x)))
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let witnesses ← importWitnesses problem
    (response "sat\n(model (define-fun k_1 ((x Int)) Bool (<= 0 x)))")
  checkUnassigned problem prepared.bodyGoal
  unless witnesses.size == 3 && witnesses.map (·.defaulted) == #[true, false, true] do
    throwError "model completion lost witness order or provenance"
  let expected := #[
    ← elaborate (← `(True)),
    ← elaborate (← `(fun x : Int => 0 ≤ x)),
    ← elaborate (← `(fun (_ : Prop) (_ : Bool) (_ : Int) => True))]
  for relation in problem.relations, witness in witnesses, value in expected do
    unless witness.symbol == relation.symbol && witness.mvarId == relation.kvar.mvarId &&
        (← isDefEq witness.value value) do
      throwError "model completion changed a predicate's identity or type"
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun target => do proveLeafWith (← `(tactic| omega)) target)
  unless certificate.goals.isEmpty do throwError "completed model could not be certified"
  checkProof goal target

run_elab do
  let target ← elaborate
    (← `(∃ p : Prop, ∃ k : Bool → Prop, (p → True) ∧ (∀ b, k b → True)))
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId! (headsOnly := true)
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  unless problem.clauseCount == 0 do throwError "tautological clauses were not removed"
  let witnesses ← importWitnesses problem (response "sat\n()")
  checkUnassigned problem prepared.bodyGoal
  unless witnesses.size == 2 && witnesses.all (·.defaulted) do
    throwError "an explicitly empty model did not complete unused predicates"
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal (headsOnly := true)
  unless certificate.goals.isEmpty do throwError "original tautological VC was not certified"
  checkProof goal target

run_elab do
  let target ← elaborate
    (← `(∃ p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : Prop, p10))
  let prepared ← prepareGoal (← mkFreshExprMVar target).mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let witnesses ← importWitnesses problem
    (response "sat\n(model (define-fun k_10 () Bool true))")
  unless witnesses.size == 11 && witnesses[1]!.defaulted && !witnesses[10]!.defaulted do
    throwError "predicate names were matched by substring"
  checkUnassigned problem prepared.bodyGoal
  for term in #[
      ← `(∃ p : Prop, p),
      ← `(∃ p : Prop, p → False),
      ← `(∃ k : Int → Prop, ∀ x, k x → x = 0)] do
    expectRejected term "sat\n(model)" "missing model definition"
  expectRejected (← `(∃ p : Prop, True)) "sat" "successful sat result"
  expectRejected (← `(∃ k : Int → Prop, True))
    "sat\n(model (define-fun k_0 ((x Bool)) Bool true))" "model signature"
