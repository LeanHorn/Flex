import Flex.CHC.Goal

/-! Regression checks for predicate signatures and preparation rollback. -/

open Lean Meta Elab Term Flex.CHC

private def expectRejected (target : Expr) (message : String) (maxClauses := 1024)
    : TermElabM Unit := do
  let goal ← mkFreshExprMVar target
  let error ← try
    discard <| prepareGoal goal.mvarId! maxClauses
    pure none
  catch error =>
    pure (some (← error.toMessageData.toString))
  let some error := error | throwError "preparation unexpectedly succeeded"
  unless (error.splitOn message).length > 1 do
    throwError "expected '{message}', got '{error}'"
  if ← goal.mvarId!.isAssignedOrDelayedAssigned then
    throwError "failed preparation modified its caller's goal"

run_elab do
  let target ← elabTerm
    (← `(∃ p : Prop, ∃ k : Prop → Bool → Int → Prop,
      p ∧ (∀ (q : Prop) (b : Bool) (x : Int), q → p → k q b x))) none
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  unless problem.relations.size == 2 && problem.clauseCount == 2 do
    throwError "predicate prefix or proof/value binders were misclassified"
  unless problem.relations[0]!.argumentSorts.isEmpty &&
      problem.relations[1]!.argumentSorts == #[.bool, .bool, .int] do
    throwError "nullary or Prop-valued predicate arguments were lost"
  for (term, message) in #[
      (← `(∃ A : Type, ∃ k : A → Prop, True), "existential carrier"),
      (← `(∃ c : Int, c = 0), "background constant"),
      (← `(∃ f : Int → Int, f 0 = 0), "background function"),
      (← `(∃ f : Int → Bool, f 0 = true), "background function"),
      (← `(∃ k : Nat → Prop, k 0), "unsupported type"),
      (← `(∃ k : (n : Int) → n = n → Prop, True), "dependent argument")] do
    expectRejected (← elabTerm term none) message
  withLocalDeclD `A (.sort (.succ .zero)) fun carrier => do
    let functionType ← mkArrow carrier (mkConst ``Int)
    withLocalDeclD `select functionType fun select => do
      let target ← mkAppM ``Exists #[← mkLambdaFVars #[select] (mkConst ``True)]
      expectRejected target "theory-model parameter"
  let target ← elabTerm
    (← `(∃ k : Int → Prop, ((0 : Int) = 0 ∨ (0 : Int) = 1) → k 0)) none
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let compact ← prepareGoal (← mkFreshExprMVar target).mvarId! 1
  unless (← exportConstraints compact.kvars (← compact.exportGoal.getType)).clauseCount == 1 do
    throwError "theory disjunction should remain one clause"
  let target ← elabTerm
    (← `(∃ k : Int → Prop, (k 0 ∨ k 1) → k 2)) none
  expectRejected target "clause limit" 1
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId! (headsOnly := true)
  if ← prepared.bodyGoal.isAssignedOrDelayedAssigned then
    throwError "heads-only preparation changed the original body"
  if prepared.bodyGoal == prepared.exportGoal then
    throwError "heads-only preparation did not create a separate export goal"

run_elab do
  let guard := mkApp2 (mkConst ``And) (mkConst ``True) (mkConst ``True)
  let mut body := Expr.forallE `h guard (mkBVar 1) .default
  for _ in [:100] do body := mkApp2 (mkConst ``And) (mkConst ``True) body
  let target ← mkAppM ``Exists #[.lam `k (.sort .zero) body .default]
  let goal ← mkFreshExprMVar target
  let failed ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxRecDepth := 32 }) do
      discard <| prepareGoal goal.mvarId!
      pure false)
    (fun error => do
      unless error.isMaxRecDepth do throw error
      pure true)
  unless failed do throwError "expected preparation to exceed its recursion budget"
  if ← goal.mvarId!.isAssignedOrDelayedAssigned then
    throwError "resource-limited preparation modified its caller's goal"
