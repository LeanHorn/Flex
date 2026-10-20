import Flex.CHC.Goal

/-! Constant division and modulus through export, model import, and certification. -/

open Lean Meta Elab Term Flex.CHC

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let result ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars result

private def exportTerm (term : TSyntax `term) : TermElabM ExportedProblem := do
  let prepared ← prepareGoal (← mkFreshExprMVar (← elaborate term)).mvarId!
  exportConstraints prepared.kvars (← prepared.exportGoal.getType)

private def expectRejected (term : TSyntax `term) (message : String) : TermElabM Unit := do
  let error ← try
    discard <| exportTerm term
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  let some error := error | throwError "unsupported arithmetic was exported"
  unless (error.splitOn message).length > 1 do
    throwError "expected '{message}', got '{error}'"

private abbrev customDiv : HDiv Int Int Int := ⟨fun _ _ => 0⟩
private abbrev customMod : HMod Int Int Int := ⟨fun _ _ => 0⟩

run_elab do
  let problem ← exportTerm
    (← `(∃ k : Int → Prop,
      k ((-5 : Int) / 2) ∧ k ((-5 : Int) % 2) ∧
      (∀ x : Int, k x → k (Int.ediv (Int.emod x 3) 2 + x % 1))))
  unless problem.clauseCount == 3 do throwError "division export lost a clause"
  for operator in #["(div ", "(mod "] do
    unless (problem.toSMTLib.splitOn operator).length > 1 do
      throwError "missing exported arithmetic operator '{operator}'"
  for term in #[
      ← `(∃ k : Int → Prop, ∀ x : Int, k (x / 0)),
      ← `(∃ k : Int → Prop, ∀ x : Int, k (x % 0)),
      ← `(∃ k : Int → Prop, ∀ x y : Int, k (x / y)),
      ← `(∃ k : Int → Prop, ∀ x y : Int, k (x % y)),
      ← `(∃ k : Int → Prop, ∀ x : Int, k (x / (-2))),
      ← `(∃ k : Int → Prop, ∀ x : Int, k (x % (-2)))] do
    expectRejected term "positive integer literal"
  expectRejected
    (← `(∃ k : Int → Prop, ∀ x : Int, k (@HDiv.hDiv Int Int Int customDiv x 2)))
    "nonstandard operator instance"
  expectRejected
    (← `(∃ k : Int → Prop, ∀ x : Int, k (@HMod.hMod Int Int Int customMod x 2)))
    "nonstandard operator instance"

run_elab do
  let target ← elaborate
    (← `(∃ k : Int → Prop,
      k (-5) ∧ (∀ x : Int, k x → k x) ∧ (∀ x : Int, k x → x = -5)))
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let response := SolverResult.ofProcess {
    completion := .exited 0
    stdout := "sat\n(model (define-fun k_0 ((x Int)) Bool
      (and (= (div x 2) (- 3)) (= (mod x 2) 1))))" }
  let witnesses ← importWitnesses problem response
  let expected ← elaborate (← `(fun x : Int => x / 2 = -3 ∧ x % 2 = 1))
  unless witnesses.size == 1 && (← isDefEq witnesses[0]!.value expected) do
    throwError "imported division/modulus invariant changed meaning"
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun target => do proveLeafWith (← `(tactic| omega)) target)
  unless certificate.goals.isEmpty do
    throwError "division/modulus invariant left unproved clauses"
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "arithmetic certificate contains unresolved or admitted evidence"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do
    throwError "arithmetic certificate changed the original proposition"
