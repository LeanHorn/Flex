import Flex.CHC

/-! Real Spacer integration checks. These require `z3` on PATH, like the existing
lean-auto demos. Protocol and process-failure tests live in `CHCRunner.lean`. -/
namespace CHCSpacerDemo

open Lean Meta Qq Flex.CHC

private def solve (formula : Expr) : MetaM SolverResult := do
  let goal ← mkFreshExprMVar formula
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
  let problem ← exportConstraints kvars (← bodyGoal.getType)
  let result ← Spacer.run problem
  unless !(← bodyGoal.isAssigned) do throwError "runner assigned the constraint goal"
  for kvar in kvars do
    if ← kvar.mvarId.isAssigned then throwError "runner assigned a witness"
  return result

private def expectSat (formula : Expr) (definitions : Nat) : MetaM Unit := do
  let result ← solve formula
  let .sat model := result.outcome
    | throwError "expected a Spacer model ({repr result.process.completion}), got stdout:\n{result.process.stdout}\nstderr:\n{result.process.stderr}"
  unless model.size == definitions do throwError "unexpected number of model definitions"
  unless result.process.completion matches .exited 0 do throwError "Spacer did not exit successfully"
  for definition in model do
    unless definition.tokens[1]? == some "define-fun" do
      throwError "model entry was not an ordinary definition"

run_elab do
  expectSat q(∃ k : Int → Prop,
    k 0 ∧ (∀ x, k x → k (x + 1)) ∧ (∀ x, k x → 0 ≤ x)) 1
  expectSat q(∃ k : Bool → Int → Prop,
    (∀ b : Bool, k b 0) ∧
    (∀ b x, k b x → k (Bool.not b) (x + 1)) ∧
    (∀ b x, k b x → x ≥ 0)) 1
  -- An explicitly empty model differs from a missing model.
  expectSat q(True) 0
  let result ← solve q(∃ k : Int → Prop,
    k 0 ∧ (∀ x, k x → k (x + 1)) ∧ (∀ x, k x → x < 0))
  unless result.outcome matches .unsat do
    throwError "expected unsat, got:\n{result.process.stdout}"
  -- -model must not emit a failing get-model request after unsat.
  unless result.process.completion matches .exited 0 do
    throwError "unsat was accompanied by a process error"

end CHCSpacerDemo
