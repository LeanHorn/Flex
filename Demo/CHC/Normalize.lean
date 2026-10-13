import Flex.CHC
import Demo.UX

/-! Horn normalization and its actual acyclic-elimination boundary. The real
solver checks use Spacer by default; `CHC_ELDARICA=/path/to/eld` selects Eldarica
for the same tests. Run with `lake lean` to execute both configurations. -/
namespace CHCNormalizeDemo

open Lean Meta Elab Tactic Qq Flex.CHC

private def check (condition : Bool) (message : String) : MetaM Unit :=
  unless condition do throwError message

private def normalized (proposition : Expr) (expectedClauses : Nat)
    (expected : Option Expr := none) : MetaM Unit := do
  let original ← mkFreshExprMVar proposition
  let (_, kvars, body) ← peelExistentialsAndIntro original.mvarId!
  let body ← normalizeGoal body
  check (!(← body.isAssignedOrDelayedAssigned)) "normalization closed the certificate goal"
  for kvar in kvars do
    check (!(← kvar.mvarId.isAssignedOrDelayedAssigned)) "normalization chose a predicate witness"
  let actual ← body.getType
  if let some expected := expected then
    let expected := expected.beta (kvars.toArray.map fun kvar => mkMVar kvar.mvarId)
    unless ← isDefEq actual expected do
      throwError "unexpected normalized body:{indentExpr actual}\nexpected:{indentExpr expected}"
  let problem ← exportConstraints kvars actual
  check (problem.clauseCount == expectedClauses) "normalization/export clause counts disagree"

run_elab do
  normalized q(∃ k : Int → Prop,
    ∀ x : Int, (∃ y : Int, y = x ∧ 0 ≤ y) → k x) 1
    (some q(fun k : Int → Prop => ∀ x y : Int, y = x → 0 ≤ y → k x))
  normalized q(∃ k : Int → Prop,
    ∀ x : Int, (k x ∨ x = 0) → k (x + 1)) 2
    (some q(fun k : Int → Prop => ∀ x : Int,
      (k x → k (x + 1)) ∧ (x = 0 → k (x + 1))))
  -- Both antecedent alternatives and conjunctive conclusions contribute clauses.
  normalized q(∃ k : Int → Prop,
    ∀ x : Int, ((k x ∨ x = 0) ∧ (k x ∨ x = 1)) →
      (k (x + 1) ∧ k (x + 2))) 8
  -- Existential binders may carry a remaining relation, and must not capture x.
  normalized q(∃ k : Int → Prop,
    ∀ x : Int, (∃ y : Int, k y ∧ y = x) → k x) 1
    (some q(fun k : Int → Prop => ∀ x y : Int, k y → y = x → k x))
  normalized q(True) 0

run_elab do
  let proposition := q(∃ k : Int → Prop,
    ∀ x : Int, (k x ∨ x = 0) → k (x + 1))
  let original ← mkFreshExprMVar proposition
  let (_, kvars, body) ← peelExistentialsAndIntro original.mvarId!
  let before := (← getMCtx).eAssignment.toList
  let failed ← try
    discard <| normalizeGoal body (maxClauses := 1)
    pure false
  catch error =>
    check ((← error.toMessageData.toString).contains "clause limit") "unexpected cap failure"
    pure true
  check failed "normalization ignored the expansion cap"
  check ((← getMCtx).eAssignment.toList == before) "failed normalization changed assignments"
  for kvar in kvars do
    check (!(← kvar.mvarId.isAssignedOrDelayedAssigned)) "failed normalization assigned a predicate"
  discard <| normalizeGoal body (maxClauses := 2)

/-- Test-only caller: the public library leaves tactic goal-list policy to users. -/
elab "solve_normalized_chc" expectedRelations:num expectedClauses:num : tactic => withMainContext do
  let config : Flex.CHC.Config := match ← IO.getEnv "CHC_ELDARICA" with
    | some executable => { backend := .eldarica, executable := some executable }
    | none => { backend := .spacer }
  let outcome ← solveGoal (← getMainGoal) config
  let report ← match outcome with
    | .solved report => pure report
    | .partial report =>
      throwError "normalization integration left {report.certificate.obligations.size} VCs"
    | .failed failure => throwError "{repr failure.stage}: {failure.message}"
  check (report.problem.relations.size == expectedRelations.getNat)
    "wrong predicate count after normalization"
  check (report.problem.clauseCount == expectedClauses.getNat)
    "wrong normalized clause count"
  check (report.certificate.provedHeads + report.certificate.provedQueries == report.problem.clauseCount)
    "certificate provenance does not cover every normalized clause"
  replaceMainGoal []

-- This exact example previously stopped in export after zap introduced an
-- existential guard for κseed. Only κinv should reach the CHC backend now.
theorem afterZap : ex := by
  unfold ex
  zap
  solve_normalized_chc 1 3

-- A relation-containing disjunction is split before the Horn checker sees it.
theorem relationBranches :
    ∃ k : Int → Prop,
      k 0 ∧ (∀ x, (k x ∨ x = 0) → k (x + 1)) ∧ (∀ x, k x → 0 ≤ x) := by
  solve_normalized_chc 1 4

theorem branchedConclusions :
    ∃ k : Int → Prop,
      k 0 ∧ (∀ x, (k x ∨ x = 0) → k (x + 1) ∧ k (x + 2)) ∧
      (∀ x, k x → 0 ≤ x) := by
  solve_normalized_chc 1 6

run_elab do
  for name in [``afterZap, ``relationBranches, ``branchedConclusions] do
    let info ← getConstInfo name
    let some proof := info.value? (allowOpaque := true)
      | throwError "missing normalization integration proof"
    checkWithKernel proof
    for axiomName in ← collectAxioms name do
      check (#[``propext, ``Classical.choice, ``Quot.sound].contains axiomName)
        s!"unexpected axiom in normalization integration proof: {axiomName}"

end CHCNormalizeDemo
