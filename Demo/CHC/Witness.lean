import Flex.CHC
import Smt2Lean.Equivalence

/-! Static model-to-witness regressions. No external solver is launched. -/
namespace CHCWitnessDemo

open Lean Meta Qq Flex.CHC

set_option linter.unusedVariables false

private def check (condition : Bool) (message : String) : MetaM Unit :=
  unless condition do throwError message

private def response (text : String) : SolverResult :=
  SolverResult.ofProcess { completion := .exited 0, stdout := text }

private def problemFor (formula : Expr) : MetaM ExportedProblem := do
  let goal ← mkFreshExprMVar formula
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
  exportConstraints kvars (← bodyGoal.getType)

private structure Snapshot where
  constants : List Name
  locals : Array FVarId
  metavariables : List MVarId
  assignments : List (MVarId × Expr)
  delayedAssignments : List (MVarId × Array Expr × MVarId)
  deriving BEq

private def snapshot : MetaM Snapshot := do
  return {
    constants := (← getEnv).constants.toList.map (·.1)
    locals := (← getLCtx).getFVarIds
    metavariables := (← getMCtx).decls.toList.map (·.1)
    assignments := (← getMCtx).eAssignment.toList
    delayedAssignments := (← getMCtx).dAssignment.toList.map fun (id, assignment) =>
      (id, assignment.fvars, assignment.mvarIdPending) }

private def unassigned (problem : ExportedProblem) : MetaM Unit := do
  for relation in problem.relations do
    check (!(← relation.kvar.mvarId.isAssigned)) "operation unexpectedly assigned a κ"

private def prepare (problem : ExportedProblem) (text : String) : MetaM (Array Witness) := do
  let before ← snapshot
  let witnesses ← importWitnesses problem (response text)
  check ((← snapshot) == before) "import changed the caller's environment or meta state"
  unassigned problem
  check (witnesses.map (·.symbol) == problem.relations.map (·.symbol))
    "witnesses are not in the original existential order"
  check (witnesses.map (·.mvarId) == problem.relations.map (·.kvar.mvarId))
    "witnesses target the wrong existential metavariables"
  for witness in witnesses, relation in problem.relations do
    check (!(witness.value.hasFVar || witness.value.hasMVar || witness.value.hasLooseBVars))
      "imported witness contains an unresolved variable"
    check (← isDefEq (← inferType witness.value) relation.leanType) "wrong witness type"
    checkWithKernel witness.value
  return witnesses

private def rejects (action : MetaM Unit) : MetaM Unit := do
  let before ← snapshot
  let rejected ← try action; pure false catch _ => pure true
  check rejected "accepted an invalid model or witness collection"
  check ((← snapshot) == before) "failed operation left partial changes in the caller"

private def sameMeaning (actual expected : Expr) : MetaM Unit := do
  let proof ← Smt2Lean.Equivalence.prove actual expected (fun _ => false)
  checkWithKernel proof

-- Definitions arrive out of existential order. A helper is expanded, original
-- Bool and Prop argument positions stay distinct, and unused arguments survive.
run_elab do
  let problem ← problemFor q(∃ k : Bool → Prop → Int → Prop,
    ∃ unused : Int → Bool → Prop, ∃ flag : Prop, k true True 0 ∧ flag)
  let witnesses ← prepare problem "sat\n(model\n\
    (define-fun bump ((x Int)) Int (+ x 1))\n\
    (define-fun k_2 () Bool true)\n\
    (define-fun k_1 ((x Int) (b Bool)) Bool false)\n\
    (define-fun k_0 ((b Bool) (p Bool) (n Int)) Bool (and b (or p (>= (bump n) 0)))))"
  sameMeaning witnesses[0]!.value q(fun (b : Bool) (p : Prop) (n : Int) =>
    (b = true) ∧ (p ∨ n + 1 ≥ 0))
  sameMeaning witnesses[1]!.value q(fun (_ : Int) (_ : Bool) => False)
  sameMeaning witnesses[2]!.value q(True)
  assignWitnesses problem witnesses
  for witness in witnesses do
    check (← witness.mvarId.isAssigned) "successful assignment omitted a κ"
    check (← isDefEq (← instantiateMVars (mkMVar witness.mvarId)) witness.value)
      "assigned expression differs from the prepared witness"

run_elab do
  let problem ← problemFor q(∃ k : Int → Prop,
    k 0 ∧ (∀ x, k x → k (x + 1)) ∧ (∀ x, k x → 0 ≤ x))
  let witnesses ← prepare problem "sat ((define-fun k_0 ((x Int)) Bool (>= x 0)))"
  sameMeaning witnesses[0]!.value q(fun (x : Int) => 0 ≤ x)
  -- No existential relations requires an explicitly empty witness collection.
  let empty ← problemFor q(True)
  let noWitnesses ← prepare empty "sat ()"
  check noWitnesses.isEmpty "ground problem acquired witnesses"
  assignWitnesses empty noWitnesses

-- Preparation rejects incomplete, malformed, and ill-typed interpretations.
run_elab do
  let problem ← problemFor q(∃ k : Bool → Int → Prop, True)
  for text in [
      "sat ()",
      "sat ((define-fun other ((b Bool) (x Int)) Bool true))",
      "sat ((define-fun k_0 ((x Int)) Bool true))",
      "sat ((define-fun k_0 ((x Int) (b Bool)) Bool true))",
      "sat ((define-fun k_0 ((b Bool) (x Int)) Int x))",
      "sat ((define-fun k_0 ((b Bool) (x Int)) Bool true) (define-fun k_0 ((b Bool) (x Int)) Bool false))",
      "sat ((define-fun k_0 ((b Bool) (x Int)) Bool (unknown_helper x)))",
      "sat ((define-fun k_0 ((b Bool) (x Int)) Bool true) (define-fun unsupported ((x Real)) Real x))",
      "unsat", "unknown", "sat", "(error \"solver failed\")"] do
    rejects (discard <| importWitnesses problem (response text))
    unassigned problem
  -- A valid model still imports after failed native-parser/reconstruction calls.
  discard <| prepare problem "sat ((define-fun k_0 ((b Bool) (x Int)) Bool (and b (>= x 0))))"

private def twoPredicates : MetaM (ExportedProblem × Array Witness) := do
  let problem ← problemFor q(∃ first : Int → Prop, ∃ second : Int → Prop, True)
  let witnesses ← prepare problem "sat ((define-fun k_1 ((x Int)) Bool (<= x 10))\
    (define-fun k_0 ((x Int)) Bool (>= x 0)))"
  return (problem, witnesses)

-- Commit checks the whole collection before assigning any existential.
run_elab do
  let (problem, witnesses) ← twoPredicates
  rejects <| assignWitnesses problem (witnesses.extract 0 1)
  rejects <| assignWitnesses problem #[witnesses[0]!, witnesses[0]!]
  rejects <| assignWitnesses problem (witnesses.set! 1 { witnesses[1]! with value := q(0 : Nat) })
  rejects <| assignWitnesses problem (witnesses.set! 1 {
    witnesses[1]! with value := mkApp (mkNatLit 0) (mkNatLit 1) })
  rejects <| assignWitnesses problem (witnesses.set! 1 { witnesses[1]! with symbol := "wrong" })
  let unresolved ← mkFreshExprMVar q(Int → Prop)
  rejects <| assignWitnesses problem (witnesses.set! 1 { witnesses[1]! with value := unresolved })
  withLocalDeclD `outside q(Int → Prop) fun outside => do
    rejects <| assignWitnesses problem (witnesses.set! 1 { witnesses[1]! with value := outside })
  unassigned problem
  assignWitnesses problem witnesses
  for witness in witnesses do
    check (← witness.mvarId.isAssigned) "valid assignment failed after rejected attempts"

-- A slot can become occupied between preparation and assignment. Keep its
-- existing value and leave every other slot untouched when rejecting the bundle.
run_elab do
  let (problem, witnesses) ← twoPredicates
  witnesses[1]!.mvarId.assign q(fun (_ : Int) => False)
  rejects <| assignWitnesses problem witnesses
  check (!(← witnesses[0]!.mvarId.isAssigned)) "stale bundle partially assigned its first κ"
  check (← isDefEq (← instantiateMVars (mkMVar witnesses[1]!.mvarId))
    q(fun (_ : Int) => False)) "stale bundle overwrote an existing assignment"

run_elab do
  let (problem, witnesses) ← twoPredicates
  let pending ← mkFreshExprMVar q(Int → Prop) (kind := .syntheticOpaque)
  assignDelayedMVar witnesses[1]!.mvarId #[] pending.mvarId!
  rejects <| assignWitnesses problem witnesses
  rejects <| discard <| importWitnesses problem
    (response "sat ((define-fun k_0 ((x Int)) Bool true) (define-fun k_1 ((x Int)) Bool true))")
  check (!(← witnesses[0]!.mvarId.isAssigned)) "delayed assignment caused a partial commit"

-- Public metadata must agree with the actual witness slots.
run_elab do
  let (problem, _) ← twoPredicates
  let model := response "sat ((define-fun k_0 ((x Int)) Bool true)\
    (define-fun k_1 ((x Int)) Bool true))"
  let first := problem.relations[0]!
  for altered in #[
      { problem with relations := #[first, first] },
      { problem with relations := problem.relations.set! 0 { first with leanType := q(Bool → Prop) } },
      { problem with relations := problem.relations.set! 0 { first with argumentSorts := #[.bool] } },
      { problem with relations := problem.relations.set! 0 {
        first with kvar := { first.kvar with paramTypes := [] } } }] do
    rejects (discard <| importWitnesses altered model)
  unassigned problem

end CHCWitnessDemo
