import Flex.VCG.LambdaRK.Bridge.Reconstruct

/-!
Solver-independent checks of λRK reconstruction and residual cleanup. In
particular, cleanup cannot manufacture evaluation evidence for an undefined
measure, and admission checking applies to partial proof scaffolds too.
-/

namespace LambdaRKBridgeReconstruction

open Lean Meta Elab Tactic LambdaRK LambdaRK.Bridge

private def check (condition : Bool) (message : String) : MetaM Unit :=
  unless condition do throwError message

elab "checked_scalar_bridge" : tactic => withMainContext do
  let goal ← getMainGoal
  let some proof ← proveBridge (← goal.getType)
    | throwError "the generic scalar implication was not certified"
  goal.assign proof
  replaceMainGoal []

theorem mixedScalarBridge (predicate : Int → Bool → Prop) : predicate 4 true →
    Cstr.Valid {} (bindPredicate "mixed" [.int, .bool] predicate (fun _ _ => False))
      (.head (.kvar "mixed" [.int 4, .bool true])) := by
  checked_scalar_bridge

run_elab do
  let invalid ← mkArrow (mkConst ``True) (mkConst ``False)
  let proof ← proveBridge invalid
  check proof.isNone
    "proof reconstruction accepted an invalid implication"

-- A missing measure on an arbitrary runtime value remains a semantic goal.
-- It cannot become the scalar equation `0 = 0` merely by inventing a witness.
run_elab do
  let target ← Term.elabTerm (← `(Cstr.Valid {} (fun _ _ => False)
    (.all "x" .value (.head (.theory
      (.eq (.measure "undefined" (.var "x")) (.int 0))))))) none
  let original ← mkFreshExprMVar target (kind := .syntheticOpaque)
  let remaining ← cleanSourceGoal original.mvarId!
  check (remaining.length == 1) "undefined measure lost its residual obligation"
  remaining.head!.withContext do
    let residual ← remaining.head!.getType
    check (residual.isAppOfArity ``MeasureEval 4)
      "undefined measure residue was not a clean MeasureEval fact"
    check (!(← getLCtx).getFVarIds.isEmpty) "cleanup did not introduce the runtime-value binder"
  let partialProof ← instantiateMVars original
  check partialProof.hasMVar "cleanup discharged an undefined measure"
  Flex.CHC.rejectAdmissions partialProof

-- The final bridge check also scans partial scaffolds, rather than assuming
-- that the presence of an outstanding goal makes the completed pieces safe.
run_elab do
  let pending ← mkFreshExprMVar (mkConst ``True)
  let admitted ← mkSorry (mkConst ``True) true
  let partialProof ← mkAppM ``And.intro #[pending, admitted]
  let rejected ← try
    Flex.CHC.rejectAdmissions partialProof
    pure false
  catch _ => pure true
  check rejected "admission checking ignored an admitted sibling of a residual goal"
  check (!(← pending.mvarId!.isAssigned)) "admission checking assigned a residual goal"

end LambdaRKBridgeReconstruction
