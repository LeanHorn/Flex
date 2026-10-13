import Flex.VCG.LambdaRK.Bridge.Goal

/-!
The generic λRK goal adapter, independently of `map`: mixed scalar signatures,
multiple relations, retained source obligations, and transactional failures.
Spacer runs by default; `CHC_ELDARICA=/path/to/eld` selects Eldarica.
-/
namespace LambdaRKBridgeChecks

open Lean Meta Elab Tactic LambdaRK LambdaRK.Bridge

private def scalarSignature : Signature := {
  kvars := [⟨"state", [.bool, .int]⟩, ⟨"summary", [.int]⟩] }

private def scalarConstraints : Cstr :=
  let initial : Cstr := .head (.kvar "state" [.bool true, .int 0])
  let step : Cstr := .all "b" .bool <| .all "n" .int <|
    .guard (.kvar "state" [.var "b", .var "n"])
      (.head (.kvar "state" [.var "b", .add (.var "n") (.int 1)]))
  let link : Cstr := .all "b" .bool <| .all "n" .int <|
    .guard (.kvar "state" [.var "b", .var "n"])
      (.head (.kvar "summary" [.var "n"]))
  let query : Cstr := .all "n" .int <| .guard (.kvar "summary" [.var "n"])
    (.head (.theory (.le (.int 0) (.var "n"))))
  .conj initial (.conj step (.conj link query))

private def proposition (signature constraint : Lean.Expr) : MetaM Lean.Expr :=
  withLocalDeclD `κ (mkConst ``KAssignment) fun assignment => do
    mkAppM ``Exists #[← mkLambdaFVars #[assignment]
      (mkApp3 (mkConst ``Cstr.Valid) signature assignment constraint)]

private def freshGoal (signature : Signature) (constraint : Cstr) : MetaM Lean.Expr := do
  mkFreshExprMVar (← proposition (toExpr signature) (toExpr constraint))

private def backendConfig : TermElabM Flex.CHC.Config := do
  return match ← IO.getEnv "CHC_ELDARICA" with
    | some executable => { backend := .eldarica, executable := some executable }
    | none => {}

private def completed (goal : Lean.Expr) : MetaM Unit := do
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasLevelMVar || proof.hasSorry then
    throwError "bridge left unresolved or admitted proof evidence"
  checkWithKernel proof
  for declaration in proof.getUsedConstants do
    for axiomName in (← collectAxioms declaration) do
      unless axiomName == ``propext || axiomName == ``Classical.choice ||
          axiomName == ``Quot.sound do
        throwError "bridge certificate uses a nonstandard axiom: {axiomName}"

private def finishObligations (report : GoalReport) : TermElabM Unit := do
  for obligation in report.obligations do
    if !(← obligation.goal.isAssigned) then
      let remaining ← Tactic.run obligation.goal do
        evalTactic (← `(tactic| first | exact fun _ => True | simp_all <;> omega))
      unless remaining.isEmpty do
        throwError "manual bridge completion left obligations"

run_elab do
  let config ← backendConfig
  let goal ← freshGoal scalarSignature scalarConstraints
  let report ← match ← solveGoal goal.mvarId! config with
    | .solved report => pure report
    | .partial report =>
        throwError "mixed scalar example left {report.obligations.size} obligations: {repr report.diagnostics}"
    | .failed message => throwError "mixed scalar example failed: {message}"
  unless report.checkedClauses == 4 && report.witnesses.size == 2 do
    throwError "mixed scalar example lost checked clauses or predicates"
  let some solver := report.solver | throwError "mixed scalar example did not invoke the solver"
  unless solver.problem.relations.size == 2 do
    throwError "mixed scalar example lost a relation during export"
  completed goal

  -- A disabled proof oracle keeps imported predicates and explicit scalar VCs.
  let goal ← freshGoal scalarSignature scalarConstraints
  let .partial report ← solveGoal goal.mvarId! config (fun _ => pure none)
    | throwError "disabled scalar oracle did not leave partial progress"
  unless report.witnesses.size == 2 && !report.obligations.isEmpty do
    throwError "partial scalar result lost its invariant witnesses or VCs"
  finishObligations report
  completed goal

  -- An arbitrary runtime value need not have a measure. Successful synthesis
  -- for the scalar clauses must retain this unsupported evaluation obligation.
  let signature : Signature := { scalarSignature with
    datatypes := [⟨"Chain", 0, [⟨"empty", []⟩, ⟨"next", [.data "Chain" []]⟩]⟩]
    measures := [⟨"length", "Chain", [⟨"empty", .literal 0⟩,
      ⟨"next", .add (.literal 1) (.recur 0)⟩]⟩] }
  let measureClause : Cstr := .all "x" .value <|
    .head (.theory (.le (.int 0) (.measure "length" (.var "x"))))
  let goal ← freshGoal signature (.conj scalarConstraints measureClause)
  let .partial report ← solveGoal goal.mvarId! config
    | throwError "undefined measure head did not leave a source obligation"
  unless report.solver.isSome && report.witnesses.size == 2 &&
      report.checkedClauses == 4 && report.obligations.any (·.sourceClause == some 4) do
    throwError "measure residual lost the successfully synthesized scalar predicates"
  for (_, witness) in report.witnesses do
    if (← instantiateMVars witness).hasMVar then
      throwError "measure residual reverted a synthesized predicate"
  let mut retainsMeasure := false
  for obligation in report.obligations do
    let target ← instantiateMVars (← obligation.goal.getType)
    retainsMeasure := retainsMeasure || target.getUsedConstants.contains ``MeasureEval
    if target.getUsedConstants.contains ``Cstr.Valid || target.getUsedConstants.contains ``Cstr.denote then
      throwError "measure residual retained opaque source-constraint scaffolding"
  unless retainsMeasure do throwError "source cleanup erased partial measure evaluation"
  check (← instantiateMVars goal)

run_elab do
  let missing : Flex.CHC.Config := { executable := some "/flex-bridge-test/does-not-exist" }
  let signature : Signature := { kvars := [⟨"opaque", [.value]⟩] }
  let constraint : Cstr := .all "x" .value (.head (.kvar "opaque" [.var "x"]))
  let goal ← freshGoal signature constraint
  let .partial report ← solveGoal goal.mvarId! missing
    | throwError "runtime-value predicate did not leave an explicit witness and source VC"
  unless report.solver.isNone && report.checkedClauses == 0 &&
      report.diagnostics.size == 1 && report.obligations.any (·.sourceClause == some 0) do
    throwError "unsupported value clause lost its source provenance"
  finishObligations report
  completed goal

  -- An unused scalar declaration likewise remains a witness goal. A backend
  -- cannot be asked for a model definition absent from its scalar constraints.
  let signature : Signature := { kvars := [⟨"unused", [.int]⟩] }
  let goal ← freshGoal signature .truth
  let .partial report ← solveGoal goal.mvarId! missing
    | throwError "unused scalar predicate did not remain an explicit witness"
  unless report.solver.isNone && report.obligations.size == 1 do
    throwError "unused scalar predicate unexpectedly reached the solver"
  finishObligations report
  completed goal

  -- A compiler proposal alone is insufficient. A constant measure body still
  -- requires its constructor fields to evaluate; this unbound field has no such
  -- evidence in an arbitrary source environment.
  let signature : Signature := {
    datatypes := [⟨"Box", 0, [⟨"box", [.int]⟩]⟩]
    measures := [⟨"zero", "Box", [⟨"box", .literal 0⟩]⟩]
    kvars := [⟨"candidate", [.int]⟩] }
  let constraint : Cstr := .head (.kvar "candidate"
    [.measure "zero" (.ctor "box" [.var "unbound"])])
  unless (lower signature constraint).supported.size == 1 do
    throwError "negative certificate test did not exercise a compiler proposal"
  let goal ← freshGoal signature constraint
  let .partial report ← solveGoal goal.mvarId! missing
    | throwError "unjustified constructor evaluation was accepted"
  unless report.solver.isNone && report.checkedClauses == 0 &&
      report.diagnostics.any (·.message == "could not certify the proposed scalar lowering") &&
      report.obligations.any (·.sourceClause == some 0) do
    throwError "failed lowering proof was not retained as an explicit source obligation"

run_elab do
  let missing : Flex.CHC.Config := { executable := some "/flex-bridge-test/does-not-exist" }
  let goal ← freshGoal scalarSignature scalarConstraints
  let beforeMetavariables := (← getMCtx).decls.toList.map (·.1)
  let beforeAssignments := (← getMCtx).eAssignment.toList
  let beforeConstants := (← getEnv).constants.toList.map (·.1)
  let .failed _ ← solveGoal goal.mvarId! missing
    | throwError "missing solver unexpectedly succeeded"
  unless !(← goal.mvarId!.isAssigned) &&
      (← getMCtx).decls.toList.map (·.1) == beforeMetavariables &&
      (← getMCtx).eAssignment.toList == beforeAssignments &&
      (← getEnv).constants.toList.map (·.1) == beforeConstants do
    throwError "failed bridge did not roll back elaborator state"

  withLocalDeclD `signature (mkConst ``Signature) fun parameter => do
    let goal ← mkFreshExprMVar (← proposition parameter (toExpr Cstr.truth))
    let .failed _ ← solveGoal goal.mvarId! missing
      | throwError "open signature was accepted"
    if ← goal.mvarId!.isAssigned then throwError "open input failure assigned the original goal"

end LambdaRKBridgeChecks
