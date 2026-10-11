import Flex.CHC

/-! Public goal API regressions. Solver fixtures keep failures reproducible;
`Instantiate.lean` separately checks the real Spacer/Eldarica executables. -/
namespace CHCGoalDemo

open Lean Meta Elab Tactic Qq Flex.CHC

private def check (condition : Bool) (message : String) : MetaM Unit :=
  unless condition do throwError message

private def formula : Expr := q(∃ k : Bool → Int → Prop,
  (∀ b, k b 0) ∧ (∀ b n, k b n → k (Bool.not b) (n + 1)) ∧
  (∀ b n, k b n → 0 ≤ n))

-- The disjunctive guard expands the preservation clause into two clauses.
private def branchingFormula : Expr := q(∃ k : Bool → Int → Prop,
  (∀ b, k b 0) ∧ (∀ b n, (k b n ∨ n = 0) → k b (n + 1)) ∧
  (∀ b n, k b n → 0 ≤ n))

private structure Snapshot where
  constants : List Name
  metavariables : List MVarId
  assignments : List (MVarId × Expr)
  messages : Nat
  deriving BEq

private def snapshot : TermElabM Snapshot := do
  return {
    constants := (← getEnv).constants.toList.map (·.1)
    metavariables := (← getMCtx).decls.toList.map (·.1)
    assignments := (← getMCtx).eAssignment.toList
    messages := (← Core.getMessageLog).toList.length }

private def expectFailure (goal : MVarId) (config : Flex.CHC.Config) (stage : Stage)
    (hasTranscript : Bool) : TermElabM Unit := do
  let before ← snapshot
  let .failed failure ← solveGoal goal config
    | throwError "goal API unexpectedly succeeded"
  check (failure.stage == stage && !failure.message.isEmpty)
    s!"wrong failure stage or empty diagnostic: {repr failure.stage}"
  check (failure.solver.isSome == hasTranscript) "failure lost its solver transcript"
  check ((← snapshot) == before) "failed goal attempt did not restore caller state"

private def expectedScript (proposition : Expr) : MetaM String := do
  let saved ← Meta.saveState
  try
    let goal ← mkFreshExprMVar proposition
    let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
    let bodyGoal ← normalizeGoal bodyGoal
    return (← exportConstraints kvars (← bodyGoal.getType)).toSMTLib
  finally saved.restore

private def prepareFixture (directory : System.FilePath) (backend : Backend)
    (proposition : Expr) (mode : String) : TermElabM Flex.CHC.Config := do
  let name := if backend == .spacer then "spacer fixture" else "eldarica fixture"
  let executable := directory / name
  IO.FS.writeFile executable (← IO.FS.readFile "tests/fixtures/chc_backend.py")
  let chmod ← IO.Process.output { cmd := "chmod", args := #["+x", executable.toString] }
  check (chmod.exitCode == 0) "could not make solver fixture executable"
  IO.FS.writeFile (directory / "expected.smt2") (← expectedScript proposition)
  IO.FS.writeFile (directory / "mode") mode
  return { backend, executable := some executable.toString }

run_elab do
  let missing : Flex.CHC.Config := { executable := some "/flex-chc-test/does-not-exist" }
  let goal ← mkFreshExprMVar formula
  expectFailure goal.mvarId! missing .solver true
  expectFailure goal.mvarId! { missing with timeoutMs := 0 } .solver true
  let unsupported ← mkFreshExprMVar q(∃ k : Nat → Prop, k 0)
  expectFailure unsupported.mvarId! missing .exporting false
  let assigned ← mkFreshExprMVar q(True)
  assigned.mvarId!.assign q(True.intro)
  expectFailure assigned.mvarId! missing .prepare false
  -- The current export fragment requires parameters inside the constraint body.
  let ambient ← withLocalDeclD `outside q(Int) fun outside => do
    let outside : Q(Int) := outside
    mkFreshExprMVar q(∃ k : Int → Prop, k $outside)
  expectFailure ambient.mvarId! missing .exporting false

  let branching ← mkFreshExprMVar branchingFormula
  let originalType ← branching.mvarId!.getType
  let before ← snapshot
  let .failed failure ← solveGoal branching.mvarId! missing defaultProofOracle 3
    | throwError "clause expansion exceeded the supplied limit"
  check (failure.stage == .prepare && failure.solver.isNone && !failure.message.isEmpty)
    "expansion limit did not fail during preparation before launching a solver"
  check ((← snapshot) == before && !(← branching.mvarId!.isAssigned) &&
    (← branching.mvarId!.getType) == originalType)
    "expansion-limit failure changed the original existential or caller state"

run_elab do
  if System.Platform.isWindows then return
  IO.FS.withTempDir fun directory => do
    for backend in [.spacer, .eldarica] do
      let config ← prepareFixture directory backend formula "sat"
      let sibling ← mkFreshExprMVar q(True)
      let goal ← mkFreshExprMVar formula
      let report ← match ← solveGoal goal.mvarId! config with
        | .solved report => pure report
        | .partial report =>
          let remaining ← report.certificate.obligations.mapM fun item => do
            item.goal.withContext do return m!"{repr item.kind}: {← item.goal.getType}"
          throwError "valid model left VCs: {remaining}"
        | .failed failure => throwError "valid model failed at {repr failure.stage}: {failure.message}"
      check report.certificate.obligations.isEmpty "solved report contains obligations"
      check (report.witnesses.size == 1 && report.problem.relations.size == 1)
        "goal report lost its model metadata"
      check (report.solver.outcome matches .sat _) "goal report lost its solver result"
      check (report.timings.map (·.stage) ==
        #[.prepare, .exporting, .solver, .importing, .certificate])
        "successful goal report lost a pipeline phase timing"
      check (!(← sibling.mvarId!.isAssigned)) "goal API assigned an unrelated sibling"
      let proof ← instantiateMVars goal
      check (!proof.hasMVar && !proof.hasSorry) "solved result contains incomplete evidence"
      checkWithKernel proof

      let goal ← mkFreshExprMVar formula
      let .partial report ← solveGoal goal.mvarId! config (fun _ => pure none)
        | throwError "nonterminal proof oracle did not leave partial progress"
      check (!report.certificate.obligations.isEmpty) "partial report omitted its VCs"
      for witness in report.witnesses do
        check (← witness.mvarId.isAssigned) "partial result lost witness assignment"
      for obligation in report.certificate.obligations do
        let pending ← Tactic.run obligation.goal do
          evalTactic (← `(tactic| simp_all <;> omega))
        check pending.isEmpty "partial VC could not be finished manually"
      let proof ← instantiateMVars goal
      check (!proof.hasMVar && !proof.hasSorry) "manual completion left an incomplete proof"
      checkWithKernel proof

    let config ← prepareFixture directory .spacer formula "sat"
    for mode in ["malformed", "solver-error", "unsat", "unknown"] do
      IO.FS.writeFile (directory / "mode") mode
      let goal ← mkFreshExprMVar formula
      expectFailure goal.mvarId! config .solver true
    IO.FS.writeFile (directory / "mode") "timeout"
    let goal ← mkFreshExprMVar formula
    let before ← snapshot
    let .failed failure ← solveGoal goal.mvarId! { config with timeoutMs := 1000 }
      | throwError "timed-out solver unexpectedly produced a witness result"
    check (failure.stage == .solver &&
      failure.solver.any (fun solver => solver.outcome matches .timedOut))
      "timeout failure lost its solver transcript or failure stage"
    check ((← snapshot) == before) "timeout left partial witness assignments"
    IO.FS.writeFile (directory / "mode") "empty"
    let goal ← mkFreshExprMVar formula
    expectFailure goal.mvarId! config .importing true
    -- The transcript is well formed but gives the wrong relation signature.
    let intOnly := q(∃ k : Int → Prop, k 0)
    let config ← prepareFixture directory .spacer intOnly "sat"
    let goal ← mkFreshExprMVar intOnly
    expectFailure goal.mvarId! config .importing true

    let invalid := q(∃ k : Bool → Int → Prop, k true (-1))
    let config ← prepareFixture directory .spacer invalid "sat"
    let goal ← mkFreshExprMVar invalid
    let .partial report ← solveGoal goal.mvarId! config
      | throwError "invalid candidate did not retain its unproved initialization VC"
    check (report.certificate.obligations.size == 1 &&
      report.certificate.obligations[0]!.kind == .head "k_0")
      "invalid candidate lost its failed head"

    let config ← prepareFixture directory .spacer q(True) "empty"
    let goal ← mkFreshExprMVar q(True)
    let .solved report ← solveGoal goal.mvarId! config
      | throwError "empty model could not certify a ground True goal"
    check report.witnesses.isEmpty "ground goal acquired existential witnesses"

    -- The same goal that exceeded a limit of three succeeds when the caller
    -- allows its four normalized clauses, proving the original proposition.
    let config ← prepareFixture directory .spacer branchingFormula "sat"
    let goal ← mkFreshExprMVar branchingFormula
    let .solved report ← solveGoal goal.mvarId! config defaultProofOracle 4
      | throwError "valid clause-limit override did not permit normalized certification"
    check (report.problem.clauseCount == 4)
      "normalization did not expose the expected four Horn clauses"
    let proof ← instantiateMVars goal
    check (!proof.hasMVar && !proof.hasSorry)
      "normalized goal completion left unresolved proof obligations"
    checkWithKernel proof

    -- Unused ambient parameters must not stop an otherwise closed export.
    let config ← prepareFixture directory .spacer formula "sat"
    let goal ← withLocalDeclD `unused q(Int) fun _ => mkFreshExprMVar formula
    let .solved _ ← solveGoal goal.mvarId! config
      | throwError "unused ambient local prevented goal certification"

end CHCGoalDemo
