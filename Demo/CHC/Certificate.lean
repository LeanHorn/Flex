import Flex.CHC.Certificate
import Flex.CHC.Export
import Flex.Tactic.Oracles
import Auto.Solver.SMT

/-! Model candidates become ordinary Lean obligations even when a proof oracle
cannot finish. These tests use static models and need no external solver. -/
namespace CHCCertificateDemo

open Lean Meta Elab Tactic Qq Flex.CHC

private def check (condition : Bool) (message : String) : MetaM Unit :=
  unless condition do throwError message

private def prepare (formula : Expr) (model : String) :
    MetaM (MVarId × ExportedProblem × Array Witness × MVarId) := do
  let goal ← mkFreshExprMVar formula
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
  let problem ← exportConstraints kvars (← bodyGoal.getType)
  let witnesses ← importWitnesses problem
    (SolverResult.ofProcess { completion := .exited 0, stdout := model })
  return (goal.mvarId!, problem, witnesses, bodyGoal)

private def counter : Expr := q(∃ k : Int → Prop,
  k 0 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → 0 ≤ n))

private def counterModel : String :=
  "sat ((define-fun k_0 ((x Int)) Bool (>= x 0)))"

-- The certifier's residuals can be handed straight to an ordinary tactic.
elab "static_chc_certificate" : tactic => withMainContext do
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro (← getMainGoal)
  let problem ← exportConstraints kvars (← bodyGoal.getType)
  let witnesses ← importWitnesses problem
    (SolverResult.ofProcess { completion := .exited 0, stdout := counterModel })
  let result ← certifyWitnesses problem witnesses bodyGoal (fun _ => pure none)
  replaceMainGoal (result.obligations.toList.map (·.goal))

theorem manuallyFinished :
    ∃ k : Int → Prop,
      k 0 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → 0 ≤ n) := by
  static_chc_certificate
  all_goals omega

theorem siblingPreserved :
    (∃ k : Int → Prop,
      k 0 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → 0 ≤ n)) ∧ True := by
  constructor
  · static_chc_certificate
    all_goals omega
  · trivial

elab "smt_chc_certificate" : tactic => withMainContext do
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro (← getMainGoal)
  let problem ← exportConstraints kvars (← bodyGoal.getType)
  let witnesses ← importWitnesses problem
    (SolverResult.ofProcess { completion := .exited 0, stdout := counterModel })
  let result ← certifyWitnesses problem witnesses bodyGoal fun proposition => do
    proveLeafWith (← `(tactic| flex_smt [*])) proposition
  unless result.obligations.isEmpty do throwError "reconstructing SMT oracle left a VC"
  replaceMainGoal []

-- Exercise proof injection with real lean-smt reconstruction and no fallback.
theorem smtFinished :
    ∃ k : Int → Prop,
      k 0 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → 0 ≤ n) := by
  smt_chc_certificate

run_elab do
  let (goal, problem, witnesses, bodyGoal) ← prepare counter counterModel
  let result ← certifyWitnesses problem witnesses bodyGoal (fun _ => pure none)
  check (result.obligations.size == 3) "counter lost an unproved clause"
  check (result.provedHeads == 0 && result.provedQueries == 0)
    "nonterminal oracle was counted as a proof"
  check (result.obligations.map (·.clauseIndex) == #[0, 1, 2])
    "obligations lost their source clause indices"
  check (result.obligations.map (·.kind) == #[.head "k_0", .head "k_0", .query])
    "head/query classification was lost after instantiation"
  for witness in witnesses do
    check (← witness.mvarId.isAssigned) "partial certification discarded a witness"
  for obligation in result.obligations do
    obligation.goal.withContext do
      let target ← instantiateMVars (← obligation.goal.getType)
      check (!target.hasMVar && !target.isForall)
        "residual still contains internal metavariables or leading binders"
      for localDecl in ← getLCtx do
        let type ← instantiateMVars localDecl.type
        check (!type.hasMVar) "residual hypothesis still contains an internal metavariable"
    let pending ← Tactic.run obligation.goal do evalTactic (← `(tactic| omega))
    check pending.isEmpty "clean residual was not directly finishable by omega"
  let proof ← instantiateMVars (mkMVar goal)
  check (!proof.hasMVar && !proof.hasSorry) "manual completion left an incomplete proof"
  checkWithKernel proof

run_elab do
  let (goal, problem, witnesses, bodyGoal) ← prepare
    q(∃ k : Int → Prop,
      k 0 ∧ (∀ n, True → k n → k (n + 1)) ∧ (∀ n, k n → 0 ≤ n))
    "sat ((define-fun k_0 ((x Int)) Bool (and true (or false (>= x 0)))))"
  let result ← certifyWitnesses problem witnesses bodyGoal (fun _ => pure none)
  check (result.obligations.size == 3) "cleanup changed the number of arithmetic clauses"
  for obligation in result.obligations do
    obligation.goal.withContext do
      let target ← obligation.goal.getType
      check (target.and?.isNone && !target.isForall)
        "residual target still contains invariant scaffolding"
      for localDecl in ← getLCtx do
        check (!localDecl.type.isConstOf ``True && localDecl.type.and?.isNone)
          "residual hypothesis still contains a trivial guard or conjunction"
    let pending ← Tactic.run obligation.goal do evalTactic (← `(tactic| omega))
    check pending.isEmpty "cleaned noisy-model VC could not be finished directly"
  checkWithKernel (← instantiateMVars (mkMVar goal))

-- One invariant conjunction may split a single exported clause into several
-- goals; preserve shared provenance while giving each residual a unique tag.
run_elab do
  let (goal, problem, witnesses, bodyGoal) ← prepare q(∃ k : Int → Prop, k 0)
    "sat ((define-fun k_0 ((x Int)) Bool (and (>= x 0) (<= x 10))))"
  let result ← certifyWitnesses problem witnesses bodyGoal (fun _ => pure none)
  check (result.obligations.size == 2) "conjunctive invariant was not split"
  check (result.obligations.all (fun item => item.clauseIndex == 0 && item.kind == .head "k_0"))
    "split invariant lost its shared clause provenance"
  check ((← result.obligations[0]!.goal.getTag) != (← result.obligations[1]!.goal.getTag))
    "split obligations have duplicate goal tags"
  for obligation in result.obligations do
    let pending ← Tactic.run obligation.goal do evalTactic (← `(tactic| omega))
    check pending.isEmpty "split invariant obligation was not manually finishable"
  checkWithKernel (← instantiateMVars (mkMVar goal))

-- A proved head is removed independently of the other clauses.
run_elab do
  let (_, problem, witnesses, bodyGoal) ← prepare counter counterModel
  let result ← certifyWitnesses problem witnesses bodyGoal fun proposition => do
    if (← getLCtx).getFVarIds.isEmpty then defaultProofOracle proposition else pure none
  check (result.provedHeads == 1 && result.provedQueries == 0)
    "selective certification did not remove just the initialization head"
  check (result.obligations.map (·.clauseIndex) == #[1, 2])
    "selective certification discarded an unproved clause"

-- A well-typed but invalid solver candidate remains a VC, not a proof.
run_elab do
  let (_, problem, witnesses, bodyGoal) ← prepare counter
    "sat ((define-fun k_0 ((x Int)) Bool true))"
  let result ← certifyWitnesses problem witnesses bodyGoal
  check (!result.obligations.isEmpty) "invalid invariant was accepted as a complete proof"
  check (result.obligations.any (·.kind == .query))
    "invalid invariant lost its safety obligation"

-- Check indirect uses too: syntactic absence of sorry is not sufficient.
private theorem hiddenTrust (p : Prop) : p := autoSMTSorry p

private def rejectsOracle (oracle : ProofOracle) : TermElabM Unit := do
  let (_, problem, witnesses, bodyGoal) ← prepare q(∃ k : Int → Prop, k 0)
    "sat ((define-fun k_0 ((x Int)) Bool false))"
  let messages ← Core.getMessageLog
  let constants := (← getEnv).constants.toList.map (·.1)
  let result ← certifyWitnesses problem witnesses bodyGoal oracle
  check (result.provedHeads == 0 && result.provedQueries == 0 &&
    result.obligations.size == 1) "invalid oracle evidence closed False"
  check ((← Core.getMessageLog).toList.length == messages.toList.length)
    "oracle failure leaked messages"
  check ((← getEnv).constants.toList.map (·.1) == constants)
    "oracle failure leaked temporary declarations"
  result.obligations[0]!.goal.withContext do
    check (← isDefEq (← result.obligations[0]!.goal.getType) q(False))
      "invalid oracle changed the residual proposition"

run_elab do
  rejectsOracle (fun _ => pure (some q(True.intro)))
  rejectsOracle (fun proposition => return some (← mkSorry proposition true))
  rejectsOracle (fun proposition => return some (← mkFreshExprMVar proposition))
  rejectsOracle (fun proposition => return some (← mkAppM ``hiddenTrust #[proposition]))
  rejectsOracle (fun proposition => do
    return some (← mkAuxTheorem proposition (← mkSorry proposition true)))
  rejectsOracle (fun proposition => do
    let name ← mkFreshUserName `untrustedOracleAxiom
    addDecl (.axiomDecl { name, levelParams := [], type := proposition, isUnsafe := false })
    return some (mkConst name))
  rejectsOracle (fun _ => do
    logError "this deliberately failing oracle must be silent"
    throwError "oracle failed")
  let sibling ← mkFreshExprMVar q(True)
  rejectsOracle (fun _ => do
    sibling.mvarId!.assign q(True.intro)
    return some q(True.intro))
  check (!(← sibling.mvarId!.isAssigned)) "oracle assigned an unrelated caller goal"

-- Whole-call validation is atomic, including already prepared witness slots.
run_elab do
  let (_, problem, witnesses, bodyGoal) ← prepare counter counterModel
  let before ← getMCtx
  let rejected ← try
    discard <| certifyWitnesses problem
      (witnesses.set! 0 { witnesses[0]! with value := q(0 : Nat) }) bodyGoal
    pure false
  catch _ => pure true
  check rejected "ill-typed witness bundle was accepted"
  check ((← getMCtx).decls.toList.map (·.1) == before.decls.toList.map (·.1) &&
    (← getMCtx).eAssignment.toList == before.eAssignment.toList)
    "failed certification leaked metavariables or assignments"
  check (!(← bodyGoal.isAssigned) && !(← witnesses[0]!.mvarId.isAssigned))
    "failed certification partially assigned the body or witness"
  -- This check fails after witness assignment and proof scaffolding, so it also
  -- exercises rollback of work already performed inside the certifier.
  let rejected ← try
    discard <| certifyWitnesses { problem with clauseCount := problem.clauseCount + 1 }
      witnesses bodyGoal
    pure false
  catch _ => pure true
  check rejected "mismatched body/export metadata was accepted"
  check ((← getMCtx).decls.toList.map (·.1) == before.decls.toList.map (·.1) &&
    (← getMCtx).eAssignment.toList == before.eAssignment.toList)
    "late certification failure retained witness assignments or proof scaffolding"

run_elab do
  for name in [``manuallyFinished, ``siblingPreserved, ``smtFinished] do
    let axioms ← collectAxioms name
    check (!axioms.contains ``sorryAx && !axioms.contains ``autoSMTSorry)
      "unchecked evidence leaked into the completed theorem"

end CHCCertificateDemo
