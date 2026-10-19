import Flex.CHC.Witness
import Flex.PA.Check
import Flex.Zap.Emit

namespace Flex.CHC

open Lean Meta Elab Term

/-- Prove an instantiated clause. Failure or invalid evidence leaves an obligation;
callback state and messages are discarded, and interrupts propagate. -/
abbrev ProofOracle := Expr → TermElabM (Option Expr)

/-- Flex's default proof-producing automation. -/
def defaultProofOracle : ProofOracle := proveLeaf

/-- Provenance is recorded before substituting the solver's predicates. -/
inductive ObligationKind where
  | head (symbol : String)
  | query
  deriving BEq, Repr, Inhabited

/-- A residual Lean goal. Clause indices are zero-based, in export order;
splitting a clause can produce several obligations with the same index. -/
structure Obligation where
  goal : MVarId
  kind : ObligationKind
  clauseIndex : Nat
  deriving Inhabited

/-- Counts refer to fully discharged clauses. Obligations have witnesses
instantiated and structural noise removed. -/
structure CertificateResult where
  obligations : Array Obligation := #[]
  provedHeads : Nat := 0
  provedQueries : Nat := 0
  deriving Inhabited

/-- Restore all elaborator, meta, and core state, including messages and caches. -/
def restoreTermState (saved : Term.SavedState) : TermElabM Unit := do
  set saved.elab
  restoreMetaState saved.meta

private def checkEvidence (target proof : Expr) : TermElabM Unit := do
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "CHC certification: oracle returned unresolved or admitted evidence"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do
    throwError "CHC certification: oracle returned evidence for a different proposition"
  -- Reject trusted SMT axioms hidden behind theorem constants as well.
  for name in proof.getUsedConstants do
    for axiomName in (← collectAxioms name) do
      if axiomName == ``sorryAx || axiomName == `autoSMTSorry ||
          axiomName == `Auto.autoSMTSorry then
        throwError "CHC certification: oracle evidence depends on {axiomName}"

/-- Check oracle evidence in the caller's state, independently of its mutations. -/
private def tryOracle (oracle : ProofOracle) (target : Expr) : TermElabM (Option Expr) := do
  let saved ← Term.saveState
  try
    let result ← withNewMCtxDepth <| oracle target
    -- Existing tactic adapters can catch an interrupt as ordinary failure.
    Core.checkInterrupted
    let candidate ← result.mapM instantiateMVars
    let oracleEnvironment ← getEnv
    restoreTermState saved
    let some proof := candidate | return none
    -- Inline fresh helper theorems (e.g. from omega) before kernel checking.
    let proof ← Meta.unfoldDeclsFrom oracleEnvironment proof
    checkEvidence target proof
    return some proof
  catch error =>
    if error.isInterrupt then throw error
    return none
  finally restoreTermState saved

/-- Reduce beta, let, and metadata wrappers, preserving readable definitions. -/
private def normalize (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  Core.transform expression (pre := fun current => do
    let exposed := current.consumeMData.headBeta
    match exposed with
    | .letE _ _ value body _ => return .visit (body.instantiate1 value)
    | _ => return if exposed == current then .continue else .visit exposed)

private structure WalkState where
  result : CertificateResult := {}
  nextClause : Nat := 0

private abbrev CertM := StateT WalkState TermElabM

private def abstractBinder (name : Name) (bi : BinderInfo) (domain : Expr)
    (body : Expr → CertM Expr) : CertM Expr :=
  withLocalDecl name bi domain fun parameter => do
    mkLambdaFVars #[parameter] (← body parameter)

private def addObligation (tag : Name) (kind : ObligationKind)
    (clauseIndex : Nat) (target : Expr) : CertM Expr := do
  let sequence := (← get).result.obligations.size + 1
  let suffix := match kind with
    | .head symbol => Name.mkSimple s!"{symbol}_head_{clauseIndex + 1}_{sequence}"
    | .query => Name.mkSimple s!"query_{clauseIndex + 1}_{sequence}"
  let goal ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
    (userName := tag ++ suffix)
  modify fun s => { s with result.obligations := s.result.obligations.push {
    goal := goal.mvarId!, kind, clauseIndex } }
  return goal

/-- Try whole clauses before splitting binders and invariant conjunctions. -/
private partial def residual (oracle : ProofOracle) (tag : Name)
    (kind : ObligationKind) (clauseIndex : Nat) (target : Expr)
    (tryWhole : Bool := true) : CertM Expr := do
  if target.isConstOf ``True then return mkConst ``True.intro
  if tryWhole then
    if let some proof ← tryOracle oracle target then return proof
  if let .forallE name domain body bi := target then
    return ← abstractBinder name bi domain fun parameter =>
      -- Retry only after splitting: the failed oracle already saw this binder.
      residual oracle tag kind clauseIndex (body.instantiate1 parameter)
        (tryWhole := false)
  if let some (left, right) := target.and? then
    return mkAndIntro left right
      (← residual oracle tag kind clauseIndex left)
      (← residual oracle tag kind clauseIndex right)
  addObligation tag kind clauseIndex target

private def certifyLeaf (oracle : ProofOracle) (tag : Name)
    (kind : ObligationKind) (raw : Expr) : CertM Expr := do
  let index := (← get).nextClause
  modify fun s => { s with nextClause := index + 1 }
  let before := (← get).result.obligations.size
  let normalized ← normalize raw
  let (target, equivalence) ← collapseInert normalized
  if target.hasMVar || target.hasLevelMVar then
    throwError "CHC certification: unresolved variables remain in an instantiated clause"
  let proof ← residual oracle tag kind index target
  if (← get).result.obligations.size == before then
    modify fun s => { s with result := match kind with
      | .head _ => { s.result with provedHeads := s.result.provedHeads + 1 }
      | .query => { s.result with provedQueries := s.result.provedQueries + 1 } }
  -- Definitional normalization needs no logical bridge.
  if target == normalized then return proof
  mkAppM ``Iff.mpr #[equivalence, proof]

/-- Preserve κ-head provenance and clean hypotheses before introduction.
Equivalence bridges retain a proof of the original constraint. -/
private partial def walk (relations : Array Relation) (oracle : ProofOracle)
    (tag : Name) (raw : Expr) : CertM Expr := do
  let raw ← Prepare.expose raw
  if raw.getAppFn.isMVar then
    let some relation := relations.find? (·.kvar.mvarId == raw.getAppFn.mvarId!)
      | throwError "CHC certification: unregistered predicate head"
    return ← certifyLeaf oracle tag (.head relation.symbol) raw
  if raw.isConstOf ``True then return mkConst ``True.intro
  if let .forallE name domain body bi := raw then
    let domain ← normalize domain
    if ← isProp domain then
      if body.hasLooseBVar 0 then
        throwError "CHC certification: constraints depending on proof terms are unsupported"
      let (cleanDomain, equivalence) ← collapseInert domain
      if cleanDomain.isConstOf ``True then
        let originalProof ←
          if cleanDomain == domain then
            pure (Lean.mkConst ``True.intro)
          else mkAppM ``Iff.mpr #[equivalence, mkConst ``True.intro]
        let proof ← walk relations oracle tag (body.instantiate1 originalProof)
        return ← abstractBinder name bi domain fun _ => pure proof
      if cleanDomain != domain then
        let cleanProof ← abstractBinder name bi cleanDomain fun hypothesis => do
          let originalProof ← mkAppM ``Iff.mpr #[equivalence, hypothesis]
          walk relations oracle tag (body.instantiate1 originalProof)
        return ← abstractBinder name bi domain fun hypothesis => do
          let cleanedHypothesis ← mkAppM ``Iff.mp #[equivalence, hypothesis]
          return cleanProof.beta #[cleanedHypothesis]
    return ← abstractBinder name bi domain fun parameter =>
      walk relations oracle tag (body.instantiate1 parameter)
  if let some (left, right) := raw.and? then
    return mkAndIntro left right
      (← walk relations oracle tag left)
      (← walk relations oracle tag right)
  certifyLeaf oracle tag .query raw

/-- Assign candidates and certify the original body, leaving unproved clauses as
Lean goals. Partial results retain assignments and the proof scaffold; errors
restore all entry state. Oracle evidence is checked in the original context.
Does not change the tactic goal list. -/
def certifyWitnesses (problem : ExportedProblem) (witnesses : Array Witness)
    (bodyGoal : MVarId) (oracle : ProofOracle := defaultProofOracle)
    : TermElabM CertificateResult := do
  let saved ← Term.saveState
  try
    bodyGoal.withContext do
      if ← bodyGoal.isAssignedOrDelayedAssigned then
        throwError "CHC certification: the body goal is already assigned"
      -- Capture κ applications before the assignment; they carry head provenance.
      let raw ← instantiateMVars (← bodyGoal.getType)
      assignWitnesses problem witnesses
      let instantiated ← instantiateMVars raw
      if instantiated.hasMVar || instantiated.hasLevelMVar then
        throwError "CHC certification: unresolved variables remain in the original body"
      let (proof, state) ← (walk problem.relations oracle (← bodyGoal.getTag) raw).run {}
      unless state.nextClause == problem.clauseCount do
        throwError "CHC certification: body and exported clause count disagree"
      let proof ← instantiateMVars proof
      if state.result.obligations.isEmpty && (proof.hasMVar || proof.hasLevelMVar) then
        throwError "CHC certification: completed certificate contains unresolved variables"
      -- Partial scaffolds contain goals, so only completed proofs use the kernel.
      if state.result.obligations.isEmpty then checkWithKernel proof else check proof
      unless ← isDefEq (← inferType proof) (← bodyGoal.getType) do
        throwError "CHC certification: certificate does not prove the original body"
      bodyGoal.assign proof
      return state.result
  catch error =>
    restoreTermState saved
    throw error

end Flex.CHC
