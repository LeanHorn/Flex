import Flex.CHC.Witness
import Flex.CHC.Prepare
import Flex.PA.Check
import Flex.Zap.Emit

namespace Flex.CHC

open Lean Meta Elab Term

/-- A proof-producing callback, run in the context of one instantiated clause.
Returning `none`, throwing, or returning invalid evidence leaves an obligation.
The callback's elaborator state and messages never escape the invocation. -/
abbrev ProofOracle := Expr → TermElabM (Option Expr)

/-- Reuse Flex's existing proof-producing Lean automation. Callers may supply a
different oracle, including a proof-reconstructing SMT tactic. -/
def defaultProofOracle : ProofOracle := proveLeaf

/-- Provenance is recorded before substituting the solver's predicates. -/
inductive ObligationKind where
  | head (symbol : String)
  | query
  deriving BEq, Repr, Inhabited

/-- An ordinary Lean goal left by certification. `clauseIndex` is zero-based
and follows the exporter's depth-first flattened clause order. Splitting one
instantiated clause may produce several goals with the same index. -/
structure Obligation where
  goal : MVarId
  kind : ObligationKind
  clauseIndex : Nat
  deriving Inhabited

/-- Counts refer to fully discharged original clauses, not individual conjuncts
of a candidate predicate. Remaining obligations already have their witnesses
instantiated and their structural noise removed. -/
structure CertificateResult where
  obligations : Array Obligation := #[]
  provedHeads : Nat := 0
  provedQueries : Nat := 0
  deriving Inhabited

private def restoreExactly (saved : Term.SavedState) : TermElabM Unit := do
  set saved.elab
  modifyThe Meta.State fun _ => saved.meta.meta
  modifyThe Core.State fun _ => saved.meta.core.toState

private def checkEvidence (target proof : Expr) : TermElabM Unit := do
  if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "CHC certification: oracle returned unresolved or admitted evidence"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do
    throwError "CHC certification: oracle returned evidence for a different proposition"
  -- `hasSorry` alone misses a theorem that transitively uses a trusted SMT axiom.
  for name in proof.getUsedConstants do
    for axiomName in (← collectAxioms name) do
      if axiomName == ``sorryAx || axiomName == `autoSMTSorry ||
          axiomName == `Auto.autoSMTSorry then
        throwError "CHC certification: oracle evidence depends on {axiomName}"

/-- Revalidate after restoring the caller's state: an oracle cannot justify a
proof by assigning other goals or adding an unchecked temporary declaration. -/
private def tryOracle (oracle : ProofOracle) (target : Expr) : TermElabM (Option Expr) := do
  let saved ← Term.saveState
  try
    let result ← withNewMCtxDepth <| oracle target
    -- Existing tactic adapters can catch an interrupt as ordinary failure.
    Core.checkInterrupted
    let candidate ← result.mapM instantiateMVars
    let oracleEnvironment ← getEnv
    restoreExactly saved
    let some proof := candidate | return none
    -- `omega` and other tactics may abstract proofs into fresh helper theorems.
    -- Inline only those new declarations, rather than committing the callback's
    -- environment. Lean's bounded traversal also handles nested abstractions.
    let proof ← Meta.unfoldDeclsFrom oracleEnvironment proof
    checkEvidence target proof
    return some proof
  catch error =>
    if error.isInterrupt then throw error
    return none
  finally restoreExactly saved

/-- Only beta, let, and metadata reduction. Definitions and arithmetic operators
are deliberately retained so residual goals remain readable. -/
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

/-- Decompose a cleaned proposition only after a whole-clause proof attempt has
failed. This also handles conjunctions introduced by the invariant itself. -/
private partial def residual (oracle : ProofOracle) (tag : Name)
    (kind : ObligationKind) (clauseIndex : Nat) (target : Expr)
    (tryWhole : Bool := true) : CertM Expr := do
  if target.isConstOf ``True then return mkConst ``True.intro
  if tryWhole then
    if let some proof ← tryOracle oracle target then return proof
  if let .forallE name domain body bi := target then
    return ← withLocalDecl name bi domain fun parameter => do
      -- The failed whole-clause oracle already had access to these binders.
      -- Splitting a conjunction below may still justify independent attempts.
      let proof ← residual oracle tag kind clauseIndex (body.instantiate1 parameter)
        (tryWhole := false)
      mkLambdaFVars #[parameter] proof
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
  -- Beta/let normalization is definitional: unchanged propositions need no
  -- logical bridge around the oracle's (potentially large) proof.
  if target == normalized then return proof
  mkAppM ``Iff.mpr #[equivalence, proof]

/-- Traverse the original body without expanding assigned κ heads. Domains are
cleaned before introduction, so residual contexts contain readable hypotheses.
The `Iff` bridges retain a proof of the original, uncleaned constraint. -/
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
        return ← withLocalDecl name bi domain fun unused => mkLambdaFVars #[unused] proof
      if cleanDomain == domain then
        return ← withLocalDecl name bi domain fun hypothesis => do
          let proof ← walk relations oracle tag (body.instantiate1 hypothesis)
          mkLambdaFVars #[hypothesis] proof
      let cleanProof ← withLocalDecl name bi cleanDomain fun hypothesis => do
        let originalProof ← mkAppM ``Iff.mpr #[equivalence, hypothesis]
        let proof ← walk relations oracle tag (body.instantiate1 originalProof)
        mkLambdaFVars #[hypothesis] proof
      return ← withLocalDecl name bi domain fun hypothesis => do
        let cleanedHypothesis ← mkAppM ``Iff.mp #[equivalence, hypothesis]
        mkLambdaFVars #[hypothesis] (cleanProof.beta #[cleanedHypothesis])
    else
      return ← withLocalDecl name bi domain fun parameter => do
        let proof ← walk relations oracle tag (body.instantiate1 parameter)
        mkLambdaFVars #[parameter] proof
  if let some (left, right) := raw.and? then
    return mkAndIntro left right
      (← walk relations oracle tag left)
      (← walk relations oracle tag right)
  certifyLeaf oracle tag .query raw

/-- Assign a complete solver witness bundle and construct a certificate of the
original body, retaining each unproved head or query as an ordinary Lean goal.

Witnesses are candidates, never trusted proofs. Oracle evidence is checked in
the original context, with unresolved/admitted evidence rejected. All callback
elaborator-state changes and messages are discarded. A normal partial result retains witness
assignments and the body proof scaffold; any internal/validation error restores
the entire entry state. No tactic goal list is modified by this API.
-/
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
      -- A completed proof is checked by the kernel; repeating the full Meta
      -- checker adds no validation. Partial scaffolds still need the Meta check.
      if state.result.obligations.isEmpty then checkWithKernel proof else check proof
      unless ← isDefEq (← inferType proof) (← bodyGoal.getType) do
        throwError "CHC certification: certificate does not prove the original body"
      bodyGoal.assign proof
      return state.result
  catch error =>
    restoreExactly saved
    throw error

end Flex.CHC
