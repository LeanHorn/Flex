import Flex.CHC.Witness
import Flex.PA.Check
import Flex.Zap.Emit
import Smt

namespace Flex.CHC

open Lean Meta Elab Term

/-- Prove an instantiated clause. Failure or invalid evidence leaves an obligation;
callback state and messages are discarded, and interrupts propagate. -/
abbrev ProofOracle := Expr → TermElabM (Option Expr)

/-- Per-attempt proof budget; zero disables that resource's attempts. -/
structure ProofConfig where
  heartbeats : Nat := 20000
  smtTimeout : Nat := 30

private def tryProof (config : ProofConfig) (tactic : TSyntax `tactic)
    (goal : Expr) : TermElabM (Option Expr) := do
  let mut limit := config.heartbeats * 1000
  let outerLimit ← getMaxHeartbeats
  if outerLimit != 0 then
    -- Reserve half the caller's budget for cleanup and the residual proof scaffold.
    limit := min limit ((← getRemainingHeartbeats) - outerLimit / 2)
  if limit == 0 then return none
  let saved ← Term.saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx =>
        { ctx with maxHeartbeats := limit }) <|
      Core.withCurrHeartbeats do
        let result ← proveLeafWith tactic goal
        if result.isNone then saved.restore
        return result)
    (fun _ => do saved.restore; return none)

/-- Try bounded Lean automation, then lean-smt with proof reconstruction. -/
def proofOracle (config : ProofConfig := {}) : ProofOracle := fun goal => do
  for tactic in #[← `(tactic| omega), ← `(tactic| grind)] do
    if let some proof ← tryProof config tactic goal then return some proof
  let needsSearch := fun e : Expr =>
    (e.find? fun e => e.isAppOfArity ``Exists 2 || e.isAppOfArity ``Or 2).isSome
  if needsSearch goal || (← getLCtx).any (needsSearch ·.type) then
    if let some proof ← tryProof config
        (← `(tactic| aesop (config := { maxRuleApplications := 200 })
          (add unsafe 20% (by omega)))) goal then
      return some proof
  if config.smtTimeout == 0 then return none
  let timeout := quote config.smtTimeout
  tryProof config
    (← `(tactic| smt (timeout := some $timeout) (trust := false) [*] <;>
      first | omega | grind)) goal

def defaultProofOracle : ProofOracle := proofOracle {}

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
  residualVC : Option MVarId := none
  provedHeads : Nat := 0
  provedQueries : Nat := 0
  deriving Inhabited

/-- All remaining goals, including a structure-preserving residual when present. -/
def CertificateResult.goals (result : CertificateResult) : Array MVarId :=
  match result.residualVC with
  | none => result.obligations.map (·.goal)
  | some goal => (result.obligations.map (·.goal)).push goal

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
  let limit ← getMaxHeartbeats
  let reserved ← if limit == 0 then pure 0 else pure ((← getRemainingHeartbeats) / 4)
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := limit - reserved }) do
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
      finally restoreTermState saved)
    (fun _ => do restoreTermState saved; return none)

/-- Reduce beta, let, and metadata wrappers, preserving readable definitions. -/
private def normalize (expression : Expr) : MetaM Expr := do
  let expression ← instantiateMVars expression
  Core.transform expression (pre := fun current => do
    let exposed := current.consumeMData.headBeta
    match exposed with
    | .letE _ _ value body _ => return .visit (body.instantiate1 value)
    | _ => return if exposed == current then .continue else .visit exposed)

private structure WalkState where
  cleanupContext : Simp.Context
  cleanupCache : ExprStructMap (Expr × Expr) := {}
  result : CertificateResult := {}
  nextClause : Nat := 0

private abbrev CertM := StateT WalkState TermElabM

/-- Only logical cleanup: no user simp lemmas or arithmetic unfolding. -/
private def cleanupContext : MetaM Simp.Context := do
  let mut lemmas : SimpTheorems := {}
  for name in #[``eq_self, ``and_true, ``true_and, ``and_false, ``false_and,
      ``or_true, ``true_or, ``or_false, ``false_or, ``and_self, ``or_self,
      ``not_true_eq_false, ``not_false_eq_true, ``not_not, ``iff_self,
      ``true_implies, ``false_implies, ``imp_true_iff,
      ``ite_true, ``ite_false, ``ite_self,
      ``exists_eq, ``exists_eq', ``exists_eq_left, ``exists_eq_left',
      ``exists_eq_right, ``exists_eq_right', ``exists_eq_right_right,
      ``exists_eq_right_right', ``exists_false] do
    lemmas ← lemmas.addConst name
  Simp.mkContext { maxSteps := 10000, decide := false, failIfUnchanged := false }
    #[lemmas]

/-- Cleanup is optional and bounded; its cache contains only context-independent rewrites. -/
private def cleanup (raw : Expr) : CertM (Expr × Expr) := do
  let raw ← instantiateMVars raw
  if let some result := (← get).cleanupCache[ExprStructEq.mk raw]? then return result
  let context := (← get).cleanupContext
  let simplify : MetaM (Expr × Expr) := do
    let saved ← Meta.saveState
    let remaining ← getRemainingHeartbeats
    let limit := if (← getMaxHeartbeats) == 0 then 5000000
      else min 5000000 (remaining / 4)
    if limit == 0 then return (raw, mkApp (mkConst ``Iff.refl) raw)
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := limit }) <|
        Core.withCurrHeartbeats do
          let target ← normalize raw
          let (result, _) ← Meta.simp target context
          return (result.expr,
            mkApp3 (mkConst ``Iff.of_eq) target result.expr (← result.getProof)))
      (fun error => do
        saved.restore
        unless error.isRuntime do throw error
        return (raw, mkApp (mkConst ``Iff.refl) raw))
  let result ← liftM simplify
  modify fun s => { s with cleanupCache := s.cleanupCache.insert raw result }
  return result

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
      -- Retry only after conjunction splitting, not after introducing a binder.
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
  let (target, equivalence) ← cleanup raw
  if target.hasMVar || target.hasLevelMVar then
    throwError "CHC certification: unresolved variables remain in an instantiated clause"
  let proof ← residual oracle tag kind index target
  if (← get).result.obligations.size == before then
    modify fun s => { s with result := match kind with
      | .head _ => { s.result with provedHeads := s.result.provedHeads + 1 }
      | .query => { s.result with provedQueries := s.result.provedQueries + 1 } }
  return mkApp4 (mkConst ``Iff.mpr) raw target equivalence proof

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
      let (cleanDomain, equivalence) ← cleanup domain
      if cleanDomain.isConstOf ``True then
        let originalProof ←
          if cleanDomain == domain then
            pure (Lean.mkConst ``True.intro)
          else pure (mkApp4 (mkConst ``Iff.mpr) domain cleanDomain equivalence (mkConst ``True.intro))
        let proof ← walk relations oracle tag (body.instantiate1 originalProof)
        return ← abstractBinder name bi domain fun _ => pure proof
      if cleanDomain != domain then
        let cleanProof ← abstractBinder name bi cleanDomain fun hypothesis => do
          let originalProof := mkApp4 (mkConst ``Iff.mpr) domain cleanDomain equivalence hypothesis
          walk relations oracle tag (body.instantiate1 originalProof)
        return ← abstractBinder name bi domain fun hypothesis => do
          let cleanedHypothesis := mkApp4 (mkConst ``Iff.mp) domain cleanDomain equivalence hypothesis
          return cleanProof.beta #[cleanedHypothesis]
    return ← abstractBinder name bi domain fun parameter =>
      walk relations oracle tag (body.instantiate1 parameter)
  if let some (left, right) := raw.and? then
    return mkAndIntro left right
      (← walk relations oracle tag left)
      (← walk relations oracle tag right)
  certifyLeaf oracle tag .query raw

/-- Replace certified κ-heads by True, retaining the original constraint tree.
The returned equivalence closes every temporary binder before it escapes. -/
private partial def walkHeads (relations : Array Relation) (oracle : ProofOracle)
    (raw : Expr) : CertM (Expr × Expr) := do
  let raw ← Prepare.expose raw
  if raw.getAppFn.isMVar then
    unless relations.any (·.kvar.mvarId == raw.getAppFn.mvarId!) do
      throwError "CHC certification: unregistered predicate head"
    let (target, equivalence) ← cleanup raw
    let proof? ← if target.isConstOf ``True then pure (some (Lean.mkConst ``True.intro))
      else tryOracle oracle target
    if let some proof := proof? then
      modify fun s => { s with result.provedHeads := s.result.provedHeads + 1 }
      let proof := mkApp4 (mkConst ``Iff.mpr) raw target equivalence proof
      return (mkConst ``True, mkApp2 (mkConst ``iff_true_intro) raw proof)
    return (target, equivalence)
  if let .forallE name domain body bi := raw then
    let domain ← normalize domain
    if ← isProp domain then
      if body.hasLooseBVar 0 then
        throwError "CHC certification: constraints depending on proof terms are unsupported"
      let (cleanDomain, domainIff) ← cleanup domain
      if cleanDomain != domain then
        let (target, bodyIff) ← withLocalDecl name bi cleanDomain fun parameter => do
          let hypothesis := mkApp4 (mkConst ``Iff.mpr) domain cleanDomain domainIff parameter
          let (reduced, equivalence) ← walkHeads relations oracle (body.instantiate1 hypothesis)
          return (← mkForallFVars #[parameter] reduced,
            ← mkAppM ``forall_congr' #[← mkLambdaFVars #[parameter] equivalence])
        let domainBridge ← mkAppM ``imp_congr
          #[domainIff, ← mkAppM ``Iff.refl #[body.instantiate1 (Lean.mkConst ``True.intro)]]
        return (target, ← mkAppM ``Iff.trans #[domainBridge, bodyIff])
    return ← withLocalDecl name bi domain fun parameter => do
      let (reduced, equivalence) ← walkHeads relations oracle (body.instantiate1 parameter)
      let target ← mkForallFVars #[parameter] reduced
      let motive ← mkLambdaFVars #[parameter] equivalence
      return (target, ← mkAppM ``forall_congr' #[motive])
  if let some (left, right) := raw.and? then
    let (left', leftIff) ← walkHeads relations oracle left
    let (right', rightIff) ← walkHeads relations oracle right
    return (mkApp2 (mkConst ``And) left' right',
      ← mkAppM ``and_congr #[leftIff, rightIff])
  cleanup raw

/-- Construct a checked bridge and at most one residual in the body's context. -/
private def certifyHeads (relations : Array Relation) (oracle : ProofOracle)
    (tag : Name) (raw : Expr) (context : Simp.Context)
    : TermElabM (Expr × CertificateResult) := do
  let ((reduced, equivalence), state) ←
    (walkHeads relations oracle raw).run { cleanupContext := context }
  let ((target, cleanup), _) ← (cleanup reduced).run state
  let equivalence ← instantiateMVars (← mkAppM ``Iff.trans #[equivalence, cleanup])
  if equivalence.hasMVar || equivalence.hasLevelMVar then
    throwError "CHC certification: residual equivalence contains unresolved variables"
  checkWithKernel equivalence
  if target.isConstOf ``True then
    return (← mkAppM ``Iff.mpr #[equivalence, mkConst ``True.intro], state.result)
  let residual ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
    (userName := tag ++ `vc)
  return (← mkAppM ``Iff.mpr #[equivalence, residual],
    { state.result with residualVC := some residual.mvarId! })

/-- Assign candidates and certify the original body, leaving unproved clauses as
Lean goals. Partial results retain assignments and the proof scaffold; errors
restore all entry state. Oracle evidence is checked in the original context.
With `headsOnly`, certify only κ-heads and retain one structured residual VC.
Does not change the tactic goal list. -/
def certifyWitnesses (problem : ExportedProblem) (witnesses : Array Witness)
    (bodyGoal : MVarId) (oracle : ProofOracle := defaultProofOracle)
    (headsOnly : Bool := false)
    : TermElabM CertificateResult := do
  let saved ← Term.saveState
  let committed ← IO.mkRef false
  try
    let result ← bodyGoal.withContext do
      if ← bodyGoal.isAssignedOrDelayedAssigned then
        throwError "CHC certification: the body goal is already assigned"
      -- Capture κ applications before the assignment; they carry head provenance.
      let raw ← instantiateMVars (← bodyGoal.getType)
      assignWitnesses problem witnesses
      let instantiated ← instantiateMVars raw
      if instantiated.hasMVar || instantiated.hasLevelMVar then
        throwError "CHC certification: unresolved variables remain in the original body"
      let assigned ← Term.saveState
      let detailed : TermElabM CertificateResult := do
        let context ← cleanupContext
        let (proof, result) ← if headsOnly then
            certifyHeads problem.relations oracle (← bodyGoal.getTag) raw context
          else do
            let (proof, state) ←
              (walk problem.relations oracle (← bodyGoal.getTag) raw).run
                { cleanupContext := context }
            unless state.nextClause == problem.clauseCount do
              throwError "CHC certification: body and exported clause count disagree"
            pure (proof, state.result)
        let proof ← instantiateMVars proof
        if result.goals.isEmpty && (proof.hasMVar || proof.hasLevelMVar) then
          throwError "CHC certification: completed certificate contains unresolved variables"
        -- Partial scaffolds contain goals, so only completed proofs use the kernel.
        if result.goals.isEmpty then checkWithKernel proof else check proof
        unless ← isDefEq (← inferType proof) (← bodyGoal.getType) do
          throwError "CHC certification: certificate does not prove the original body"
        bodyGoal.assign proof
        return result
      -- Reserve space for a typed residual if detailed proof construction reaches a limit.
      let limit ← getMaxHeartbeats
      let reserved ← if limit == 0 then pure 0 else pure ((← getRemainingHeartbeats) / 4)
      tryCatchRuntimeEx
        (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := limit - reserved })
          detailed)
        (fun error => do
          unless error.isRuntime do throw error
          restoreTermState assigned
          let remaining ← getRemainingHeartbeats
          let cleanupLimit := if (← getMaxHeartbeats) == 0 then 5000000
            else max 1 (min 5000000 (remaining / 2))
          let target ← tryCatchRuntimeEx
            (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := cleanupLimit }) <|
              Core.withCurrHeartbeats <| normalize instantiated)
            (fun error => do
              unless error.isRuntime do throw error
              pure instantiated)
          let residual ← mkFreshExprMVar target (kind := .syntheticOpaque)
            (userName := (← bodyGoal.getTag) ++ `vc)
          bodyGoal.assign residual
          return { residualVC := some residual.mvarId! })
    committed.set true
    return result
  finally
    unless ← committed.get do restoreTermState saved

end Flex.CHC
