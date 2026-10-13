import Flex.VCG.LambdaRK.Bridge.Flatten
import Flex.VCG.LambdaRK.Bridge.Quote
import Flex.VCG.LambdaRK.Bridge.Read
import Flex.VCG.LambdaRK.Bridge.Reconstruct
import Flex.CHC.Goal

/-!
Checked lowering of a closed λRK verification condition. The executable compiler
only proposes scalar clauses: each proposal must first prove its implication to
the exact source clause. Solver witnesses are then certified by the shared CHC
API. Anything outside the supported fragment remains an ordinary source goal.
-/
namespace LambdaRK.Bridge

open Lean Meta Elab Term

/-- Source locations survive lowering, including failures of proof reconstruction. -/
structure Diagnostic where
  clauseIndex : Nat
  path : List Nat
  message : String
  deriving Repr

structure Obligation where
  goal : MVarId
  /-- Original index for a source residual. Scalar certificate provenance remains
  in `GoalReport.solver`; predicate witness goals have no clause index. -/
  sourceClause : Option Nat := none

structure GoalReport where
  solver : Option Flex.CHC.GoalReport := none
  witnesses : Array (String × Lean.Expr) := #[]
  diagnostics : Array Diagnostic := #[]
  obligations : Array Obligation := #[]
  checkedClauses : Nat := 0
  sourceClauses : Nat := 0

inductive GoalResult where
  | solved (report : GoalReport)
  | «partial» (report : GoalReport)
  | failed (message : String)

private structure Prepared where
  scalarGoal : Lean.Expr
  synthesized : Array Bool
  /-- Closed over all source predicate slots, including residual-only slots. -/
  bridges : Array (Option Lean.Expr)
  diagnostics : Array Diagnostic
  checkedClauses : Nat

private def withPredicates (declarations : Array KDecl)
    (action : Array Lean.Expr → TermElabM α) : TermElabM α :=
  go 0 #[]
where
  go (index : Nat) (parameters : Array Lean.Expr) : TermElabM α := do
    if h : index < declarations.size then
      let declaration := declarations[index]
      withLocalDeclD (Name.mkSimple declaration.name) (← predicateTypeExpr declaration)
        fun parameter => go (index + 1) (parameters.push parameter)
    else action parameters
  termination_by declarations.size - index

private def scalarRelation (declaration : KDecl) : Bool :=
  declaration.args.all (fun sort => sort != .value)

private def sourceType (signature assignment : Lean.Expr) (source : SourceClause) : Lean.Expr :=
  mkApp3 (mkConst ``Cstr.Valid) signature assignment (toExpr source.constraint)

private def prepare (signature : Signature) (lowering : Lowering) : TermElabM Prepared :=
  withPredicates signature.kvars.toArray fun parameters => do
    let declarations := signature.kvars.toArray
    let assignment ← predicateAssignmentExpr (declarations.zip parameters)
    let relations := (declarations.zip parameters).map fun (declaration, parameter) =>
      (declaration.name, parameter)
    let mut bridges := #[]
    let mut diagnostics := #[]
    let mut scalarClauses := #[]
    for entry in lowering.clauses do
      let proposed : Except String (Lean.Expr × Lean.Expr) ← match entry.result with
        | .error message => pure (.error message)
        | .ok scalar => do
          let target ← scalarClauseExpr relations scalar
          let implication ← mkArrow target (sourceType (toExpr signature) assignment entry.source)
          match ← proveBridge implication with
          | some proof =>
              pure (.ok (target, ← mkLambdaFVars parameters proof (usedOnly := false)))
          | none => pure (.error "could not certify the proposed scalar lowering")
      match proposed with
      | .ok (target, proof) =>
          scalarClauses := scalarClauses.push target
          bridges := bridges.push (some proof)
      | .error message =>
          bridges := bridges.push none
          diagnostics := diagnostics.push {
            clauseIndex := entry.source.index, path := entry.source.path, message }
    let mut body := scalarClauses.foldr mkAnd (mkConst ``True)
    let synthesized := (declarations.zip parameters).map fun (declaration, parameter) =>
      scalarRelation declaration && body.containsFVar parameter.fvarId!
    for active in synthesized.reverse, parameter in parameters.reverse do
      if active then
        body ← mkAppM ``Exists #[← mkLambdaFVars #[parameter] body (usedOnly := false)]
    if body.hasFVar || body.hasMVar then
      throwError "λRK bridge: scalar goal contains an unsupported free parameter"
    return {
      scalarGoal := body
      synthesized
      bridges
      diagnostics
      checkedClauses := scalarClauses.size }

private def restoreExactly (saved : Term.SavedState) : TermElabM Unit := do
  set saved.elab
  modifyThe Meta.State fun _ => saved.meta.meta
  modifyThe Core.State fun _ => saved.meta.core.toState

/-- Synthesize the declared scalar predicates of `∃ κ, Cstr.Valid signature κ vc`.
The signature and VC must be closed terms. Unsupported clauses are retained with
source provenance and synthesized predicates substituted. Predicates taking
runtime `Value` arguments remain explicit witness goals. Failed backend attempts
restore the entry state; partial success commits only checked proof scaffolding.
This operation does not change the tactic goal list.
-/
def solveGoal (goal : MVarId) (config : Flex.CHC.Config := {})
    (oracle : Flex.CHC.ProofOracle := Flex.CHC.defaultProofOracle) : TermElabM GoalResult := do
  let saved ← Term.saveState
  try
    goal.withContext do
      let target ← whnf (← goal.getType)
      unless target.isAppOfArity ``Exists 2 do
        throwError "λRK bridge: expected ∃ κ, Cstr.Valid signature κ constraints"
      let domain := target.getArg! 0
      unless ← isDefEq domain (mkConst ``KAssignment) do
        throwError "λRK bridge: the existential must bind a runtime predicate assignment"
      let predicate := target.getArg! 1
      let (signatureExpression, signature, constraint) ← withLocalDeclD `κ domain fun assignment => do
        let body := predicate.beta #[assignment]
        unless body.isAppOfArity ``Cstr.Valid 3 do
          throwError "λRK bridge: expected Cstr.Valid signature κ constraints under the existential"
        unless ← isDefEq (body.getArg! 1) assignment do
          throwError "λRK bridge: validity must use the bound predicate assignment"
        return (body.getArg! 0, ← readSignature (body.getArg! 0),
          ← readConstraint (body.getArg! 2))
      let lowering := lower signature constraint
      let prepared ← prepare signature lowering
      let scalarGoal ← mkFreshExprMVar prepared.scalarGoal (kind := .syntheticOpaque)
      let mut report : GoalReport := {
        diagnostics := prepared.diagnostics
        checkedClauses := prepared.checkedClauses
        sourceClauses := lowering.clauses.size }
      if prepared.synthesized.any id then
        match ← Flex.CHC.solveGoal scalarGoal.mvarId! config oracle with
        | .failed failure =>
            throwError "λRK bridge: solver failed at {repr failure.stage}: {failure.message}"
        | .solved solver | .partial solver =>
            report := { report with
              solver := some solver
              obligations := solver.certificate.obligations.map fun obligation =>
                { goal := obligation.goal } }
      else if prepared.scalarGoal.isConstOf ``True then
        scalarGoal.mvarId!.assign (Lean.mkConst ``True.intro)
      else
        match ← Flex.CHC.checkOracleProof oracle prepared.scalarGoal with
        | some proof => scalarGoal.mvarId!.assign proof
        | none => report := { report with obligations := #[{ goal := scalarGoal.mvarId! }] }
      let mut scalarProof ← instantiateMVars scalarGoal
      let mut candidates := #[]
      for declaration in signature.kvars.toArray, active in prepared.synthesized do
        if active then
          scalarProof ← whnf scalarProof
          unless scalarProof.isAppOfArity ``Exists.intro 4 do
            throwError "λRK bridge: solver certificate did not expose its predicate witnesses"
          let candidate := scalarProof.getArg! 2
          candidates := candidates.push candidate
          report := { report with witnesses := report.witnesses.push (declaration.name, candidate) }
          scalarProof := scalarProof.getArg! 3
        else
          let candidate ← mkFreshExprMVar (← predicateTypeExpr declaration)
            (kind := .syntheticOpaque) (userName := Name.mkSimple declaration.name)
          candidates := candidates.push candidate
          report := { report with obligations := report.obligations.push { goal := candidate.mvarId! } }
      let assignment ← predicateAssignmentExpr (signature.kvars.toArray.zip candidates)
      let mut sourceProofs := #[]
      for entry in lowering.clauses, bridge in prepared.bridges do
        match bridge with
        | some proof =>
            let scalarClauseProof ← mkAppM ``And.left #[scalarProof]
            scalarProof ← mkAppM ``And.right #[scalarProof]
            sourceProofs := sourceProofs.push (mkApp (proof.beta candidates) scalarClauseProof)
        | none =>
            -- Keep the user's signature name readable in unresolved measure facts.
            let target := sourceType signatureExpression assignment entry.source
            let proof ← mkFreshExprMVar target (kind := .syntheticOpaque)
              (userName := Name.mkSimple s!"source_clause_{entry.source.index + 1}")
            let remaining ← cleanSourceGoal proof.mvarId!
            sourceProofs := sourceProofs.push proof
            report := { report with
              obligations := report.obligations ++ remaining.toArray.map
                (fun goal => { goal, sourceClause := some entry.source.index }) }
      let mut combined := Lean.mkConst ``True.intro
      for proof in sourceProofs.reverse do
        combined ← mkAppM ``And.intro #[proof, combined]
      let valid ← mkAppM ``flatten_valid_sound #[toExpr signature, assignment, toExpr constraint, combined]
      let result ← mkAppOptM ``Exists.intro #[domain, predicate, assignment, valid]
      let result ← instantiateMVars result
      if report.obligations.isEmpty then checkWithKernel result else check result
      Flex.CHC.rejectAdmissions result
      unless ← isDefEq (← inferType result) target do
        throwError "λRK bridge: reconstructed proof has the wrong source constraint"
      goal.assign result
      return if report.obligations.isEmpty then .solved report else .«partial» report
  catch error =>
    let message ← error.toMessageData.toString
    restoreExactly saved
    if error.isInterrupt then throw error
    return .failed message

end LambdaRK.Bridge
