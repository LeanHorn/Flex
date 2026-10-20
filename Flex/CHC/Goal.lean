import Flex.CHC.Certificate
import Flex.CHC.Normalize

namespace Flex.CHC

open Lean Meta Elab Term

/-- Stages of a single backend attempt, without tactic selection or fallback. -/
inductive Stage where
  | prepare | exporting | solver | importing | certificate
  deriving BEq, Repr, Inhabited

/-- Wall time for a completed or failed phase, including external solver work. -/
structure PhaseTiming where
  stage : Stage
  elapsedNs : Nat
  deriving Repr, Inhabited

/-- A failed attempt leaves the caller's Lean state unchanged. The transcript is
retained when a solver was invoked, including on model reconstruction failure. -/
structure Failure where
  stage : Stage
  message : String
  solver : Option SolverResult := none
  relations : Nat := 0
  clauses : Nat := 0
  timings : Array PhaseTiming := #[]

/-- A committed attempt: all existential predicates have been instantiated.
Remaining proof goals are available through `certificate.goals`. -/
structure GoalReport where
  problem : ExportedProblem
  solver : SolverResult
  witnesses : Array Witness
  certificate : CertificateResult
  timings : Array PhaseTiming := #[]

/-- Only certification can report success; partial results retain explicit VCs. -/
inductive GoalResult where
  | solved (report : GoalReport)
  | «partial» (report : GoalReport)
  | failed (failure : Failure)

private def measure (phase : IO.Ref Stage) (timings : IO.Ref (Array PhaseTiming))
    (stage : Stage) (action : TermElabM α) : TermElabM α := do
  phase.set stage
  let start ← IO.monoNanosNow
  try action
  finally
    let stop ← IO.monoNanosNow
    timings.modify (·.push { stage, elapsedNs := stop - start })

private def requireModel (result : SolverResult) : TermElabM Unit := do
  match result.outcome with
  | .sat _ => pure ()
  | .unsat => throwError "CHC solver found no satisfying predicate interpretation"
  | .unknown _ => throwError "CHC solver returned unknown; no witnesses are available"
  | .timedOut => throwError "CHC solver exceeded its wall-clock timeout"
  | .error message => throwError message

/-- Normalize, export, solve, and certify one existential constraint goal.
`solved` proves the goal; `partial` retains witnesses and reported obligations.
Failures restore all entry state; interrupts propagate. The tactic goal list is
unchanged, and no backend or tactic fallback runs here.

Signatures and constraints must be closed except for peeled predicate slots.
`maxClauses` bounds guard expansion; `config.timeoutMs` bounds only the solver.
With `headsOnly`, certify κ-heads and leave one VC with its original structure.
Callers configure oracle budgets and install residual goals. -/
def solveGoal (goal : MVarId) (config : Config := {})
    (oracle : ProofOracle := defaultProofOracle) (maxClauses : Nat := 1024)
    (headsOnly : Bool := false)
    : TermElabM GoalResult := do
  let saved ← Term.saveState
  let phase ← IO.mkRef Stage.prepare
  let timings ← IO.mkRef (#[] : Array PhaseTiming)
  let transcript ← IO.mkRef (none : Option SolverResult)
  let size ← IO.mkRef (0, 0)
  try
    goal.withContext do
      let (kvars, bodyGoal, exportGoal) ← measure phase timings .prepare do
        if ← goal.isAssignedOrDelayedAssigned then
          throwError "CHC goal is already assigned"
        unless ← isProp (← goal.getType) do
          throwError "CHC goal must be a proposition"
        let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal
        -- Normalize a copy for export when the residual must preserve the source VC.
        let exportGoal ← if headsOnly then
            bodyGoal.withContext do
              let copy ← Meta.mkFreshExprMVar (some (← bodyGoal.getType))
                (kind := .syntheticOpaque)
              normalizeGoal copy.mvarId! maxClauses
          else normalizeGoal bodyGoal maxClauses
        return (kvars, if headsOnly then bodyGoal else exportGoal, exportGoal)
      let problem ← measure phase timings .exporting do
        exportConstraints kvars (← exportGoal.getType)
      size.set (problem.relations.size, problem.clauseCount)
      let solver ← measure phase timings .solver do
        let result ← run problem config
        Core.checkInterrupted
        transcript.set (some result)
        requireModel result
        return result
      let witnesses ← measure phase timings .importing do
        importWitnesses problem solver
      let certificate ← measure phase timings .certificate do
        certifyWitnesses problem witnesses bodyGoal oracle headsOnly
      let report : GoalReport := {
        problem, solver, witnesses, certificate, timings := ← timings.get }
      return if certificate.goals.isEmpty then .solved report else .partial report
  catch error =>
    let message ← error.toMessageData.toString
    restoreTermState saved
    if error.isInterrupt then throw error
    return .failed {
      stage := ← phase.get, message, solver := ← transcript.get
      relations := (← size.get).1, clauses := (← size.get).2, timings := ← timings.get }

end Flex.CHC
