import Flex.CHC.Certificate
import Flex.CHC.Normalize

namespace Flex.CHC

open Lean Meta Elab Term

initialize registerTraceClass `flex.chc

/-- Stages of a backend invocation. -/
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

/-- Attempt artifacts emitted as soon as they become available, including solver failures. -/
inductive Event where
  | exported (problem : ExportedProblem)
  | solverReturned (config : Config) (result : SolverResult)
  | importFailed (message : String)
  | imported (witnesses : Array Witness)
  | certified (certificate : CertificateResult)

private def measure (phase : IO.Ref Stage) (timings : IO.Ref (Array PhaseTiming))
    (notify : Stage → Option Nat → IO Unit)
    (stage : Stage) (action : TermElabM α) : TermElabM α := do
  phase.set stage
  let start ← IO.monoNanosNow
  notify stage none
  try action
  finally
    let stop ← IO.monoNanosNow
    timings.modify (·.push { stage, elapsedNs := stop - start })
    notify stage (some ((stop - start) / 1000000))

private def requireModel (result : SolverResult) : TermElabM Unit := do
  match result.outcome with
  | .sat _ => pure ()
  | .unsat => throwError "CHC solver found no satisfying predicate interpretation"
  | .unknown _ => throwError "CHC solver returned unknown; no witnesses are available"
  | .timedOut => throwError "CHC solver exceeded its wall-clock timeout"
  | .error message => throwError message

/-- Predicate slots and the goals used for certification and export. -/
structure PreparedGoal where
  kvars : List KVar
  bodyGoal : MVarId
  exportGoal : MVarId

/-- Validate and peel predicates, compact guards, then normalize for export.
With `headsOnly`, retain the cleaned clause structure for certification. Failures restore entry state. -/
def prepareGoal (goal : MVarId) (maxClauses : Nat := 1024)
    (headsOnly : Bool := false) : TermElabM PreparedGoal := do
  let saved ← Term.saveState
  let committed ← IO.mkRef false
  try
    let prepared : PreparedGoal ← goal.withContext do
      if ← goal.isAssignedOrDelayedAssigned then
        throwError "CHC preparation: goal is already assigned"
      let target ← instantiateMVars (← goal.getType)
      unless ← isProp target do
        throwError "CHC preparation: goal must be a proposition"
      Prepare.checkPredicatePrefix target
      let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal
      let bodyGoal ← compactGoal bodyGoal kvars
      let exportGoal ← if headsOnly then
          bodyGoal.withContext do
            let copy ← Meta.mkFreshExprMVar (some (← bodyGoal.getType))
              (kind := .syntheticOpaque)
            normalizeGoal copy.mvarId! kvars maxClauses
        else normalizeGoal bodyGoal kvars maxClauses
      return { kvars, bodyGoal := if headsOnly then bodyGoal else exportGoal, exportGoal }
    committed.set true
    return prepared
  finally
    unless ← committed.get do restoreTermState saved

/-- Normalize, export, solve, and certify one existential constraint goal.
`solved` proves the goal; `partial` retains witnesses and reported obligations.
Failures restore entry state; interrupts propagate. The tactic goal list is unchanged.

Signatures and constraints must be closed except for peeled predicate slots.
`maxClauses` bounds guard expansion; `config.timeoutMs` bounds only the solver.
With `headsOnly`, certify κ-heads and leave one VC with its original structure.
`onCandidate` inspects a temporarily instantiated body before certification.
`retryInconclusiveCandidates` prefers an alternate model when that check is unknown.
`onEvent` observes available artifacts even when a later stage fails.
At most two retries try alternate settings or equivalent Horn syntax after an
unusable result. Definitive UNSAT and process failures are not retried.
Callers configure oracle budgets and install residual goals. -/
def solveGoal (goal : MVarId) (config : Config := {})
    (oracle : ProofOracle := defaultProofOracle) (maxClauses : Nat := 1024)
    (headsOnly : Bool := false)
    (onPhase : Stage → Option Nat → IO Unit := fun _ _ => pure ())
    (onCandidate : Option (MVarId → TermElabM PASynthResult) := none)
    (onEvent : Event → TermElabM Unit := fun _ => pure ())
    (retryInconclusiveCandidates : Bool := false)
    : TermElabM GoalResult := do
  let saved ← Term.saveState
  let committed ← IO.mkRef false
  let phase ← IO.mkRef Stage.prepare
  let timings ← IO.mkRef (#[] : Array PhaseTiming)
  let transcript ← IO.mkRef (none : Option SolverResult)
  let size ← IO.mkRef (0, 0)
  try
    goal.withContext do
      let prepared ← measure phase timings onPhase .prepare <| prepareGoal goal maxClauses headsOnly
      let problem ← measure phase timings onPhase .exporting do
        let body ← prepared.exportGoal.getType
        exportConstraints prepared.kvars body
      size.set (problem.relations.size, problem.clauseCount)
      let solve (problem : ExportedProblem) (config : Config) := do
        onEvent (.exported problem)
        measure phase timings onPhase .solver do
          let result ← run problem config
          transcript.set (some result)
          onEvent (.solverReturned config result)
          Core.checkInterrupted
          return result
      let importModel (problem : ExportedProblem) (solver : SolverResult)
          : TermElabM (Except Exception (Array Witness)) :=
        measure phase timings onPhase .importing do
          let outcome ← try
              pure (.ok (← importWitnesses problem solver))
            catch error => pure (.error error)
          if let .error error := outcome then
            if error.isInterrupt then throw error
            Core.checkInterrupted
            onEvent (.importFailed (← error.toMessageData.toString))
          return outcome
      let useModel (problem : ExportedProblem) (solver : SolverResult)
          : TermElabM (Except Exception (Array Witness × Bool)) := do
        let available : Except Exception Unit ← try requireModel solver; pure (.ok ())
          catch error => pure (.error error)
        if let .error error := available then return .error error
        let witnesses ← match ← importModel problem solver with
          | .ok witnesses => pure witnesses
          | .error error => return .error error
        onEvent (.imported witnesses)
        if let some inspect := onCandidate then
          -- Save a validated instantiation before starting proof search.
          let before ← Term.saveState
          let answer ← try
            assignWitnesses problem witnesses
            prepared.bodyGoal.withContext <| inspect prepared.bodyGoal
          finally restoreTermState before
          if answer == .invalid then
            return .error (.error (← getRef) m!"CHC solver candidate refuted")
          return .ok (witnesses, answer != .valid)
        return .ok (witnesses, false)
      let rec attempt (retries : Nat) (problem : ExportedProblem) (config : Config)
          : TermElabM (ExportedProblem × SolverResult × Array Witness) := do
        let solver ← solve problem config
        match ← useModel problem solver with
        | .ok (witnesses, inconclusive) =>
          if inconclusive && retryInconclusiveCandidates &&
              config.retrySearch && !problem.canonicalClauses then
            if let remaining + 1 := retries then
              -- Large quantified models can make validation inconclusive. Try
              -- equivalent Horn syntax before spending the proof-search budget.
              -- Conservative Spacer settings preserve explicit relation bodies.
              let fallback := if config.backend == .spacer then
                { config with spacerInlining := false } else config
              return ← attempt remaining (← problem.withCanonicalClauses) fallback
          return (problem, solver, witnesses)
        | .error error =>
          if error.isInterrupt || error.isRuntime then throw error
          Core.checkInterrupted
          let remaining + 1 := retries | throw error
          -- A definitive UNSAT or a broken executable is not a model-format problem.
          match solver.outcome with
          | .unsat => throw error
          | .error _ => unless solver.process.completion == .exited 0 do throw error
          | _ => pure ()
          let (problem, fallback) ← match solver.outcome with
            | .unknown _ | .timedOut =>
              if config.backend == .eldarica && config.eldaricaLargeBlockEncoding then
                let some fallback := config.modelFallback? | throw error
                pure (problem, fallback)
              else if config.backend == .spacer && !config.spacerInlining then
                unless config.retrySearch do throw error
                pure (problem, { config with spacerInlining := true })
              else
                unless config.retrySearch do throw error
                if problem.canonicalClauses then throw error
                pure (← problem.withCanonicalClauses, config)
            | _ =>
              let some fallback := config.modelFallback? | throw error
              pure (problem, fallback)
          -- Preserve every attempt; retries never weaken constraints or import checks.
          attempt remaining problem fallback
      let (problem, solver, witnesses) ← attempt 2 problem config
      let certificate ← measure phase timings onPhase .certificate do
        certifyWitnesses problem witnesses prepared.bodyGoal oracle headsOnly
      onEvent (.certified certificate)
      let report : GoalReport := {
        problem, solver, witnesses, certificate, timings := ← timings.get }
      committed.set true
      return if certificate.goals.isEmpty then .solved report else .partial report
  catch error =>
    let message ← error.toMessageData.toString
    if error.isInterrupt then throw error
    return .failed {
      stage := ← phase.get, message, solver := ← transcript.get
      relations := (← size.get).1, clauses := (← size.get).2, timings := ← timings.get }
  finally
    unless ← committed.get do restoreTermState saved

end Flex.CHC
