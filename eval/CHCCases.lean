import Demo.Basic
import Demo.Fix
import Flex.CHC

/-! Benchmark prelude used by `scripts/benchmark_chc.py`.

The solver paths use `Flex.CHC.solveGoal` on the original demo propositions,
without predicate abstraction or Zap. Ordinary Lean automation certifies
the candidates; partial certificates are reported separately from solver errors.
Imports and dependency builds are excluded from the timers. -/

open Lean Meta Elab Tactic Command Flex.CHC

set_option Elab.async false
set_option maxHeartbeats 4000000

namespace CHCCases

private structure Measurement where
  phases : Array (String × Nat) := #[]
  stage : String := "setup"
  relations : Nat := 0
  clauses : Nat := 0
  witnesses : Array String := #[]
  solverStatus : String := "not_run"
  processElapsedMs : Nat := 0
  resultKind : String := "not_run"
  remainingHeads : Nat := 0
  remainingQueries : Nat := 0
  provedHeads : Nat := 0
  provedQueries : Nat := 0

private def timed (measure : IO.Ref Measurement) (stage : String)
    (action : TacticM α) : TacticM α := do
  measure.modify fun m => { m with stage }
  let start ← IO.monoNanosNow
  let errorsBefore := (← Core.getMessageLog).toList.countP (·.severity == .error)
  try
    let result ← action
    let errorsAfter := (← Core.getMessageLog).toList.countP (·.severity == .error)
    -- Some tactics recover from failure by logging an error and inserting
    -- synthetic sorry. Classify this at the failing phase, before kernel audit.
    if errorsAfter > errorsBefore then
      throwError "{stage} automation reported an error; no complete proof was produced"
    return result
  finally
    let stop ← IO.monoNanosNow
    measure.modify fun m => { m with phases := m.phases.push (stage, stop - start) }

private def solverConfig (backend : String) : IO Flex.CHC.Config := do
  if backend == "spacer" then
    return { backend := .spacer }
  else if backend == "eldarica" then
    return {
      backend := .eldarica, executable := ← IO.getEnv "CHC_ELDARICA" }
  else
    throw (IO.userError s!"unknown backend: {backend}")

private def stageName : Stage → String
  | .prepare => "prepare"
  | .exporting => "export"
  | .solver => "solver"
  | .importing => "import"
  | .certificate => "certificate"

private def recordSolver (measure : IO.Ref Measurement) (result : SolverResult) : IO Unit := do
  let status := match result.outcome with
    | .sat _ => "sat"
    | .unsat => "unsat"
    | .unknown _ => "unknown"
    | .timedOut => "timeout"
    | .error _ => "error"
  measure.modify fun m => { m with
    solverStatus := status, processElapsedMs := result.process.elapsedMs }

private def recordTimings (measure : IO.Ref Measurement) (timings : Array PhaseTiming) : IO Unit :=
  measure.modify fun m => { m with
    phases := m.phases ++ timings.map (fun timing => (stageName timing.stage, timing.elapsedNs)) }

private def recordReport (measure : IO.Ref Measurement) (report : GoalReport) : TermElabM Unit := do
  recordTimings measure report.timings
  recordSolver measure report.solver
  let heads := report.certificate.obligations.countP fun obligation =>
    match obligation.kind with | .head _ => true | .query => false
  measure.modify fun m => { m with
    stage := "certificate"
    relations := report.problem.relations.size
    clauses := report.problem.clauseCount
    remainingHeads := heads
    remainingQueries := report.certificate.obligations.size - heads
    provedHeads := report.certificate.provedHeads
    provedQueries := report.certificate.provedQueries }
  -- Pretty printing is excluded from the reported pipeline duration.
  let start ← IO.monoNanosNow
  try
    let rendered ← report.witnesses.mapM fun w => do
      return s!"{w.symbol} := {← ppExpr w.value}"
    measure.modify fun m => { m with witnesses := rendered }
  finally
    let stop ← IO.monoNanosNow
    measure.modify fun m => { m with phases := m.phases.push ("describe", stop - start) }

/-- Exercise the public goal pipeline directly, so expected failures and useful
partial certificates are data rather than tactic error-recovery admissions. -/
private def proveCHC (measure : IO.Ref Measurement) (backend : String)
    (goal : MVarId) : TermElabM Unit := do
  let config ← solverConfig backend
  let oracle : ProofOracle := fun proposition => do
    proveLeafWith (← `(tactic| first | omega | grind)) proposition
  match ← solveGoal goal config oracle with
  | .failed failure =>
    recordTimings measure failure.timings
    if let some solver := failure.solver then recordSolver measure solver
    measure.modify fun m => { m with
      stage := stageName failure.stage, resultKind := "failed"
      relations := failure.relations, clauses := failure.clauses }
    throwError "{failure.message}"
  | .partial report =>
    recordReport measure report
    measure.modify fun m => { m with stage := "partial", resultKind := "partial" }
    let m ← measure.get
    throwError "CHC witnesses leave {m.remainingHeads} head and {m.remainingQueries} query obligations"
  | .solved report =>
    recordReport measure report
    measure.modify fun m => { m with resultKind := "solved" }

private def timedKernelCheck (measure : IO.Ref Measurement) (goal type : Expr) : TermElabM (Array String) := do
  measure.modify fun m => { m with stage := "kernel" }
  let start ← IO.monoNanosNow
  try
    let proof ← instantiateMVars goal
    if proof.hasExprMVar || proof.hasFVar || proof.hasSorry then
      throwError "proof is incomplete or contains an admission"
    checkWithKernel proof
    unless ← isDefEq (← inferType proof) type do
      throwError "proof does not have the original proposition's type"
    let mut axioms : Array Name := #[]
    let mut pending := proof.getUsedConstants
    let mut visited : NameSet := {}
    let env ← getEnv
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      let info ← getConstInfo name
      if let some index := env.getModuleIdxFor? name then
        let moduleName := env.allImportedModuleNames[index.toNat]!
        if (moduleName == `Demo.Basic || moduleName == `Demo.Fix) &&
            (info matches .thmInfo _) && name.getRoot != `Point && name.getRoot != `double then
          throwError "proof reused an existing demo theorem: {name}"
        -- Earlier imported modules cannot depend on the demo modules.
      else
        pending := pending ++ info.type.getUsedConstants
        if let some value := info.value? then pending := pending ++ value.getUsedConstants
      for axiomName in (← collectAxioms name) do
        unless axioms.contains axiomName do axioms := axioms.push axiomName
    for axiomName in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "proof depends on an unexpected axiom: {axiomName}"
    return axioms.map toString
  finally
    let stop ← IO.monoNanosNow
    measure.modify fun m => { m with phases := m.phases.push ("kernel", stop - start) }

/-- Failures are data, so an unsupported input cannot abort the remaining cases.
Every success is checked as a closed proof of the original proposition. -/
elab "chc_case " target:ident backend:str repetition:num : command => do
  let measure ← IO.mkRef ({} : Measurement)
  let start ← IO.monoNanosNow
  let mut success := false
  let mut error := ""
  let mut axioms : Array String := #[]
  try
    axioms ← liftTermElabM do
      let messages ← Core.getMessageLog
      try
        let type ← Term.elabTerm target (some (.sort .zero))
        let goal ← mkFreshExprMVar type
        if backend.getString == "fix" then
          let remaining ← Tactic.run goal.mvarId! do
            withMainContext do
              timed measure "fix" do
                evalTactic (← `(tactic| (try zap; all_goals first | (fix; done) | grind)))
          unless remaining.isEmpty do throwError "automation left {remaining.length} goals"
        else
          proveCHC measure backend.getString goal.mvarId!
        -- Tactic.run catches abort exceptions; a failed tactic may therefore
        -- skip subsequent TacticM checks and return a recovered sorry proof.
        -- Inspect the root here, retaining the last automation phase on failure.
        let proof ← instantiateMVars goal
        if proof.hasExprMVar || proof.hasFVar || proof.hasSorry then
          throwError "automation did not produce a complete proof of the original proposition"
        timedKernelCheck measure goal type
      finally
        -- Expected failures are emitted in CHC_RESULT, not as Lean file errors.
        Core.setMessageLog messages
    success := true
  catch e =>
    error ← e.toMessageData.toString
  let stop ← IO.monoNanosNow
  let m ← measure.get
  let result := Json.mkObj [
    ("case", toJson target.getId.toString),
    ("backend", toJson backend.getString),
    ("repetition", toJson repetition.getNat),
    ("success", toJson success),
    ("stage", toJson m.stage),
    ("result_kind", toJson m.resultKind),
    ("solver_status", toJson m.solverStatus),
    ("process_elapsed_ms", toJson m.processElapsedMs),
    ("error", toJson error),
    ("total_ns", toJson (stop - start)),
    ("phases_ns", Json.mkObj (m.phases.toList.map fun (k, v) => (k, toJson v))),
    ("relations", toJson m.relations),
    ("clauses", toJson m.clauses),
    ("remaining_heads", toJson m.remainingHeads),
    ("remaining_queries", toJson m.remainingQueries),
    ("proved_heads", toJson m.provedHeads),
    ("proved_queries", toJson m.provedQueries),
    ("witnesses", toJson m.witnesses),
    ("axioms", toJson axioms)]
  IO.println s!"CHC_RESULT {result.compress}"

end CHCCases
