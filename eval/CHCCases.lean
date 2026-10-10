import Demo.Basic
import Demo.Cyclic
import Flex.CHC

/-! Benchmark prelude used by `scripts/benchmark_chc.py`.

The solver paths use the original demo propositions, without Flex predicate
abstraction, fusion, or zap. Only ordinary Lean automation discharges the
constraints after every existential predicate is supplied by the solver.
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

private def solverResult (backend : String) (problem : ExportedProblem) : IO SolverResult := do
  if backend == "spacer" then
    Spacer.run problem
  else if backend == "eldarica" then
    let executable := (← IO.getEnv "CHC_ELDARICA").getD "eld"
    let process ← Process.run {
      executable, args := #["-in", "-hsmt", "-ssol"], timeoutMs := 10000
    } problem.toSMTLib
    return SolverResult.ofProcess process
  else
    throw (IO.userError s!"unknown backend: {backend}")

private def prove (measure : IO.Ref Measurement) (backend : String) : TacticM Unit :=
  withMainContext do
    if backend == "fix" then
      timed measure "fix" do
        evalTactic (← `(tactic| solve_fixpoint))
      return
    let (bodyGoal, problem) ← timed measure "export" do
      let (_, kvars, bodyGoal) ← peelExistentialsAndIntro (← getMainGoal)
      let problem ← exportConstraints kvars (← bodyGoal.getType)
      measure.modify fun m => { m with
        relations := problem.relations.size, clauses := problem.clauseCount }
      return (bodyGoal, problem)
    let result ← timed measure "solver" do
      let result ← solverResult backend problem
      let status := match result.outcome with
        | .sat _ => "sat"
        | .unsat => "unsat"
        | .unknown _ => "unknown"
        | .timedOut => "timeout"
        | .error _ => "error"
      measure.modify fun m => { m with
        solverStatus := status, processElapsedMs := result.process.elapsedMs }
      return result
    let witnesses ← timed measure "import" (importWitnesses problem result)
    timed measure "assign" (assignWitnesses problem witnesses)
    -- Pretty printing is recorded separately from the synthesis/proof phases.
    timed measure "describe" do
      let rendered ← witnesses.mapM fun w => do
        return s!"{w.symbol} := {← ppExpr w.value}"
      measure.modify fun m => { m with witnesses := rendered }
    timed measure "vc" do
      let bodyGoal ← bodyGoal.replaceTargetDefEq (← instantiateMVars (← bodyGoal.getType))
      setGoals [bodyGoal]
      evalTactic (← `(tactic| repeat' (first | (intro) | apply And.intro)))
      evalTactic (← `(tactic| all_goals (first | omega | grind)))

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
        if (moduleName == `Demo.Basic || moduleName == `Demo.Cyclic) &&
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
        let remaining ← Tactic.run goal.mvarId! (prove measure backend.getString)
        unless remaining.isEmpty do throwError "automation left {remaining.length} goals"
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
    ("solver_status", toJson m.solverStatus),
    ("process_elapsed_ms", toJson m.processElapsedMs),
    ("error", toJson error),
    ("total_ns", toJson (stop - start)),
    ("phases_ns", Json.mkObj (m.phases.toList.map fun (k, v) => (k, toJson v))),
    ("relations", toJson m.relations),
    ("clauses", toJson m.clauses),
    ("witnesses", toJson m.witnesses),
    ("axioms", toJson axioms)]
  IO.println s!"CHC_RESULT {result.compress}"

end CHCCases
