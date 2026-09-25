import Lean
import Aesop

import Flex.Core
import Flex.Fusion
import Flex.Tactic.Utils
import Flex.PA.Fixpoint

open Lean Elab Meta Tactic

initialize Lean.registerTraceClass `solveFixpoint

/-- Closers tried in order on a leaf goal. The order is RQ3 baseline A, so
    don't reorder. `simp_all` is left out: its `maxRecDepth` escapes
    `attemptTactic`'s catch (logged, not thrown). -/
private def tryClosers : TacticM Bool := do
  let closers : List (TSyntax `tactic) := [
    (← `(tactic| native_decide)),
    (← `(tactic| grind)),
    -- When aesop can't close a goal it may still leave simplified subgoals and
    -- succeed; don't warn about that.
    (← `(tactic| aesop (config := { warnOnNonterminal := false }))),
    (← `(tactic| omega)),
    (← `(tactic| bv_decide)),
    (← `(tactic| (constructor <;> grind)))]
  for tac in closers do
    if (← attemptTactic (evalTactic tac)) then
      trace[solveFixpoint] m!"closer succeeded: {tac}"
      return true
  return false


private partial def closeLoop : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => pure ()
  | g :: restGoals =>
    -- Use `g.withContext` so `whnfR`/`tryClosers`/`unfoldDefinition` operate
    -- in `g`'s actual LCtx, not whatever stale `withMainContext` snapshot the
    -- caller set. Without this, `intro _` mutates the main goal but the
    -- surrounding LCtx stays stale, causing `unknown free variable` errors.
    g.withContext do
      let ty ← whnfR (← g.getType)
      if ty.isForall then
        evalTactic (← `(tactic| intro _))
        closeLoop
      else if ty.isAppOfArity ``And 2 then
        evalTactic (← `(tactic| and_intros))
        closeLoop
      else
        let closed ← tryClosers
        if closed then
          closeLoop
        else
          -- Try unfolding if required
          let didUnfold ← attemptTactic do
            let newGoal ← g.withContext do
              let target ← g.getType
              let u ← unfoldDefinition target
              g.replaceTargetDefEq u
            replaceMainGoal (newGoal :: restGoals)
          if didUnfold then
            closeLoop
          else
            setGoals restGoals
            closeLoop
            let remaining ← getGoals
            setGoals (g :: remaining)

/-!
  ## `solve_fixpoint` tactic

  Zap + Predicate abstraction.
-/
def solveFixpointImpl : TacticM Unit := withMainContext do
  -- Unfolding essentially
  let goal ← getMainGoal
  let _    ← attemptTactic
    (do let newGoal ← goal.withContext do
          let target   ← goal.getType
          let unfolded ← unfoldDefinition target
          goal.replaceTargetDefEq unfolded
        replaceMainGoal [newGoal])
  -- Peel ∃ κ : T, .. into κ-MVars via Exists.intro
  --    After this, the κ-mvars are part of the proof scaffolding and
  --    `bodyGoal` is the residual proof obligation with κs replaced
  --    by their mvars.
  let goal ← getMainGoal
  let (kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
  replaceMainGoal [bodyGoal]

  let kctx : KContext := { kvars := kvarMap }

  -- `withMainContext` here refreshes the LCtx after `peelExistentialsAndIntro`
  -- (and any prior tactic) mutated the main goal — without this, downstream
  -- code (`exprPartitionKVars`, `withLocalDeclD`) sees a stale LCtx that may
  -- be missing fvars present in the new main goal's context.
  let _ ← tryCatch (withMainContext do
      let bodyGoal ← getMainGoal
      let body     ← bodyGoal.getType
      let body     ← reduce body

      -- Partition acyclic vs cyclic κ-vars
      let (acyclic, cyclic) ← (exprPartitionKVars body).run kctx
      -- Parsed by scripts/kappa_classify.py, which runs Lean with -Dflex.benchPhases=true.
      if flex.benchPhases.get (← getOptions) then
        IO.println s!"[solve_fixpoint] Acyclic κ: {acyclic.map (·.name)}"
        IO.println s!"[solve_fixpoint] Cyclic κ:  {cyclic.map (·.name)}"

      -- Fusion for ALL acyclic κs (no proof-term construction — we just assign
      -- κ-mvars and let the kernel re-check the final term). An acyclic κ's σ̂
      -- may reference a cut κ's mvar (e.g. `k4 a5 → k0 a5` puts `?k4` in σ̂(k0));
      -- that is fine — κ-mvars are global, so the unifier resolves `?k4` once PA
      -- assigns the cut. Fuse every acyclic κ (exactly like `fusion`); PA then
      -- solves ONLY the genuine feedback-vertex cut.
      let curr ← benchPhase "solve_fixpoint" "fuse" do
        let mut curr := body
        for κ in acyclic do
          let scoped' ← (exprScope κ curr).run kctx
          let sol     ← (exprSolScoped κ scoped').run kctx
          let lam ← solToWitnessExpr sol κ.params κ.paramTypes
          trace[solveFixpoint] m!"fuse {κ.name}: sol = {sol}, lam = {lam}"
          κ.mvarId.assign lam
          curr ← (exprElimStar κ sol curr).run kctx
        pure curr

      -- Predicate abstraction only for the genuine cut κs.
      let paSet := cyclic
      benchPhase "solve_fixpoint" "pa" do
        if !paSet.isEmpty then
          trace[solveFixpoint] m!"PA on cyclic κs {paSet.map (·.name)}"
          let flatCs ← (exprFlat curr).run kctx
          let paSols ← predicateAbstraction kctx paSet flatCs
          for (κ, sol) in paSols do
            trace[solveFixpoint] m!"PA sol for {κ.name} = {sol}"
            let lam ← solToWitnessExpr sol κ.params κ.paramTypes
            κ.mvarId.assign lam
    )
    (fun e => do
      logInfo m!"[solve_fixpoint] ✗ Solver failed: {e.toMessageData}"
      logInfo m!"[solve_fixpoint] → leaving unfilled κs as user goals")

  -- 4. Expose unfilled κ-mvars as user goals so the user can `exact`
  --    a witness when fusion or PA didn't fully solve them.
  let unfilled ← kvarsInOrder.filterMapM fun κ => do
    if (← κ.mvarId.isAssigned) then return none
    else return some κ.mvarId

  if unfilled.isEmpty then
    -- Refresh LCtx — fusion's mvar assignments / earlier tactics may have
    -- mutated the main goal beyond the surrounding `withMainContext` snapshot.
    benchPhase "solve_fixpoint" "close" (withMainContext closeLoop)
  else
    let residual ← getMainGoal
    -- κs first so the user fills them before tackling the residual,
    -- which depends on them.
    setGoals (unfilled ++ [residual])
    logInfo m!"[solve_fixpoint] {unfilled.length} κ(s) left as user goal(s) — \
                 fill each with `exact (fun z0 z1 ... => ...)`."

syntax "solve" : tactic
elab_rules : tactic
  | `(tactic| solve) => solveFixpointImpl

-- Backward-compatible alias — `solve_fixpoint` is the former name of `solve`
macro "solve_fixpoint" : tactic => `(tactic| solve)
