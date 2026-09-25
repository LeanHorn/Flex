import Lean
import Aesop

import Flex.Core
import Flex.Fusion
import Flex.PA
import Flex.Tactic.Utils

open Lean Elab Meta Tactic

/-! ## `fixpoint` tactic

  Predicate abstraction for the *cyclic* κ's of a constraint — the second half
  of the solver, complementing `fusion` (which handles the acyclic κ's).

  Per the pipeline contract:
  - **assumes κ's as meta-vars** — peels the head ∃-chain into κ-mvars first, so
    it works directly on `∃ κ, P` goals (e.g. the residual `fusion` leaves);
  - **predicate abstraction** — seeds every cyclic κ with the union of all
    `@[qualif]`-tagged predicates and runs Houdini weakening to a fixpoint;
  - **existentials handled too** — the ∃-peeling means no manual `Exists.intro`
    is needed before calling it.

  Acyclic κ's are *not* solved here — run `fusion` first. Any acyclic κ still
  present (or any κ PA fails to solve) is surfaced as a user goal `⊢ T`. -/

private def fixpointImpl : TacticM Unit := withMainContext do
  -- Unfold a top-level def wrapping the ∃-chain, if any (best-effort).
  let goal ← getMainGoal
  let _ ← attemptTactic
    (do let newGoal ← goal.withContext do
          let target   ← goal.getType
          let unfolded ← unfoldDefinition target
          goal.replaceTargetDefEq unfolded
        replaceMainGoal [newGoal])

  -- Peel `∃ κ : T, …` into fresh κ-mvars via `Exists.intro`; the body becomes
  -- the residual proof goal with each κ replaced by its mvar.
  let goal ← getMainGoal
  let (kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
  replaceMainGoal [bodyGoal]
  let kctx : KContext := { kvars := kvarMap }

  -- `withMainContext` refreshes the LCtx after `peelExistentialsAndIntro`
  -- mutated the main goal — downstream traversal must see the new context.
  let _ ← tryCatch (withMainContext do
      let bodyGoal ← getMainGoal
      let body ← reduce (← bodyGoal.getType)

      -- Partition κ's; PA only ever solves the cyclic ones.
      let (acyclic, cyclic) ← (exprPartitionKVars body).run kctx
      unless acyclic.isEmpty do
        logInfo m!"[fixpoint] ⚠ acyclic κ present — run `fusion` first: \
                   {acyclic.map (·.name)}"

      benchPhase "fixpoint" "pa" do
        if !cyclic.isEmpty then
          let flatCs ← (exprFlat body).run kctx
          let paSols ← predicateAbstraction kctx cyclic flatCs
          for (κ, sol) in paSols do
            logInfo m!"[fixpoint] PA sol for {κ.name} := {← ppExpr sol}"
            let lam ← solToWitnessExpr sol κ.params κ.paramTypes
            κ.mvarId.assign lam)
    (fun e => logInfo m!"[fixpoint] ✗ solver failed: {e.toMessageData}")

  -- Surface unfilled κ-mvars as user goals; otherwise close residual leaf
  -- obligations (arithmetic) with a standard closer cascade.
  let unfilled ← kvarsInOrder.filterMapM fun κ => do
    if (← κ.mvarId.isAssigned) then return none else return some κ.mvarId
  if unfilled.isEmpty then
    -- Force the PA κ-mvar assignments into the residual goal(s): replace each
    -- target with its instantiated form so the closer sees concrete predicates
    -- (e.g. `(fun _ => True) 0`) rather than the κ-mvar `?k`. Without this the
    -- closer can run against `?k 0` and fail (swallowed by `try`), leaving the
    -- body mvar → "(kernel) declaration has metavariables".
    let goals ← getGoals
    let goals' ← goals.mapM fun g =>
      g.withContext do g.replaceTargetDefEq (← instantiateMVars (← g.getType))
    replaceMainGoal goals'
    benchPhase "fixpoint" "close" <| withMainContext do
      evalTactic (← `(tactic| all_goals (try (first | rfl | grind | omega | aesop))))
  else
    let residual ← getMainGoal
    setGoals (unfilled ++ [residual])
    logInfo m!"[fixpoint] {unfilled.length} κ left as user goal(s) — \
               fill each with `exact (fun z0 z1 … => …)`."

syntax "fixpoint" : tactic
elab_rules : tactic
  | `(tactic| fixpoint) => fixpointImpl
