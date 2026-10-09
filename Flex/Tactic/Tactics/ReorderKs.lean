import Flex.Core
import Flex.Fusion
import Flex.Tactic.Utils
import Flex.Tactic.Tactics.RewriteKs

open Lean Meta Elab Tactic

/-! ## `reorderKs` tactic

  Front-end for the fusion/PA pipeline: it *reorders* the head ∃-chain and then
  *explodes* it into per-κ synthesis subgoals.

  Given a goal `∃ κ₁ … κₙ, P(κ₁, …, κₙ)`, `reorderKs`:

  1. **Reorders** the ∃-chain (via `rewriteKs`) so the cyclic κ's come first,
     then the acyclic κ's in topological order (sinks first).
  2. **Explodes** each `∃ κ : T` into a fresh `syntheticOpaque` κ-mvar supplied
     as the `Exists.intro` witness (via `peelExistentialsAndIntro`), leaving the
     constraint body `P(?κ₁, …, ?κₙ)` as the residual.
  3. **Exposes** every κ-mvar as its own subgoal (a synthesis goal `⊢ T`, filled
     later with `exact (fun z₀ z₁ … => …)`), in the reordered order, with the
     constraint `P` as the final subgoal.

  Resulting goal list (cyclic-first):

      ⊢ Tᵏ¹  …  ⊢ Tᵏᵐ            -- one synthesis goal per κ (cyclic, then acyclic)
      ⊢ P(?κ₁, …, ?κₙ)           -- the constraint, with κ's as scoped mvars

  Every κ-mvar lives in the original goal's local context, so the metavariables
  carry the right scope. Downstream the acyclic κ's are dispatched by `sol`/
  `fusion`, the cyclic κ's by `fixpoint`. -/

syntax "reorderKs" : tactic

elab_rules : tactic
  | `(tactic| reorderKs) => withMainContext do
      -- 1. Reorder the ∃-chain: cyclic κ's first, acyclic in topo order.
      --    Best-effort — `rewriteKs` is a no-op (it just logs) when the chain
      --    is already in optimal order, and throws on a non-∃ goal (caught here).
      let _ ← attemptTactic (evalTactic (← `(tactic| rewriteKs)))

      -- 2. Peel each `∃ κ : T` into a fresh syntheticOpaque κ-mvar via
      --    `Exists.intro`, leaving the body as the residual proof goal.
      let goal ← getMainGoal
      let (_, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
      if kvarsInOrder.isEmpty then
        logInfo m!"reorderKs: goal has no ∃-binders, nothing to reorder"
        return

      -- 3. Expose every κ-mvar as its own synthesis subgoal (reordered order:
      --    cyclic first), with the constraint body as the final subgoal.
      setGoals (kvarsInOrder.map (·.mvarId) ++ [bodyGoal])
      logInfo m!"reorderKs: exploded {kvarsInOrder.length} κ \
                 {kvarsInOrder.map (·.name)} into synthesis subgoals + 1 constraint goal"
