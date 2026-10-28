import Flex

/-!
  # UX walkthrough — one constraint, every tactic

  This file demonstrates the solver's tactic surface on a *single* refinement
  constraint, showing exactly what each tactic does to the goal. It is meant to
  be read top-to-bottom as a figure: the same `Prop` flows through every stage.

  The constraint `ex` packs both shapes the solver distinguishes:

    * `κseed` — **acyclic**: produced from `x`, consumed once by `κinv`.
                Solved by *zap* (Cosman–Jhala elimination).
    * `κinv`  — **cyclic**: has a self-loop (`κinv i → κinv (i-1)`).
                Solved by *predicate abstraction* (Houdini).

  Pipeline:  `reorderKs` (reorder + explode) → `sol`/`zap` (acyclic) →
             `fixpoint` (cyclic).  `solve_fixpoint` is all of it at once.
-/

-- Qualifier bank for predicate abstraction: the atoms PA may conjoin per κ.
@[qualif] def q_gez (v : Int) : Prop := 0 ≤ v

/-- The running example. `κseed` is acyclic, `κinv` is cyclic.
    A solution: `κseed ν x := ν = x`, `κinv ν x := 0 ≤ ν`. -/
def ex : Prop :=
  ∃ κseed : Int → Int → Prop,
  ∃ κinv  : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x → κseed ν x)                  -- seed:  κseed ⊒ {ν = x}
    ∧ (∀ v : Int, κseed v x → κinv v x)               -- entry: κseed ⊑ κinv
    ∧ (∀ i : Int, κinv i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν x)              -- loop:  κinv self-cycle
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)                   -- check: κinv ⊑ {0 ≤ ν}

-- ───────────────────────────────────────────────────────────────────────────
-- 1.  `reorderKs` — reorder the ∃-chain (cyclic first) and EXPLODE it into
--      one synthesis subgoal per κ, plus the constraint body.
-- ───────────────────────────────────────────────────────────────────────────
-- Before:  ⊢ ∃ κseed κinv, P(κseed, κinv)
-- After:   case κinv   ⊢ Int → Int → Prop      -- cyclic, hoisted to the top
--          case κseed  ⊢ Int → Int → Prop      -- acyclic
--                      ⊢ ∀ x, 0 ≤ x → P(?κseed, ?κinv)
-- Each κ is now a *named* synthesis subgoal holding a scoped metavar; the last
-- goal is the residual constraint. This is the manual front-end the rest automate.
example : ex := by
  unfold ex
  -- rewriteKs
  reorderKs
  case κinv  => exact fun ν _ => 0 ≤ ν      -- κinv  := λ ν _. 0 ≤ ν
  case κseed => exact fun ν x => ν = x      -- κseed := λ ν x. ν = x
  grind                                     -- discharge the now-instantiated body

-- ───────────────────────────────────────────────────────────────────────────
-- 2.  `sol` (`solK1`) — solve ONE acyclic κ: synthesize its witness, bind it in
--      the context by name, and substitute it away. One fewer existential.
-- ───────────────────────────────────────────────────────────────────────────
-- Before:  ⊢ ∃ κseed κinv, P(κseed, κinv)
-- After:   κseed : Int → Int → Prop := ⋯     -- witness synthesized, bound by name
--          ⊢ ∃ κinv, P'(κinv)                -- one fewer ∃; κseed referenced by name
-- (`solve_fixpoint` then finishes the cyclic κinv; here it just closes the rest.)
example : ex := by
  unfold ex
  solK1 κseed
  solve_fixpoint

-- ───────────────────────────────────────────────────────────────────────────
-- 3.  `zap` (= the `elim` step) then `fixpoint`.
--      `zap` eliminates ALL acyclic κ's at once (repeated sol+elim), leaving
--      the cyclic κ's as an existential; `fixpoint` runs predicate abstraction.
-- ───────────────────────────────────────────────────────────────────────────
-- After `zap`:    ⊢ ∃ κinv, P''(κinv)
--   κseed is gone: head occurrences `… → κseed ν x` collapse to `True`, and
--   hypothesis occurrences `κseed v x → …` are replaced by κseed's solution.
-- After `fixpoint`:  PA finds κinv := 0 ≤ ν, discharging everything.
example : ex := by
  unfold ex
  zap
  fixpoint

-- ───────────────────────────────────────────────────────────────────────────
-- 4.  `solve_fixpoint` — zap ⨾ fixpoint fused into one push-button tactic.
-- ───────────────────────────────────────────────────────────────────────────
example : ex := by
  unfold ex
  solve_fixpoint
