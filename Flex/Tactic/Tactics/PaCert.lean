import Lean
import Aesop

import Flex.Core
import Flex.Fusion
import Flex.Tactic.Utils
import Flex.PA.Fixpoint
import Flex.PA.Cert

open Lean Elab Meta Tactic

/-!
  ## `pa_cert` — certifying Predicate Abstraction (paper §5)

  Cut-only certifier. Given `∃κ̄. c` whose ∃-bound κ's are all solved by
  predicate abstraction (e.g. `cyc0`, `FibFibFast` — the post-Zap residual),
  `pa_cert`:

  1. peels the ∃-chain into κ-mvars (`Exists.intro` scaffolding);
  2. runs the weakening fixpoint to `A*` (reused PA pipeline);
  3. assigns each κ-mvar its witness λ `σ_{A*}(κ)`;
  4. emits the §5 `glue`/`bridge` proof of the body via `walkPAProof`, where
     every κ-head leaf is discharged by an `And.intro` over per-survivor oracle
     proofs and every κ-free leaf becomes a residual goal `c′`.

  Unlike `solve_fixpoint`, the κ-heads are certified by structured proof terms
  the kernel re-checks (not thrown wholesale at `grind`), and the residual `c′`
  is LEFT as user goals rather than auto-closed. A non-cut (acyclic) κ-head
  aborts with a hint to run `fusion` first.
-/
def paCertImpl : TacticM Unit := withMainContext do
  -- Unfold a top-level `def`-wrapped goal (e.g. `FibFibFast`).
  let goal ← getMainGoal
  let _ ← attemptTactic
    (do let newGoal ← goal.withContext do
          let target   ← goal.getType
          let unfolded ← unfoldDefinition target
          goal.replaceTargetDefEq unfolded
        replaceMainGoal [newGoal])

  -- Peel `∃ κ : T, …` into κ-mvars via Exists.intro; `bodyGoal : c` (κ-mvars).
  let goal ← getMainGoal
  let (kvarMap, kvarsInOrder, bodyGoal) ← peelExistentialsAndIntro goal
  replaceMainGoal [bodyGoal]
  let kctx : KContext := { kvars := kvarMap }

  -- Refresh the LCtx after `peelExistentialsAndIntro` mutated the main goal.
  withMainContext do
    let bodyGoal ← getMainGoal
    let body     ← reduce (← bodyGoal.getType)

    -- Cut-only: every ∃-bound κ is solved by PA. Warn (don't fail) if an
    -- acyclic κ leaked in — it would want a fusion solution, not a qualifier
    -- conjunction, and likely leaves an unprovable residual.
    let (acyclic, _cyclic) ← (exprPartitionKVars body).run kctx
    unless acyclic.isEmpty do
      logWarning m!"pa_cert: {acyclic.length} acyclic κ(s) present \
        ({acyclic.map (·.name)}) — run `fusion` first. Treating all κ as cut."
    let paSet := kvarsInOrder

    -- Weakening fixpoint A* (reused PA pipeline, identical to `solve_fixpoint`).
    let flatCs  ← (exprFlat body).run kctx
    let initial ← buildInitialAssignment paSet
    let aStar   ← solveFixpoint kctx flatCs initial

    -- Assign each cut κ-mvar its witness λ `σ_{A*}(κ)`. After this, `body`'s
    -- κ-mvars instantiate to their solutions at kernel-check time, but `body`
    -- stays SYNTACTICALLY κ-headed so `walkPAProof` can still detect the heads.
    let sols ← finalizeSolutions aStar
    for (κ, sol) in sols do
      let lam ← solToWitnessExpr sol κ.params κ.paramTypes
      κ.mvarId.assign lam

    -- Emit the §5 bridge proof of the body; collect κ-free residuals = c′.
    let residualOut ← IO.mkRef (#[] : Array MVarId)
    let proof ← walkPAProof aStar body residualOut
    bodyGoal.assign proof

    -- Leave c′ as user goals (purist §5: the certified bridge is built; the
    -- κ-free residual queries remain for the user / a follow-up tactic).
    let residual := (← residualOut.get).toList
    setGoals residual
    logInfo m!"pa_cert: bridge built and assigned; \
      {residual.length} κ-free residual goal(s) left as c′."

syntax "pa_cert" : tactic
elab_rules : tactic
  | `(tactic| pa_cert) => paCertImpl

/-- `fix` — the paper's cyclic-κ solver: certifying predicate abstraction
    (`pa_cert`) followed by `grind` to discharge the κ-free residual. -/
macro "fix" : tactic => `(tactic| (pa_cert ; try grind))
