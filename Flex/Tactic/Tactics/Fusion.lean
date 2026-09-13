import Flex.Tactic.Tactics.RewriteKs
import Flex.Tactic.Utils
import Flex.Core
import Flex.Fusion
import Flex.Zap

open Lean Meta Elab Tactic

/-- Debug trace for the `fusion` tactic (per-κ σ̂ + prefix counts, elimination
    summary). Off by default — enable with `set_option trace.Fusion.debug true`. -/
initialize registerTraceClass `Fusion.debug

/-! ## `fusion` tactic

  Cosman–Jhala fusion for the *acyclic* κ's of a refinement constraint — the
  first half of the solver, complementing `fixpoint` (predicate abstraction for
  the cyclic κ's).

  On a goal `∃ κ₁ … κₙ, P`, `fusion`:

  1. peels the ∃-chain into fresh κ-mvars and classifies them into acyclic /
     cyclic (`exprPartitionKVars`);
  2. for each acyclic κ in topological order, computes its strongest solution
     `σ̂` (`sol`) and eliminates it (`elim*`): head-position κ-apps collapse to
     `True`, hypothesis-position κ-apps are replaced by `σ̂`;
  3. rebuilds the proof (the `destructAndBuild`/`nav` bridge) and leaves
     the residual `∃ κ_cyclic, P'` — body with every acyclic κ gone, cyclic κ's
     still bound — plus any leaf obligations fusion could not discharge.

  Hand the residual to `fix`, or use `solve` (= `zap` then `fix`). -/
syntax "zap" : tactic

/-- Build the bridge proof `(∃ κ_cyclic, P') → (∃ κ₁ … κₙ, P)`: ∃-eliminate the
    cyclic-κ witnesses out of the supplied proof (recursing over `cycRem`), then
    re-introduce all κ's over the original ∃-chain — acyclic κ's via their
    solutions `kLams`, cyclic κ's via the eliminated fvars — with `nav`
    supplying the body proof. -/
partial def destructAndBuild
    (kvars : Array KVar)
    (kLams : List (KVar × Expr))
    (prefixInfo : Std.HashMap MVarId (Nat × Nat × Nat))
    (bodyWithMvars : Expr)
    (originalType : Expr)
    (residualOut : IO.Ref (Array MVarId))
    (curWit : Expr) (curWitTy : Expr)
    (cycRem : List KVar)
    (cycAcc : Array (KVar × Expr)) :
    MetaM Expr := do
  match cycRem with
  | [] =>
    -- curWit : c′_with_cyclic_fvars. Use it as h_c' for nav.
    -- An acyclic κ's solution σ̂ may reference a cyclic κ (e.g. σ̂(k1) mentions
    -- k0 for the clause `k0 i → k1 i`). Here the cyclic κ is in scope only as
    -- its fvar `fv` (bound by the enclosing `Exists.elim`), not as its mvar, so
    -- substitute cyclic mvars → fvars in BOTH the body and the κ-solutions
    -- before emitting; otherwise the unassigned cyclic mvar leaks into the
    -- proof term ("(kernel) declaration has metavariables").
    let cycSubst := cycAcc.toList.map fun (κ, fv) => (κ.mvarId, fv)
    let bodyFV := replaceKMvarsWithFvars cycSubst bodyWithMvars
    let kLams  := kLams.map fun (κ, lam) =>
      (κ, replaceKMvarsWithFvars cycSubst lam)
    -- Assign acyclic κ-mvars to their (cyclic-fvar-substituted) solutions HERE,
    -- inside the cyclic fvars' scope, so defeq β-reduces κ-applications in
    -- bodyFV to σ̂ over the SAME fvars the residual c′ uses. Doing it at
    -- analysis time (before `κfv` existed) baked in the cyclic mvar and made
    -- k-use/guard types disagree with `curWit` (`h_c'`).
    for (κ, lam) in kLams do κ.mvarId.assign lam
    let bodyProof ← nav kLams bodyFV curWit [] [] [] prefixInfo residualOut
    -- Build Exists.intro chain in ORIGINAL κ-order over originalType.
    let kLamMap : Std.HashMap MVarId Expr :=
      kLams.foldl (fun m (κ, lam) => m.insert κ.mvarId lam)
        (∅ : Std.HashMap MVarId Expr)
    let cycFvMap : Std.HashMap MVarId Expr :=
      cycAcc.foldl (fun m (κ, fv) => m.insert κ.mvarId fv)
        (∅ : Std.HashMap MVarId Expr)
    let rec buildIntros (curType : Expr) (idx : Nat) : MetaM Expr := do
      let curType ← whnf curType
      if curType.isAppOfArity ``Exists 2 then
        let α := curType.appFn!.appArg!
        let pred := curType.appArg!
        let κmvar := kvars[idx]!.mvarId
        let witness ← match kLamMap.get? κmvar with
          | some lam => pure lam
          | none =>
            match cycFvMap.get? κmvar with
            | some fv => pure fv
            | none => throwError "fusion: no witness for κ idx={idx}"
        let restType := pred.beta #[witness]
        let restProof ← buildIntros restType (idx + 1)
        mkAppOptM ``Exists.intro
          #[some α, some pred, some witness, some restProof]
      else
        return bodyProof
    buildIntros originalType 0
  | κ :: rest => do
    let curWitTyW ← whnf curWitTy
    let α    := curWitTyW.appFn!.appArg!
    let pred := curWitTyW.appArg!
    withLocalDeclD κ.name α fun κfv => do
      let nextTy := pred.beta #[κfv]
      withLocalDeclD `h_inner nextTy fun innerFv => do
        let innerProof ← destructAndBuild kvars kLams prefixInfo bodyWithMvars
          originalType residualOut innerFv nextTy rest
          (cycAcc.push (κ, κfv))
        let elimLam ← mkLambdaFVars #[κfv, innerFv] innerProof
        mkAppOptM ``Exists.elim
          #[some α, some pred, none, some curWit, some elimLam]

elab_rules : tactic
  | `(tactic| zap) => withMainContext do
      let goal ← getMainGoal
      let originalType ← goal.getType

      -- Stash data computed inside the withPeeledExists closure.
      let dataRef : IO.Ref (Option (
          Expr                              -- newGoalType
        × List (KVar × Expr)                -- kLams (acyclic only)
        × List KVar                         -- acyclic κs
        × List KVar                         -- cyclic κs
        × Array KVar                        -- kvars in original ∃-order
        × Expr                              -- bodyWithMvars
        × Std.HashMap MVarId (Nat × Nat × Nat)  -- prefixInfo (per acyclic κ)
        )) ← IO.mkRef none

      withPeeledExists originalType #[] fun binders body => do
        if binders.size == 0 then
          throwError "fusion: goal has no ∃-binders"

        -- Build fresh κ-mvars + substitute fvar → mvar in body for KM classification.
        let mut kvars : Array KVar := #[]
        let mut bodyWithMvars := body
        for (name, ty, fvar) in binders do
          let paramTypes ← collectArrowTypes ty
          let params := (List.range paramTypes.length).map fun i =>
            Name.mkSimple s!"z{i}"
          let mvar ← mkFreshExprMVar (some ty) (kind := .syntheticOpaque)
          kvars := kvars.push
            { name, params, paramTypes, mvarId := mvar.mvarId! }
          bodyWithMvars := bodyWithMvars.replaceFVar fvar mvar

        let kctxMap := kvars.foldl
          (fun acc k => acc.insert k.mvarId k) (∅ : Std.HashMap MVarId KVar)
        let kctx : KContext := { kvars := kctxMap }
        let (acyclic, cyclic) ← (exprPartitionKVars bodyWithMvars).run kctx

        if acyclic.isEmpty then
          dataRef.set none
          return

        -- Acyclic loop: compute kLams + curr + prefixInfo.
        let (curr, kLams, prefixInfo) ← benchPhase "fusion" "sol" do
          let mut curr := bodyWithMvars
          let mut kLams : List (KVar × Expr) := []
          let mut prefixInfo : Std.HashMap MVarId (Nat × Nat × Nat) := ∅
          for κ in acyclic do
            -- LCA-scoped, structure-preserving σ̂ + prefix counts (= "same level
            -- of scope as original fusion": prefix binders fold into κ-params,
            -- no extra ∃/guards in the solution).
            let r ← (exprSolScopedPres κ curr).run kctx
            trace[Fusion.debug] m!"sol = {r.sol}  (nB={r.nBinders} nG={r.nGuards} nOr={r.nOr})"
            let sol    := simplifyAndExists r.sol
            let lam    ← solToWitnessExpr sol κ.params κ.paramTypes
            kLams := kLams ++ [(κ, lam)]
            prefixInfo := prefixInfo.insert κ.mvarId (r.nBinders, r.nGuards, r.nOr)
            curr   ← (exprElimStar κ sol curr).run kctx
          pure (curr, kLams, prefixInfo)

        -- (Acyclic κ-mvars are assigned later, inside `destructAndBuild`'s
        -- cyclic-fvar scope, to their cyclic-fvar-substituted solutions.)

        -- Substitute cyclic-κ-mvars in curr with original fvars (still in scope).
        let cyclicSubst : List (MVarId × Expr) := cyclic.map fun κ =>
          let idx := (kvars.findIdx? (·.mvarId == κ.mvarId)).getD 0
          (κ.mvarId, binders[idx]!.2.2)
        let curr_fv := replaceKMvarsWithFvars cyclicSubst curr

        -- Build new goal type by abstracting cyclic fvars into an ∃-chain.
        let cyclicBinders : Array (Name × Expr × Expr) :=
          cyclic.toArray.map fun κ =>
            let idx := (kvars.findIdx? (·.mvarId == κ.mvarId)).getD 0
            binders[idx]!
        let newGoalType ← mkExistsChain cyclicBinders curr_fv

        dataRef.set (some (newGoalType, kLams, acyclic, cyclic, kvars,
                           bodyWithMvars, prefixInfo))

      -- ─── Back in original lctx ─────────────────────────────────────────
      let some (newGoalType, kLams, acyclic, cyclic, kvars, bodyWithMvars, prefixInfo)
        ← dataRef.get
        | do
            trace[Fusion.debug] m!"fusion: no acyclic κs to eliminate"
            return

      -- Create bridge and new-goal mvars in original lctx.
      let bridgeType ← goal.withContext do
        mkArrow newGoalType originalType
      let bridgeMvar ← mkFreshExprMVar (some bridgeType) (kind := .syntheticOpaque)
      let newGoalM  ← mkFreshExprMVar (some newGoalType) (kind := .syntheticOpaque)
      goal.assign (mkApp bridgeMvar newGoalM)

      -- ─── Construct bridge term: λ h => Exists.elim … nav ──────
      let residualOut ← IO.mkRef #[]

      let bridge ← benchPhase "fusion" "build" <|
        withLocalDeclD `h newGoalType fun h_fv => do
          let inner ← destructAndBuild kvars kLams prefixInfo bodyWithMvars originalType
            residualOut h_fv newGoalType cyclic #[]
          mkLambdaFVars #[h_fv] inner

      bridgeMvar.mvarId!.assign bridge

      let residuals := (← residualOut.get).toList
      -- Hand the closer a CLEAN residual. The structure-preserving σ̂ leaves
      -- inert `False ∨`/`True ∧`/dead-`∃` noise — required for the bridge's
      -- And/Or mirror, but it overflows simp/grind on deep VCs (e.g. Quicksort).
      -- `collapseInert` peels it in one structural pass (`iff : e ↔ clean`) and
      -- discharges the noisy goal via `iff.mpr`, leaving the user the clean goal.
      let cleanGoals ← benchPhase "fusion" "clean" <| goal.withContext do
        (newGoalM.mvarId! :: residuals).mapM fun m => do
          let ty ← m.getType
          let (clean, iff) ← collapseInert ty
          if clean == ty then
            return m
          else
            let cleanM ← mkFreshExprMVar (some clean) (kind := .syntheticOpaque)
            m.assign (← mkAppM ``Iff.mpr #[iff, cleanM])
            return cleanM.mvarId!
      trace[Fusion.debug] m!"fusion: eliminated {acyclic.length} acyclic κ \
                {acyclic.map (·.name)}; new goal is ∃ \
                {cyclic.length} cyclic κ + body; \
                {residuals.length} residual obligation(s)"
      replaceMainGoal cleanGoals

/-- Backward-compatible alias — `fusion` is the former name of the acyclic
    κ-eliminator now called `zap`. -/
macro "fusion" : tactic => `(tactic| zap)

-- ───────────────────────────────────────────────────────────────────────
-- Tests for zap (also exercises the `fusion` alias)
-- ───────────────────────────────────────────────────────────────────────

/-- A-test: one acyclic κ. fusion should leave only the non-κ leaf. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  fusion
  all_goals first | rfl | grind

/-- B-test: two independent acyclic κs.  fusion should leave two
    non-κ leaves. -/
example :
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν) := by
  fusion
  all_goals first | rfl | grind

/-- D-test (Phase 5): mixed — κ1 cyclic (self-loop), κ2 acyclic.
    fusion eliminates κ2 in-place; residual is the single ∃-form goal
    `∃ κ1, c′`. The cyclic-κ1 witness `λ y => 0 ≤ y` is supplied manually
    (grind cannot synthesize it). -/
example : ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
      (∀ y : Int, κ1 y → κ1 (y + 1))
    ∧ (∀ ν : Int, ν = 0 → κ1 ν)
    ∧ (∀ ν : Int, ν = 0 → κ2 ν)
    ∧ (∀ z : Int, κ2 z → 0 ≤ z) := by
  fusion
  exact ⟨fun y => 0 ≤ y, by grind⟩
