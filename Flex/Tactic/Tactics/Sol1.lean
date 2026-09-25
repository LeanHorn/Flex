import Lean

import Flex.Core
import Flex.Fusion
import Flex.Tactic.Utils
import Flex.Tactic.Tactics.RewriteKs
import Flex.Tactic.Tactics.Lazy

open Lean Meta Elab Tactic

/-! ## `solK1` tactic

  Solve exactly one acyclic κ in the goal's ∃-chain, introducing the
  computed witness as a `let`-bound local hypothesis. The remaining ∃-chain
  is preserved; the solved κ continues to appear in the goal by *name*
  (folded), so the user can later choose to `lazy_unfold κ`.

  Example transformation:
      goal:    ∃ κ₁ : Int → Prop, ∃ κ₂ : Int → Prop, P(κ₁, κ₂)
      after `solK1`:
        κ₂ : Int → Prop := fun x => …
        goal:  ∃ κ₁ : Int → Prop, P(κ₁, κ₂)

  Strategy:
    1. `rewriteKs` to canonicalize the ∃-chain order.
    2. Peel ∃-binders into fresh syntheticOpaque κ-mvars (no Exists.intro).
    3. Partition into (acyclic, cyclic); walk acyclic in topo order and
       pick the first κ whose sol1 witness is *closed* (no references to
       other scratch κ-mvars). A κ classified as acyclic but with a
       hypothesis-position self-appearance produces a witness referencing
       itself — that κ needs `solve_fixpoint`, not `solK1`.
    4. Compute the witness lambda via `exprElim1` + `solToWitnessExpr`.
    5. Permute the chosen κ to the outermost ∃ via `perm_exists`.
    6. Delab the witness and invoke `name_witness` to bind it as a let. -/

private def solK1Impl (κName? : Option (TSyntax `ident)) : TacticM Unit :=
  withMainContext do
    -- 1. Canonicalize the ∃-chain order. Best effort.
    let _ ← attemptTactic (evalTactic (← `(tactic| rewriteKs)))

    let goal ← getMainGoal
    let goalType ← goal.getType
    withPeeledExists goalType #[] fun binders body => do
      if binders.size == 0 then
        logInfo m!"solK1: goal has no ∃-binders, nothing to do"
        return

      -- 2. Bridge: ∃-bound fvars → scratch syntheticOpaque mvars.
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

      -- 3. Partition into acyclic (topo order, sinks first) and cyclic.
      let kctxMap := kvars.foldl
        (fun acc k => acc.insert k.mvarId k) (∅ : Std.HashMap MVarId KVar)
      let kctx : KContext := { kvars := kctxMap }
      let (acyclic, cyclic) ← (exprPartitionKVars bodyWithMvars).run kctx

      if acyclic.isEmpty then
        logInfo m!"solK1: no acyclic κ to solve \
                   (cyclic: {cyclic.map (·.name)})"
        return

      -- 4. Determine candidate list (user override or full acyclic order).
      let candidates : List KVar ← match κName? with
        | none    => pure acyclic
        | some nm =>
          let n := nm.getId
          match acyclic.find? (·.name == n) with
          | some κ => pure [κ]
          | none =>
            throwError "solK1: κ '{n}' is not in the acyclic list \
              (acyclic: {acyclic.map (·.name)}, cyclic: {cyclic.map (·.name)})"

      -- 5. Nav candidates; pick the first whose witness is closed
      --    (no references back to scratch κ-mvars).
      let mut chosen? : Option (KVar × Expr) := none
      for cand in candidates do
        match chosen? with
        | some _ => pure ()
        | none =>
          let (sol, _) ← (exprElim1 cand bodyWithMvars).run kctx
          let sol := simplifyExpr sol
          let witnessLam ← solToWitnessExpr sol cand.params cand.paramTypes
          let hasScratch := kvars.any fun κ =>
            witnessLam.containsMVar κ.mvarId
          if !hasScratch then
            chosen? := some (cand, witnessLam)

      match chosen? with
      | none =>
        if κName?.isSome then
          throwError "solK1: named κ's witness references other κ-mvars \
            (self- or forward-reference); use `solve_fixpoint` instead"
        else
          logInfo m!"solK1: no acyclic κ with a closed witness \
              (acyclic: {acyclic.map (·.name)}, \
               cyclic: {cyclic.map (·.name)})"
      | some (chosen, witnessLam) =>
        -- 6. Locate chosen κ's binder index.
        let some chosenIdx :=
            (List.range binders.size).find? fun i =>
              kvars[i]!.mvarId == chosen.mvarId
          | throwError "solK1: internal error — chosen κ not found in binders"

        -- 7. Permute chosen κ to position 0 (outermost) if needed.
        if chosenIdx != 0 then
          let others := (List.range binders.size).filter (· != chosenIdx)
          let perm : Array Nat := (chosenIdx :: others).toArray
          let newBinders := perm.map fun i => binders[i]!
          let newType ← mkExistsChain newBinders body

          -- NOTE: create new-goal mvars in the original goal's lctx, not
          -- the extended one from withPeeledExists, so named fvars don't
          -- leak into the residual goal's context.
          let (iffMVar, newGoalM) ← goal.withContext do
            let iffType   ← mkAppM ``Iff #[goalType, newType]
            let iffMVar'  ← mkFreshExprMVar (some iffType)
                              (kind := .syntheticOpaque)
            let newGoalM' ← mkFreshExprMVar (some newType)
                              (kind := .syntheticOpaque)
            pure (iffMVar', newGoalM')

          goal.assign (← mkAppM ``Iff.mpr #[iffMVar, newGoalM])
          setGoals [iffMVar.mvarId!, newGoalM.mvarId!]
          evalTactic (← `(tactic| perm_exists))
          setGoals [newGoalM.mvarId!]

        -- 8. Bind κ as a let-decl + discharge the outermost ∃ via
        --    Exists.intro, all at the Expr level. Avoiding delab keeps the
        --    witness's type annotations (delab strips `∃ a : T, …` to
        --    `∃ a, …`, and re-elab fails when `T` isn't reconstructable).
        let mainGoal ← getMainGoal
        let mainTy ← mainGoal.withContext do whnf (← mainGoal.getType)
        unless mainTy.isAppOfArity ``Exists 2 do
          throwError "solK1: expected ∃ at outermost position after \
                      permutation, got{indentExpr mainTy}"
        let α    := mainTy.getArg! 0
        let pred := mainTy.getArg! 1
        let lvls := mainTy.getAppFn.constLevels!

        let definedGoal ← mainGoal.define chosen.name α witnessLam
        let (κFVarId, introdGoal) ← definedGoal.intro1P
        introdGoal.withContext do
          let κFvar    := mkFVar κFVarId
          let proofTy  := pred.beta #[κFvar]
          let proofMVar ← mkFreshExprMVar (some proofTy)
          let proof    := mkApp4 (mkConst ``Exists.intro lvls) α pred κFvar proofMVar
          introdGoal.assign proof
          replaceMainGoal [proofMVar.mvarId!]

syntax (name := solK1) "solK1" (ppSpace colGt ident)? : tactic

elab_rules : tactic
  | `(tactic| solK1)             => solK1Impl none
  | `(tactic| solK1 $name:ident) => solK1Impl (some name)


-- Single acyclic κ. `solK1` binds κ and leaves the residual proof
-- obligation with κ folded.
def solK1_ex1 : Prop :=
  ∃ κ : Int → Prop, ∀ x : Int, x = 0 → κ x

example : solK1_ex1 := by
  unfold solK1_ex1
  solK1
  lazy_unfold κ
  grind

--  Two independent acyclic κs. Repeated `solK1` peels them one at
--  a time; both end up as let-decls referenced by name.
def solK1_ex2 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
    ∀ x : Int, (∀ ν, ν = x + 1 → κ1 ν) ∧ (∀ ν, ν = x - 1 → κ2 ν)

example : solK1_ex2 := by
  unfold solK1_ex2
  solK1
  solK1
  lazy_unfold κ1
  lazy_unfold κ2
  grind

-- **3. `lazy_unfold` after `solK1`.** The witness stays folded by default;
-- `lazy_unfold κ` inlines it on demand for the current goal only.
example : solK1_ex1 := by
  unfold solK1_ex1
  solK1
  lazy_unfold κ
  grind

/-- **4. Explicit κ name + reorder.** `solK1 κ2` permutes κ2 to the outermost
    ∃ via `perm_exists`, then binds it. κ1 stays in the residual goal. -/
def solK1_ex4 : Prop :=
  ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
    ∀ x : Int, (∀ ν, ν = x + 1 → κ1 ν) ∧ (∀ ν, ν = x - 1 → κ2 ν)

example : solK1_ex4 := by
  unfold solK1_ex4
  solK1 κ2
  solK1 κ1
  lazy_unfold κ1
  lazy_unfold κ2
  grind
