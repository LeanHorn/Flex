import Lean
import Aesop
import Flex.Tactic.Tactics.RewriteKs
import Flex.Tactic.Utils
import Flex.Core
import Flex.Fusion
import Flex.Zap

open Lean Meta Elab Tactic

/-! # `fusion_grind` / `fusion_aesop` — search-based acyclic-κ elimination (EVAL ONLY)

  These tactics exist **solely for the RQ2 evaluation**. They are a deliberate,
  isolated copy of the `fusion` pipeline (`Tactic/Tactics/Fusion.lean`): same
  ∃-peeling, acyclic/cyclic classification, strongest-solution `σ̂` computation,
  and `Exists.intro`/`Exists.elim` bridge. The **only** difference is how each
  acyclic-κ-head clause is discharged:

  * `fusion`        — deterministic proof term (`emitKLeaf`), the Zap algorithm.
  * `fusion_grind`  — `grind` proves the σ̂-instantiated head clause (proof search).
  * `fusion_aesop`  — `aesop` proves it (proof search).

  This file imports the (public) solver building blocks but **modifies nothing**
  under `Zap/`, `PA/`, or `Fusion/`. It is not wired into the `Flex`
  root; the eval harness imports it explicitly. -/

/-- Which search tactic discharges the acyclic-κ-head clauses. -/
inductive SearchCloser where
  | grind
  | aesop
  deriving Inhabited, BEq, Repr

/-- The tactic invoked at each acyclic-κ-head leaf. -/
def SearchCloser.run : SearchCloser → TacticM Unit
  | .grind => do evalTactic (← `(tactic| grind))
  | .aesop => do evalTactic (← `(tactic| aesop))

/-- Phase label so the eval harness can attribute heartbeats per variant
    (`[phase] fusion_grind:build=…` vs `fusion_aesop:build=…`). -/
def SearchCloser.label : SearchCloser → String
  | .grind => "fusion_grind"
  | .aesop => "fusion_aesop"

/-- Try to prove `prop` by running `closer` on a fresh goal in the *current*
    local context (so the in-scope binders/guards are available as hypotheses).
    Returns the instantiated, `sorry`-free proof on success, else `none`.

    `grind`/`aesop` report failures through the *message log* rather than the
    exception path, so we snapshot/restore the log around the attempt (the
    pattern used by `PA/Check.lean`); the fresh mvar isolates tactic state. -/
def tryTacProve (prop : Expr) (closer : SearchCloser) : TermElabM (Option Expr) := do
  let savedMsgs ← Core.getMessageLog
  let mvar ← mkFreshExprMVar (some prop) (kind := .syntheticOpaque)
  try
    let goals ← Tactic.run mvar.mvarId! closer.run
    Core.setMessageLog savedMsgs
    if !goals.isEmpty then return none
    let proof ← instantiateMVars mvar
    if proof.hasSorry then return none
    return some proof
  catch _ =>
    Core.setMessageLog savedMsgs
    return none

/-- Copy of `nav` (`Zap/Nav.lean`) whose head-acyclic-κ leaf is
    discharged by SEARCH (`closer`) instead of `emitKLeaf`. Branches (b)–(d) are
    identical to the original. On search failure the clause is pushed as a
    residual mvar (handed to the outer closer), exactly as `fusion` does for the
    leaves it cannot place. -/
partial def navSearch
    (closer : SearchCloser)
    (kLams : List (KVar × Expr))
    (goal  : Expr)
    (hCprime : Expr)
    (binders guards : List (Name × Expr × FVarId))
    (orPath : List Bool)
    (prefixInfo : Std.HashMap MVarId (Nat × Nat × Nat))
    (residualOut : IO.Ref (Array MVarId)) :
    TermElabM Expr := do
  -- (a) Head-acyclic-κ leaf → prove the σ̂-instantiated head by search.
  --     No fallback: if the search tactic cannot discharge the clause, the
  --     whole tactic fails — that failure is itself an RQ2 data point.
  if let some (_κLeaf, lam, args) := kHead? kLams goal then
    let lamBody := lam.beta args
    match ← tryTacProve lamBody closer with
    | some pf => return pf
    | none =>
      throwError "{closer.label}: search tactic failed on κ-head clause:{indentExpr lamBody}"
  -- (b) ∀ — intro fv, beta-apply hCprime to fv, recurse, λ-wrap.
  if goal.isForall then
    let dom := goal.bindingDomain!
    let name := goal.bindingName!
    let bi := goal.bindingInfo!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    return ← withLocalDecl name bi dom fun fv => do
      let body := goal.bindingBody!.instantiate1 fv
      let hCprime' := mkApp hCprime fv
      let inner ←
        if domSort.isProp then
          navSearch closer kLams body hCprime' binders
            (guards ++ [(name, dom, fv.fvarId!)]) orPath prefixInfo residualOut
        else
          navSearch closer kLams body hCprime'
            (binders ++ [(name, dom, fv.fvarId!)]) guards orPath prefixInfo residualOut
      mkLambdaFVars #[fv] inner
  -- (c) ∧ — project hCprime via And.left / And.right, recurse, And.intro.
  if let some (l, r) := goal.and? then
    let hL ← mkAppM ``And.left  #[hCprime]
    let hR ← mkAppM ``And.right #[hCprime]
    let pL ← navSearch closer kLams l hL binders guards (orPath ++ [false]) prefixInfo residualOut
    let pR ← navSearch closer kLams r hR binders guards (orPath ++ [true])  prefixInfo residualOut
    return mkAndIntro l r pL pR
  -- (d) Anything else (non-κ atom OR cyclic-κ-head app) — direct transfer.
  return hCprime

/-- Copy of `destructAndBuild` (`Tactic/Tactics/Fusion.lean`) that drives
    `navSearch` (search leaves) instead of `nav`. -/
partial def destructAndBuildSearch
    (closer : SearchCloser)
    (kvars : Array KVar)
    (kLams : List (KVar × Expr))
    (prefixInfo : Std.HashMap MVarId (Nat × Nat × Nat))
    (bodyWithMvars : Expr)
    (originalType : Expr)
    (residualOut : IO.Ref (Array MVarId))
    (curWit : Expr) (curWitTy : Expr)
    (cycRem : List KVar)
    (cycAcc : Array (KVar × Expr)) :
    TermElabM Expr := do
  match cycRem with
  | [] =>
    let cycSubst := cycAcc.toList.map fun (κ, fv) => (κ.mvarId, fv)
    let bodyFV := replaceKMvarsWithFvars cycSubst bodyWithMvars
    let kLams  := kLams.map fun (κ, lam) =>
      (κ, replaceKMvarsWithFvars cycSubst lam)
    for (κ, lam) in kLams do κ.mvarId.assign lam
    let bodyProof ← navSearch closer kLams bodyFV curWit [] [] [] prefixInfo residualOut
    let kLamMap : Std.HashMap MVarId Expr :=
      kLams.foldl (fun m (κ, lam) => m.insert κ.mvarId lam)
        (∅ : Std.HashMap MVarId Expr)
    let cycFvMap : Std.HashMap MVarId Expr :=
      cycAcc.foldl (fun m (κ, fv) => m.insert κ.mvarId fv)
        (∅ : Std.HashMap MVarId Expr)
    let rec buildIntros (curType : Expr) (idx : Nat) : TermElabM Expr := do
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
            | none => throwError "fusion_search: no witness for κ idx={idx}"
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
        let innerProof ← destructAndBuildSearch closer kvars kLams prefixInfo bodyWithMvars
          originalType residualOut innerFv nextTy rest
          (cycAcc.push (κ, κfv))
        let elimLam ← mkLambdaFVars #[κfv, innerFv] innerProof
        mkAppOptM ``Exists.elim
          #[some α, some pred, none, some curWit, some elimLam]

/-- Copy of the `fusion` elaborator body, parameterised by the search `closer`.
    Identical to `fusion` except (i) it drives `destructAndBuildSearch`, and
    (ii) phase labels are the closer's (`fusion_grind`/`fusion_aesop`) so the
    eval harness can attribute heartbeats per variant. -/
def fusionSearchImpl (closer : SearchCloser) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let originalType ← goal.getType

  let dataRef : IO.Ref (Option (
      Expr
    × List (KVar × Expr)
    × List KVar
    × List KVar
    × Array KVar
    × Expr
    × Std.HashMap MVarId (Nat × Nat × Nat)
    )) ← IO.mkRef none

  withPeeledExists originalType #[] fun binders body => do
    if binders.size == 0 then
      throwError "fusion_search: goal has no ∃-binders"

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

    let (curr, kLams, prefixInfo) ← benchPhase closer.label "sol" do
      let mut curr := bodyWithMvars
      let mut kLams : List (KVar × Expr) := []
      let mut prefixInfo : Std.HashMap MVarId (Nat × Nat × Nat) := ∅
      for κ in acyclic do
        let r ← (exprSolScopedPres κ curr).run kctx
        let sol    := simplifyAndExists r.sol
        let lam    ← solToWitnessExpr sol κ.params κ.paramTypes
        kLams := kLams ++ [(κ, lam)]
        prefixInfo := prefixInfo.insert κ.mvarId (r.nBinders, r.nGuards, r.nOr)
        curr   ← (exprElimStar κ sol curr).run kctx
      pure (curr, kLams, prefixInfo)

    let cyclicSubst : List (MVarId × Expr) := cyclic.map fun κ =>
      let idx := (kvars.findIdx? (·.mvarId == κ.mvarId)).getD 0
      (κ.mvarId, binders[idx]!.2.2)
    let curr_fv := replaceKMvarsWithFvars cyclicSubst curr

    let cyclicBinders : Array (Name × Expr × Expr) :=
      cyclic.toArray.map fun κ =>
        let idx := (kvars.findIdx? (·.mvarId == κ.mvarId)).getD 0
        binders[idx]!
    let newGoalType ← mkExistsChain cyclicBinders curr_fv

    dataRef.set (some (newGoalType, kLams, acyclic, cyclic, kvars,
                       bodyWithMvars, prefixInfo))

  let some (newGoalType, kLams, acyclic, cyclic, kvars, bodyWithMvars, prefixInfo)
    ← dataRef.get
    | return

  let bridgeType ← goal.withContext do
    mkArrow newGoalType originalType
  let bridgeMvar ← mkFreshExprMVar (some bridgeType) (kind := .syntheticOpaque)
  let newGoalM  ← mkFreshExprMVar (some newGoalType) (kind := .syntheticOpaque)
  goal.assign (mkApp bridgeMvar newGoalM)

  let residualOut ← IO.mkRef #[]

  let bridge ← benchPhase closer.label "build" <|
    withLocalDeclD `h newGoalType fun h_fv => do
      let inner ← destructAndBuildSearch closer kvars kLams prefixInfo bodyWithMvars originalType
        residualOut h_fv newGoalType cyclic #[]
      mkLambdaFVars #[h_fv] inner

  bridgeMvar.mvarId!.assign bridge

  let residuals := (← residualOut.get).toList
  let cleanGoals ← benchPhase closer.label "clean" <| goal.withContext do
    (newGoalM.mvarId! :: residuals).mapM fun m => do
      let ty ← m.getType
      let (clean, iff) ← collapseInert ty
      if clean == ty then
        return m
      else
        let cleanM ← mkFreshExprMVar (some clean) (kind := .syntheticOpaque)
        m.assign (← mkAppM ``Iff.mpr #[iff, cleanM])
        return cleanM.mvarId!
  let _ := acyclic
  replaceMainGoal cleanGoals

syntax "fusion_grind" : tactic
syntax "fusion_aesop" : tactic

elab_rules : tactic
  | `(tactic| fusion_grind) => fusionSearchImpl .grind
  | `(tactic| fusion_aesop) => fusionSearchImpl .aesop

-- ───────────────────────────────────────────────────────────────────────
-- Tests (mirror the `fusion` examples in Tactic/Tactics/Fusion.lean)
-- ───────────────────────────────────────────────────────────────────────

/-- A-test: one acyclic κ, discharged by grind in-bridge. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  fusion_grind
  all_goals first | rfl | grind

/-- A-test with aesop. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  fusion_aesop
  all_goals first | rfl | grind

/-- B-test: two independent acyclic κs. -/
example :
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν) := by
  fusion_grind
  all_goals first | rfl | grind
