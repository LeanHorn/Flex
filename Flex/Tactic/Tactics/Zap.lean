import Flex.Tactic.Tactics.RewriteKs
import Flex.Tactic.Utils
import Flex.Core
import Flex.Preprocess.Cleanup
import Flex.Fusion
import Flex.Zap

open Lean Meta Elab Tactic

/-- Trace Zap's solutions and elimination steps with `trace.Zap.debug`. -/
initialize registerTraceClass `Zap.debug

syntax "zap" : tactic

/-- Rebuild the original existential VC from a proof of the residual over cut
variables, using `kLams` for eliminated predicates and local witnesses for the cut. -/
partial def destructAndBuild
    (leaf   : LeafHandler)
    (kvars  : Array KVar)
    (kLams  : List (KVar × Expr))
    (bodyWithMvars  : Expr)
    (originalType   : Expr)
    (curWit : Expr) (curWitTy : Expr)
    (cutRem : List KVar)
    (cutAcc : Array (KVar × Expr)) :
    TermElabM Expr := do
  match cutRem with
  | [] =>
    -- curWit : c′_with_cut_fvars. Use it as h_c' for cert.
    -- An elimination κ's solution σ̂ may reference a cut κ (e.g. σ̂(k1) mentions
    -- k0 for the clause `k0 i → k1 i`). Here the cut κ is in scope only as
    -- its fvar `fv` (bound by the enclosing `Exists.elim`), not as its mvar, so
    -- substitute cut mvars → fvars in BOTH the body and the κ-solutions
    -- before emitting; otherwise the unassigned cut mvar leaks into the
    -- proof term ("(kernel) declaration has metavariables").
    let cutSubst := cutAcc.toList.map fun (κ, fv) => (κ.mvarId, fv)
    let bodyFV := replaceKMvarsWithFvars cutSubst bodyWithMvars
    let kLams  := kLams.map fun (κ, lam) =>
      (κ, replaceKMvarsWithFvars cutSubst lam)
    -- Assign elimination κ-mvars to their (cut-fvar-substituted) solutions HERE,
    -- inside the cut fvars' scope, so defeq β-reduces κ-applications in
    -- bodyFV to σ̂ over the SAME fvars the residual c′ uses. Doing it at
    -- analysis time (before `κfv` existed) baked in the cut mvar and made
    -- k-use/guard types disagree with `curWit` (`h_c'`).
    for (κ, lam) in kLams do κ.mvarId.assign lam
    let bodyProof ← cert leaf kLams bodyFV curWit [] [] []
    -- Build Exists.intro chain in ORIGINAL κ-order over originalType.
    let kLamMap : Std.HashMap MVarId Expr :=
      kLams.foldl (fun m (κ, lam) => m.insert κ.mvarId lam)
        (∅ : Std.HashMap MVarId Expr)
    let cutFvMap : Std.HashMap MVarId Expr :=
      cutAcc.foldl (fun m (κ, fv) => m.insert κ.mvarId fv)
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
            match cutFvMap.get? κmvar with
            | some fv => pure fv
            | none => throwError "zap: no witness for κ idx={idx}"
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
        let innerProof ← destructAndBuild leaf kvars kLams bodyWithMvars
          originalType innerFv nextTy rest (cutAcc.push (κ, κfv))
        let elimLam ← mkLambdaFVars #[κfv, innerFv] innerProof
        mkAppOptM ``Exists.elim
          #[some α, some pred, none, some curWit, some elimLam]

/-- A leaf handler for `cert` plus the `benchPhase` label that attributes its
    cost. `mkHandler` receives the per-κ prefix counts and the residual sink
    that `zapImpl` allocates: the emitting leaf needs both, search leaves ignore
    them. -/
structure LeafStrategy where
  label     : String
  mkHandler : Std.HashMap MVarId (Nat × Nat × Nat) → IO.Ref (Array MVarId) → LeafHandler

/-- Emit exact proofs at predicate heads and report Zap phase timings. -/
def emitStrategy : LeafStrategy := { label := "zap", mkHandler := emitLeaf }

/-- The `zap` pipeline, parameterised by what happens at each κ-head leaf. -/
def zapImpl (s : LeafStrategy) (preprocess : Bool := true) : TacticM Unit := focus <| withMainContext do
  if preprocess then
    liftMetaTactic fun goal => do
      let goal ← Flex.Preprocess.prepareGoal goal
      return if ← goal.isAssignedOrDelayedAssigned then [] else [goal]
  if (← getGoals).isEmpty then return
  let goal ← getMainGoal
  let originalType ← goal.getType

  -- Stash data computed inside the withPeeledExists closure.
  let dataRef : IO.Ref (Option (
      Expr                              -- newGoalType
    × List (KVar × Expr)                -- kLams (eliminated only)
    × List KVar                         -- elimination κs
    × List KVar                         -- cut κs
    × Array KVar                        -- kvars in original ∃-order
    × Expr                              -- bodyWithMvars
    × Std.HashMap MVarId (Nat × Nat × Nat)  -- prefixInfo (per elimination κ)
    )) ← IO.mkRef none

  withPeeledExists originalType #[] fun binders body => do
    if binders.size == 0 then
      throwError "{s.label}: goal has no ∃-binders"

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
    let (elimVars, cutVars) ← (exprPartitionKVars bodyWithMvars).run kctx

    if elimVars.isEmpty then
      dataRef.set none
      return

    -- Elimination loop: compute kLams + curr + prefixInfo.
    let (curr, kLams, prefixInfo) ← benchPhase s.label "sol" do
      let mut curr := bodyWithMvars
      let mut kLams : List (KVar × Expr) := []
      let mut prefixInfo : Std.HashMap MVarId (Nat × Nat × Nat) := ∅
      for κ in elimVars do
        -- LCA-scoped, structure-preserving σ̂ + prefix counts (= "same level
        -- of scope as original zap": prefix binders fold into κ-params,
        -- no extra ∃/guards in the solution).
        let r ← (exprSolScopedPres κ curr).run kctx
        trace[Zap.debug] m!"sol = {r.sol}  (nB={r.nBinders} nG={r.nGuards} nOr={r.nOr})"
        let sol    := simplifyAndExists r.sol
        let lam    ← solToWitnessExpr sol κ.params κ.paramTypes
        kLams := kLams ++ [(κ, lam)]
        prefixInfo := prefixInfo.insert κ.mvarId (r.nBinders, r.nGuards, r.nOr)
        curr   ← (exprElimStar κ sol curr).run kctx
      pure (curr, kLams, prefixInfo)

    -- (Eliminated κ-mvars are assigned later, inside `destructAndBuild`'s
    -- cut-fvar scope, to their cut-fvar-substituted solutions.)

    -- Substitute cut-κ-mvars in curr with original fvars (still in scope).
    let cutSubst : List (MVarId × Expr) := cutVars.map fun κ =>
      let idx := (kvars.findIdx? (·.mvarId == κ.mvarId)).getD 0
      (κ.mvarId, binders[idx]!.2.2)
    let curr_fv := replaceKMvarsWithFvars cutSubst curr

    -- Build new goal type by abstracting cut fvars into an ∃-chain.
    let cutBinders : Array (Name × Expr × Expr) :=
      cutVars.toArray.map fun κ =>
        let idx := (kvars.findIdx? (·.mvarId == κ.mvarId)).getD 0
        binders[idx]!
    let newGoalType ← mkExistsChain cutBinders curr_fv

    dataRef.set (some (newGoalType, kLams, elimVars, cutVars, kvars,
                       bodyWithMvars, prefixInfo))

  -- ─── Back in original lctx ─────────────────────────────────────────
  let some (newGoalType, kLams, elimVars, cutVars, kvars, bodyWithMvars, prefixInfo)
    ← dataRef.get
    | do
        trace[Zap.debug] m!"zap: no predicates to eliminate"
        return

  -- Create bridge and new-goal mvars in original lctx.
  let bridgeType ← goal.withContext do
    mkArrow newGoalType originalType
  let bridgeMvar ← mkFreshExprMVar (some bridgeType) (kind := .syntheticOpaque)
  let newGoalM  ← mkFreshExprMVar (some newGoalType) (kind := .syntheticOpaque)
  goal.assign (mkApp bridgeMvar newGoalM)

  -- ─── Construct bridge term: λ h => Exists.elim … cert ─────
  let residualOut ← IO.mkRef #[]

  let bridge ← benchPhase s.label "build" <|
    withLocalDeclD `h newGoalType fun h_fv => do
      let inner ← destructAndBuild (s.mkHandler prefixInfo residualOut) kvars kLams
        bodyWithMvars originalType h_fv newGoalType cutVars #[]
      mkLambdaFVars #[h_fv] inner

  bridgeMvar.mvarId!.assign bridge

  let residuals := (← residualOut.get).toList
  -- Hand the closer a CLEAN residual. The structure-preserving σ̂ leaves
  -- inert `False ∨`/`True ∧`/dead-`∃` noise — required for the bridge's
  -- And/Or mirror, but it overflows simp/grind on deep VCs (e.g. Quicksort).
  -- `collapseInert` peels it in one structural pass (`iff : e ↔ clean`) and
  -- discharges the noisy goal via `iff.mpr`, leaving the user the clean goal.
  let cleanGoals ← benchPhase s.label "clean" <| goal.withContext do
    (newGoalM.mvarId! :: residuals).mapM fun m => do
      let ty ← m.getType
      let (clean, iff) ← collapseInert ty
      if clean == ty then
        return m
      else
        let cleanM ← mkFreshExprMVar (some clean) (kind := .syntheticOpaque)
        m.assign (← mkAppM ``Iff.mpr #[iff, cleanM])
        return cleanM.mvarId!
  trace[Zap.debug] m!"zap: eliminated {elimVars.length} κ \
            {elimVars.map (·.name)}; new goal is ∃ \
            {cutVars.length} retained cut κ + body; \
            {residuals.length} residual obligation(s)"
  replaceMainGoal cleanGoals

elab_rules : tactic
  | `(tactic| zap) => zapImpl emitStrategy
