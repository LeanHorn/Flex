import Lean

import Flex.Core
import Flex.Fusion

open Lean Meta Elab Tactic

/-! ## `perm_exists` tactic

  Proves `(∃ x₀ x₁ … xₙ, P) ↔ (∃ y₀ y₁ … yₙ, P)` (or the `→` direction)
  when both sides have the same body and the binder *names* match up
  (just in a different order).

  Strategy: `rintro ⟨src…, h⟩; exact ⟨dst…, h⟩`.
-/

/-- Nav the head ∃-chain, returning the binder names in source order. -/
private partial def collectExNames (e : Expr) : MetaM (List Name) := do
  let e ← whnf e
  if e.isAppOfArity ``Exists 2 then
    let pred := e.getArg! 1
    if pred.isLambda then
      let α := e.getArg! 0
      withLocalDeclD pred.bindingName! α fun fvar => do
        let rest ← collectExNames (pred.bindingBody!.instantiate1 fvar)
        return pred.bindingName! :: rest
    else return []
  else return []

/-- Build an rintro pattern `⟨n₀, n₁, …, nₖ₋₁, h⟩` from a list of names. -/
private def mkAnonPat (names : List Name) (hyp : Name) :
    MetaM (TSyntax `rintroPat) := do
  let idents : Array (TSyntax `rcasesPat) ←
    (names ++ [hyp]).toArray.mapM fun n =>
      `(rcasesPat| $(mkIdent n):ident)
  `(rintroPat| ⟨$idents,*⟩)

/-- Build an anonymous constructor `⟨n₀, …, nₖ₋₁, h⟩` term. -/
private def mkAnonCtorTerm (names : List Name) (hyp : Name) :
    MetaM (TSyntax `term) := do
  let idents : Array (TSyntax `term) ←
    (names ++ [hyp]).toArray.mapM fun n =>
      pure ⟨mkIdent n⟩
  `(term| ⟨$idents,*⟩)

/-- Prove one direction: `(∃ srcNames, P) → (∃ dstNames, P)`. -/
private def permDirection (srcNames dstNames : List Name) : TacticM Unit := do
  let hyp : Name := `h
  let srcPat ← mkAnonPat srcNames hyp
  let dstCtor ← mkAnonCtorTerm dstNames hyp
  evalTactic (← `(tactic| (rintro $srcPat; exact $dstCtor)))

/-- `perm_exists` — prove `P₁ ↔ P₂` (or `P₁ → P₂`) when both sides are
    `∃`-chains over the same body, just permuted. Matched by binder name. -/
elab "perm_exists" : tactic => withMainContext do
  let goalType ← (← getMainGoal).getType
  let goalType ← whnf goalType
  if goalType.isAppOfArity ``Iff 2 then
    let lhs := goalType.getArg! 0
    let rhs := goalType.getArg! 1
    let lNames ← collectExNames lhs
    let rNames ← collectExNames rhs
    if lNames.length != rNames.length then
      throwError "perm_exists: ∃-chains have different lengths \
        ({lNames.length} vs {rNames.length})"
    evalTactic (← `(tactic| constructor))
    permDirection lNames rNames
    permDirection rNames lNames
  else if goalType.isForall && !goalType.bindingBody!.hasLooseBVars then
    let lhs := goalType.bindingDomain!
    let rhs := goalType.bindingBody!
    let lNames ← collectExNames lhs
    let rNames ← collectExNames rhs
    if lNames.length != rNames.length then
      throwError "perm_exists: ∃-chains have different lengths"
    permDirection lNames rNames
  else
    throwError "perm_exists: expected ↔ or → between ∃-chains, \
      got{indentExpr goalType}"

/-! ## `rewriteKs` tactic

  Reorders the head ∃-chain of the goal so that κ-vars appear in the
  order `zap` expects: cyclic κ's first, then acyclic κ's in
  `topoSortAcyclic` order. Uses `perm_exists` to discharge the
  resulting `Iff`.
-/

/-- Peel ∃-binders, opening each with a fresh fvar. CPS so fvars stay
    in scope while `k` runs. Returns `(name, type, fvar)` per binder. -/
partial def withPeeledExists (e : Expr)
    (acc : Array (Name × Expr × Expr))
    (k : Array (Name × Expr × Expr) → Expr → TacticM Unit) :
    TacticM Unit := do
  let e ← whnf e
  if e.isAppOfArity ``Exists 2 then
    let α    := e.getArg! 0
    let pred := e.getArg! 1
    if pred.isLambda then
      withLocalDeclD pred.bindingName! α fun fvar =>
        withPeeledExists (pred.bindingBody!.instantiate1 fvar)
          (acc.push (pred.bindingName!, α, fvar)) k
    else k acc e
  else k acc e

/-- Build `∃ x₀ : T₀, ∃ x₁ : T₁, …, body` by abstracting `fvar` out of
    `body` for each binder, innermost first. -/
def mkExistsChain (binders : Array (Name × Expr × Expr))
    (body : Expr) : MetaM Expr := do
  let mut result := body
  for i in (List.range binders.size).reverse do
    let (_, _, fvar) := binders[i]!
    let pred ← mkLambdaFVars #[fvar] result
    result ← mkAppM ``Exists #[pred]
  return result

/-- Nav a curried function type `T₁ → T₂ → … → Tₙ → Sort` and return
    the parameter types `[T₁, …, Tₙ]`. -/
partial def collectArrowTypes (ty : Expr) : MetaM (List Expr) := do
  let ty ← whnf ty
  if ty.isForall then
    let dom := ty.bindingDomain!
    let rest ← collectArrowTypes ty.bindingBody!
    return dom :: rest
  else return []

/-- `rewriteKs` — reorder the head ∃-chain so cyclic κ's come first,
    then acyclic κ's in topological-sort order (sinks first). -/
elab "rewriteKs" : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType
  withPeeledExists goalType #[] fun binders body => do
    if binders.size == 0 then
      throwError "rewriteKs: goal has no ∃-binders"

    -- Bridge to KM: temp mvar per binder, substitute fvar → mvar in body
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

    -- Classify κ's into acyclic + cyclic
    let kctxMap := kvars.foldl
      (fun acc k => acc.insert k.mvarId k) (∅ : Std.HashMap MVarId KVar)
    let kctx : KContext := { kvars := kctxMap }
    let (acyclic, cyclic) ← (exprPartitionKVars bodyWithMvars).run kctx

    -- Desired order: cyclic first, then acyclic (sinks first)
    let desired : List KVar := cyclic ++ acyclic
    let perm : Array Nat := desired.toArray.filterMap fun κ =>
      (List.range kvars.size).find? fun i => kvars[i]!.mvarId == κ.mvarId

    -- Identity check
    let isIdentity := perm.size == kvars.size &&
      (List.range kvars.size).all fun i => perm[i]? == some i
    if isIdentity then
      logInfo "rewriteKs: already in optimal order"
      return

    if perm.size != binders.size then
      throwError "rewriteKs: failed to map all κ's into binder positions \
        ({perm.size} of {binders.size})"

    -- Build new goal type with reordered binders, same body
    let newBinders := perm.map fun i => binders[i]!
    let newType ← mkExistsChain newBinders body

    -- Iff.mpr term-assignment + perm_exists discharge (Zap-style)
    -- NOTE: it is important to create the new-goal mvars in the Original goal's lctx
    -- not the extended one introduced using `withPeeledExists`'s `withLocalD`.
    -- Otherwise named fvars k0, k1, .... get captured the newGoal's localcontext
    -- and appear in the context after rewrite as leftovers.
    let (iffMVar, newGoalM) ← goal.withContext do
      let iffType  ← mkAppM ``Iff #[goalType, newType]
      let iffMVar'  ← mkFreshExprMVar (some iffType) (kind := .syntheticOpaque)
      let newGoalM' ← mkFreshExprMVar (some newType) (kind := .syntheticOpaque)
      pure (iffMVar', newGoalM')

    goal.assign (← mkAppM ``Iff.mpr #[iffMVar, newGoalM])
    setGoals [iffMVar.mvarId!, newGoalM.mvarId!]
    evalTactic (← `(tactic| perm_exists))
    setGoals [newGoalM.mvarId!]
