import Lean
import Flex.Core
import Flex.Zap.Utils
import Flex.Zap.Emit

open Lean Meta Elab

/-- Extract a contradiction using only the logical structure of a hypothesis. -/
private partial def falseFrom (type proof : Expr) : MetaM (Option Expr) := do
  let type := (← instantiateMVars type).consumeMData.headBeta
  if type.isConstOf ``False then return some proof
  if let some (left, right) := type.and? then
    if let some contradiction ← falseFrom left (← mkAppM ``And.left #[proof]) then
      return some contradiction
    return ← falseFrom right (← mkAppM ``And.right #[proof])
  if type.isAppOfArity ``Or 2 then
    let left := type.getArg! 0
    let right := type.getArg! 1
    let branch (type : Expr) := withLocalDeclD `h type fun h => do
      let some contradiction ← falseFrom type h | return none
      return some (← mkLambdaFVars #[h] contradiction)
    let some l ← branch left | return none
    let some r ← branch right | return none
    return some (← mkAppM ``Or.elim #[proof, l, r])
  if type.isAppOfArity ``Exists 2 then
    let domain := type.getArg! 0
    let predicate := type.appArg!
    return ← withLocalDeclD `x domain fun x =>
      withLocalDeclD `h (predicate.beta #[x]) fun h => do
        let some contradiction ← falseFrom (predicate.beta #[x]) h | return none
        let branch ← mkLambdaFVars #[x, h] contradiction
        return some (← mkAppM ``Exists.elim #[proof, branch])
  return none

/-- Discharge a pruned branch from the original guards, including outer guards. -/
private def contradiction? (target : Expr) : MetaM (Option Expr) := do
  for decl in ← getLCtx do
    if let some proof ← falseFrom decl.type decl.toExpr then
      return some (← mkFalseElim target proof)
  return none

/-- `Nav` (paper Fig. 12): build a proof of `lamBody`, a β-reduced solution
    `σ(t)` — an ∃-∧-∨ tree ending in an Eq-conjunction or `False` — by
    replaying the context collected on the way down: `binders` at ∃-nodes,
    `guards` at guard-`∧`s, `orPath` bits at ∨-nodes. -/
partial def nav
    (lamBody : Expr)
    (binders : List (Name × Expr × FVarId))
    (guards  : List (Name × Expr × FVarId))
    (orPath  : List Bool)
    (residualOut : IO.Ref (Array MVarId)) :
    MetaM Expr := do
  -- Or — consume one orPath bit, navigate
  if lamBody.isAppOfArity ``Or 2 then
    let l := lamBody.appFn!.appArg!
    let r := lamBody.appArg!
    match orPath with
    | [] =>
      throwError "nav: orPath exhausted at Or-node:{indentExpr lamBody}"
    | false :: restPath =>
      let inner ← nav l binders guards restPath residualOut
      return mkOrInl l r inner
    | true :: restPath =>
      let inner ← nav r binders guards restPath residualOut
      return mkOrInr l r inner
  -- Exists — consume one binder
  else if lamBody.isAppOfArity ``Exists 2 then
    let α := lamBody.appFn!.appArg!
    let pred := lamBody.appArg!
    match binders with
    | [] =>
      throwError "nav: no binders left at Exists-node:{indentExpr lamBody}"
    | (_, _, fvId) :: rest =>
      let witness := mkFVar fvId
      let nextBody := pred.beta #[witness]
      let inner ← nav nextBody rest guards orPath residualOut
      mkExistsIntro α pred witness inner
  -- And — distinguish guard-And from Eq-conjunction leaf via guards-emptiness.
  -- Sol1's structure puts all guards before the eq-leaf, so once guards is
  -- empty (and binders/orPath too), any remaining And is the eq-conjunction.
  else if let some (p, q) := lamBody.and? then
    match guards with
    | (_, type, fvId) :: rest =>
      let h := mkFVar fvId
      unless p == type || (← withNewMCtxDepth (isDefEq p type)) do
        throwError "zap: solution guard does not match its certificate hypothesis"
      let inner ← nav q binders rest orPath residualOut
      return mkAndIntro p q h inner
    | [] =>
      -- guards exhausted: this And is the eq-conjunction leaf
      buildEqProof lamBody residualOut
  -- Single Eq leaf (κ-arity = 1)
  else if lamBody.isAppOfArity ``Eq 3 then
    buildEqProof lamBody residualOut
  -- True leaf (κ-arity = 0)
  else if lamBody.isConstOf ``True then
    return mkConst ``True.intro
  -- False or unknown: residual
  else
    if let some proof ← contradiction? lamBody then return proof
    let m ← mkFreshExprMVar (some lamBody) (kind := .syntheticOpaque)
    residualOut.modify (·.push m.mvarId!)
    return m
