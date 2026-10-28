import Lean

open Lean Meta

namespace Flex.Residual

private def reclose (caller : LocalContext) (goal : MVarId) : MetaM MVarId :=
  goal.withContext do
    let context ← getLCtx
    for declaration in caller do
      let some current := context.find? declaration.fvarId
        | throwError "flex: residual lost a caller-local declaration"
      unless (← instantiateMVars current.type) == (← instantiateMVars declaration.type) &&
          (← current.value?.mapM instantiateMVars) ==
            (← declaration.value?.mapM instantiateMVars) do
        throwError "flex: residual changed a caller-local declaration"
    let introduced := context.getFVarIds.filter (!caller.contains ·)
    let (reverted, closed) ← goal.revert introduced (preserveOrder := true)
    if reverted.any caller.contains then
      throwError "flex: residual depends on a changed caller context"
    let target ← instantiateMVars (← closed.getType)
    if target.hasMVar || target.hasLooseBVars ||
        (collectFVars {} target).fvarIds.any (!caller.contains ·) then
      throwError "flex: residual contains unresolved or out-of-scope variables"
    unless ← isProp target do
      throwError "flex: a residual obligation is not a proposition"
    return closed

private def assignProjection (goal : MVarId) (proof : Expr) : MetaM Unit :=
  goal.withContext do
    check proof
    unless ← isDefEq (← inferType proof) (← goal.getType) do
      throwError "flex: residual projection has the wrong type"
    unless ← goal.checkedAssign proof do
      throwError "flex: residual projection escapes its context"

private def bundleImpl (parent : MVarId) (goals : List MVarId) : MetaM (List MVarId) :=
  parent.withContext do
    let caller ← getLCtx
    let mut closed := #[]
    let mut seen : Std.HashSet MVarId := {}
    for goal in goals do
      if seen.contains goal || (← goal.isAssignedOrDelayedAssigned) then continue
      seen := seen.insert goal
      closed := closed.push (← reclose caller goal)
    if closed.isEmpty then return []
    if closed.size == 1 then return [closed[0]!]
    let types ← closed.toList.mapM fun goal => do instantiateMVars (← goal.getType)
    let target := mkAndN types
    let residual ← mkFreshExprMVar target (kind := .syntheticOpaque)
      (userName := (← parent.getTag))
    let mut proof := residual
    let mut remainingType := target
    for i in [:closed.size] do
      if i + 1 == closed.size then
        assignProjection closed[i]! proof
      else
        let some (left, right) := remainingType.and?
          | throwError "flex: malformed residual conjunction"
        assignProjection closed[i]! (mkApp3 (mkConst ``And.left) left right proof)
        proof := mkApp3 (mkConst ``And.right) left right proof
        remainingType := right
    return [residual.mvarId!]

/-- Reclose introduced binders and join remaining obligations in the caller's context.
    Failure restores the input goals; caller locals and obligation order are preserved. -/
def bundle (parent : MVarId) (goals : List MVarId) : MetaM (List MVarId) := do
  let saved ← Meta.saveState
  tryCatchRuntimeEx (bundleImpl parent goals) fun error => do
    saved.restore
    throw error

end Flex.Residual
