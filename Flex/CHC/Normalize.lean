import Flex.CHC.Export
import Lean.Meta.Tactic.Replace

namespace Flex.CHC

open Lean Meta

private def bounded (count limit : Nat) : MetaM Nat := do
  if count > limit then
    throwError "CHC normalization: expanded constraints exceed the clause limit ({limit})"
  return count

private structure GuardInfo where
  branches : Nat := 1
  hasRelation : Bool := false
  expand : Bool := false

/-- Theory formulas stay compact. Only predicate disjunctions and existential guards expand. -/
private partial def guardInfo (relations : Std.HashSet MVarId) (input : Expr)
    (limit : Nat) : MetaM GuardInfo := withIncRecDepth do
  let input ← Prepare.expose input
  if let some (left, right) := input.and? then
    let left ← guardInfo relations left limit
    let right ← guardInfo relations right limit
    return {
      branches := ← bounded (left.branches * right.branches) limit
      hasRelation := left.hasRelation || right.hasRelation
      expand := left.expand || right.expand }
  if let some (left, right) := input.or? then
    let left ← guardInfo relations left limit
    let right ← guardInfo relations right limit
    let hasRelation := left.hasRelation || right.hasRelation
    let expand := hasRelation || left.expand || right.expand
    let branches ← if expand then bounded (left.branches + right.branches) limit else pure 1
    return { branches, hasRelation, expand }
  if input.isAppOfArity ``Exists 2 then
    return ← withLocalDeclD `witness (input.getArg! 0) fun witness => do
      let info ← guardInfo relations ((input.getArg! 1).beta #[witness]) limit
      return { info with expand := true }
  return { hasRelation := (input.find? fun e =>
    e.isMVar && relations.contains e.mvarId!).isSome }

/-- Count exactly the clauses that selective guard expansion will produce. -/
private partial def expandedClauses (relations : Std.HashSet MVarId) (input : Expr)
    (limit : Nat) : MetaM (Nat × Bool) := withIncRecDepth do
  let input ← Prepare.expose input
  if input.isConstOf ``True then return (0, false)
  if let some (left, right) := input.and? then
    let (leftCount, leftChanged) ← expandedClauses relations left limit
    let (rightCount, rightChanged) ← expandedClauses relations right limit
    return (← bounded (leftCount + rightCount) limit, leftChanged || rightChanged)
  if let .forallE name domain body bi := input then
    return ← withLocalDecl name bi domain fun parameter => do
      let (count, changed) ← expandedClauses relations (body.instantiate1 parameter) limit
      if count != 0 && (← isProp domain) && !body.hasLooseBVar 0 then
        let info ← guardInfo relations domain limit
        return (← bounded (info.branches * count) limit, changed || info.expand)
      return (count, changed)
  return (← bounded 1 limit, false)

/-- Rewrite one guard using a logical equivalence, without descending into theory terms. -/
private def guardEquivalence (guard conclusion : Expr) : MetaM Expr := do
  let guard ← Prepare.expose guard
  if let some (left, right) := guard.and? then
    return mkApp3 (mkConst ``and_imp) left right conclusion
  if let some (left, right) := guard.or? then
    return mkApp3 (mkConst ``or_imp) left right conclusion
  if guard.isAppOfArity ``Exists 2 then
    return ← mkAppOptM ``exists_imp #[some (guard.getArg! 0), some (guard.getArg! 1), some conclusion]
  throwError "CHC normalization: expected a conjunction, disjunction, or existential guard"

/-- Traverse positive constraint positions, carrying an equivalence to the original. -/
private partial def normalize (relations : Std.HashSet MVarId) (input : Expr)
    (limit : Nat) : MetaM (Expr × Expr) := withIncRecDepth do
  let input ← Prepare.expose input
  if let some (left, right) := input.and? then
    let (left', leftProof) ← normalize relations left limit
    let (right', rightProof) ← normalize relations right limit
    return (mkApp2 (mkConst ``And) left' right',
      ← mkAppM ``and_congr #[leftProof, rightProof])
  if let .forallE name domain body bi := input then
    return ← withLocalDecl name bi domain fun parameter => do
      if (← isProp domain) && !body.hasLooseBVar 0 then
        let (count, _) ← expandedClauses relations (body.instantiate1 parameter) limit
        if count == 0 then return (input, ← mkAppM ``Iff.refl #[input])
        if (← guardInfo relations domain limit).expand then
          let proof ← guardEquivalence domain (body.instantiate1 parameter)
          let some (_, expanded) := (← inferType proof).iff?
            | throwError "CHC normalization: expected a guard equivalence"
          let (result, rest) ← normalize relations expanded limit
          return (result, ← mkAppM ``Iff.trans #[proof, rest])
      let (result, proof) ← normalize relations (body.instantiate1 parameter) limit
      return (← mkForallFVars #[parameter] result,
        ← mkAppM ``forall_congr' #[← mkLambdaFVars #[parameter] proof])
  return (input, ← mkAppM ``Iff.refl #[input])

/-- Normalize only guards that export cannot retain. Failures restore the original goal. -/
def normalizeGoal (bodyGoal : MVarId) (kvars : List KVar) (maxClauses : Nat := 1024)
    : MetaM MVarId := do
  let saved ← Meta.saveState
  let committed ← IO.mkRef false
  try
    let normalized ← bodyGoal.withContext do
      if maxClauses == 0 then throwError "CHC normalization: maxClauses must be positive"
      bodyGoal.checkNotAssigned `chc_normalize
      let target ← instantiateMVars (← bodyGoal.getType)
      unless ← isProp target do throwError "CHC normalization: expected a proposition"
      let relations := kvars.foldl (fun ids k => ids.insert k.mvarId) ({} : Std.HashSet MVarId)
      let (count, changed) ← expandedClauses relations target maxClauses
      unless changed do return bodyGoal
      let (target', proof) ← normalize relations target maxClauses
      let (actual, changed) ← expandedClauses relations target' maxClauses
      unless actual == count && !changed do
        throwError "CHC normalization: clause count or guard shape disagrees with preflight"
      bodyGoal.replaceTargetEq target' (← mkAppM ``propext #[proof])
    committed.set true
    return normalized
  finally
    unless ← committed.get do restoreMetaState saved

end Flex.CHC
