import Flex.CHC.Export
import Lean.Meta.Tactic.Replace
import Mathlib.Tactic.Simproc.ExistsAndEq

namespace Flex.CHC

open Lean Meta

private abbrev GuardCache := ExprStructMap (Expr × Expr)

-- Cache closed templates, so renamed clause binders share the same simplification.
private def compactGuard (input : Expr) (context : Simp.Context) (procs : Simp.SimprocsArray)
    : StateT GuardCache MetaM (Expr × Expr) := do
  unless (input.find? (·.isAppOfArity ``Exists 2)).isSome do
    return (input, mkApp (mkConst ``Iff.refl) input)
  let parameters := (collectFVars {} input).fvarIds.map mkFVar
  let key ← mkLambdaFVars parameters input
  if let some (result, proof) := (← get)[ExprStructEq.mk key]? then
    return (result.beta parameters, proof.beta parameters)
  let (result, _) ← Meta.simp input context procs
  let proof := mkApp3 (mkConst ``Iff.of_eq) input result.expr (← result.getProof)
  let entry ← pure (← mkLambdaFVars parameters result.expr, ← mkLambdaFVars parameters proof)
  modify (·.insert (ExprStructEq.mk key) entry)
  return (result.expr, proof)

private partial def compactGuards (input : Expr) (context : Simp.Context) (procs : Simp.SimprocsArray)
    : StateT GuardCache MetaM (Expr × Expr) := do
  let input ← Prepare.expose input
  if input.isAppOfArity ``Exists 2 then
    let domain := input.getArg! 0
    let predicate := input.getArg! 1
    return ← withLocalDeclD `witness domain fun parameter => do
      let (body, proof) ← compactGuards (predicate.beta #[parameter]) context procs
      let predicate' ← mkLambdaFVars #[parameter] body
      return (mkApp2 (mkConst ``Exists [← getLevel domain]) domain predicate',
        mkApp4 (mkConst ``exists_congr [← getLevel domain]) domain predicate predicate'
          (← mkLambdaFVars #[parameter] proof))
  if let some (left, right) := input.and? then
    let (left', lp) ← compactGuards left context procs
    let (right', rp) ← compactGuards right context procs
    return (mkApp2 (mkConst ``And) left' right',
      mkApp6 (mkConst ``and_congr) left left' right right' lp rp)
  if let .forallE name domain body bi := input then
    if (← isProp domain) && !body.hasLooseBVar 0 then
      let body := body.instantiate1 (mkConst ``True.intro)
      let (domain', dp) ← compactGuard domain context procs
      let (body', bp) ← compactGuards body context procs
      return (← mkArrow domain' body',
        mkApp6 (mkConst ``imp_congr) domain body domain' body' dp bp)
    return ← withLocalDecl name bi domain fun parameter => do
      let body := body.instantiate1 parameter
      let (result, proof) ← compactGuards body context procs
      return (← mkForallFVars #[parameter] result,
        mkApp4 (mkConst ``forall_congr' [← getLevel domain]) domain
          (← mkLambdaFVars #[parameter] body) (← mkLambdaFVars #[parameter] result)
          (← mkLambdaFVars #[parameter] proof))
  return (input, mkApp (mkConst ``Iff.refl) input)

/-- Eliminate equality-bound witnesses before expanding guards, preserving the clause structure. -/
def compactGoal (goal : MVarId) (kvars : List KVar) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let mut lemmas : SimpTheorems := {}
  for name in #[``eq_self, ``and_true, ``true_and, ``and_false, ``false_and,
      ``or_true, ``true_or, ``or_false, ``false_or, ``and_self, ``or_self,
      ``not_true_eq_false, ``not_false_eq_true, ``Classical.not_not, ``iff_self,
      ``true_implies, ``false_implies, ``imp_true_iff, ``exists_false] do
    lemmas ← lemmas.addConst name
  let context ← Simp.mkContext { maxSteps := 1000000, decide := false } #[lemmas]
  -- Simplify inner witnesses first, before constructing proofs for outer existentials.
  let procs ← ({} : Simp.Simprocs).add ``ExistsAndEq.existsAndEq true
  let declarations ← kvars.toArray.mapM fun k => return (k.name, ← k.mvarId.getType)
  -- The simproc can work directly on parameters instead of abstracting κ-mvars at every node.
  let (result, proof) ← withLocalDeclsDND declarations fun symbols => do
    let replacements := (kvars.toArray.zip symbols).foldl
      (fun map (k, symbol) => map.insert k.mvarId symbol) ({} : Std.HashMap MVarId Expr)
    let input := target.replace fun e => if e.isMVar then replacements[e.mvarId!]? else none
    let ((result, proof), _) ← (compactGuards input context #[procs]).run {}
    let mvars := kvars.toArray.map fun k => mkMVar k.mvarId
    return (result.replaceFVars symbols mvars, proof.replaceFVars symbols mvars)
  if result == target then return goal
  goal.replaceTargetEq result (mkApp3 (mkConst ``propext) target result proof)

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
private def guardEquivalence (guard conclusion : Expr) : MetaM (Expr × Expr) := do
  let guard ← Prepare.expose guard
  if let some (left, right) := guard.and? then
    return (← mkArrow left (← mkArrow right conclusion),
      mkApp3 (mkConst ``and_imp) left right conclusion)
  if let some (left, right) := guard.or? then
    return (mkApp2 (mkConst ``And) (← mkArrow left conclusion) (← mkArrow right conclusion),
      mkApp3 (mkConst ``or_imp) left right conclusion)
  if guard.isAppOfArity ``Exists 2 then
    let domain := guard.getArg! 0
    let predicate := guard.getArg! 1
    withLocalDeclD `witness domain fun witness => do
      return (← mkForallFVars #[witness] (← mkArrow (predicate.beta #[witness]) conclusion),
        mkApp3 (mkConst ``exists_imp [← getLevel domain]) domain predicate conclusion)
  else
    throwError "CHC normalization: expected a conjunction, disjunction, or existential guard"

/-- Traverse positive constraint positions, carrying an equivalence to the original. -/
private partial def normalize (relations : Std.HashSet MVarId) (input : Expr)
    (limit : Nat) : MetaM (Expr × Expr) := withIncRecDepth do
  let input ← Prepare.expose input
  if let some (left, right) := input.and? then
    let (left', leftProof) ← normalize relations left limit
    let (right', rightProof) ← normalize relations right limit
    return (mkApp2 (mkConst ``And) left' right',
      mkApp6 (mkConst ``and_congr) left left' right right' leftProof rightProof)
  if let .forallE name domain body bi := input then
    return ← withLocalDecl name bi domain fun parameter => do
      let dependent := body.hasLooseBVar 0
      let body := body.instantiate1 parameter
      if (← isProp domain) && !dependent then
        if (← guardInfo relations domain limit).expand then
          let (expanded, proof) ← guardEquivalence domain body
          let (result, rest) ← normalize relations expanded limit
          return (result, mkApp5 (mkConst ``Iff.trans) input expanded result proof rest)
      let (result, proof) ← normalize relations body limit
      return (← mkForallFVars #[parameter] result,
        mkApp4 (mkConst ``forall_congr' [← getLevel domain]) domain
          (← mkLambdaFVars #[parameter] body) (← mkLambdaFVars #[parameter] result)
          (← mkLambdaFVars #[parameter] proof))
  return (input, mkApp (mkConst ``Iff.refl) input)

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
      bodyGoal.replaceTargetEq target' (mkApp3 (mkConst ``propext) target target' proof)
    committed.set true
    return normalized
  finally
    unless ← committed.get do restoreMetaState saved

end Flex.CHC
