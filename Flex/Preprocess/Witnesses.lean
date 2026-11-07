import Flex.Core
import Lean.Meta.Tactic.Replace
import Mathlib.Tactic.Simproc.ExistsAndEq

open Lean Meta

namespace Flex.Preprocess

private abbrev GuardCache := ExprStructMap (Expr × Expr)

-- Cache closed templates, so renamed clause binders share the same simplification.
private def compactGuard (input : Expr) (context : Simp.Context) (procs : Simp.SimprocsArray)
    : StateT GuardCache MetaM (Expr × Expr) := do
  let unchanged := (input, mkApp (mkConst ``Iff.refl) input)
  let nodes ← input.numObjs
  if nodes > 4096 then return unchanged
  unless (input.find? fun e => e.isAppOfArity ``Exists 2 &&
      (e.appArg!.find? fun node => node.isAppOfArity ``Eq 3 &&
        ((node.getArg! 1).isBVar || (node.getArg! 2).isBVar)).isSome).isSome do return unchanged
  let parameters := (collectFVars {} input).fvarIds.map mkFVar
  let key ← mkLambdaFVars parameters input
  if let some (result, proof) := (← get)[ExprStructEq.mk key]? then
    return (result.beta parameters, proof.beta parameters)
  let (result, _) ← Meta.simp input context procs
  let (output, proof) ← if result.expr == input || (← result.expr.numObjs) > nodes then
      pure unchanged
    else pure (result.expr, mkApp3 (mkConst ``Iff.of_eq) input result.expr (← result.getProof))
  let entry ← pure (← mkLambdaFVars parameters output, ← mkLambdaFVars parameters proof)
  modify (·.insert (ExprStructEq.mk key) entry)
  return (output, proof)

private partial def compactGuards (input : Expr) (context : Simp.Context) (procs : Simp.SimprocsArray)
    : StateT GuardCache MetaM (Expr × Expr) := do
  Core.checkSystem "witness compaction"
  let input := input.consumeMData.headBeta
  let unchanged := (input, mkApp (mkConst ``Iff.refl) input)
  if input.isAppOfArity ``Exists 2 then
    let domain := input.getArg! 0
    let predicate := input.getArg! 1
    return ← withLocalDeclD `witness domain fun parameter => do
      let original := predicate.beta #[parameter]
      let (body, proof) ← compactGuards original context procs
      if body == original then return unchanged
      let predicate' ← mkLambdaFVars #[parameter] body
      return (mkApp2 (mkConst ``Exists [← getLevel domain]) domain predicate',
        mkApp4 (mkConst ``exists_congr [← getLevel domain]) domain predicate predicate'
          (← mkLambdaFVars #[parameter] proof))
  if let some (left, right) := input.and? then
    let (left', lp) ← compactGuards left context procs
    let (right', rp) ← compactGuards right context procs
    if left == left' && right == right' then return unchanged
    return (mkApp2 (mkConst ``And) left' right',
      mkApp6 (mkConst ``and_congr) left left' right right' lp rp)
  if let .forallE name domain body bi := input then
    if (← isProp domain) && !body.hasLooseBVar 0 then
      let body := body.instantiate1 (mkConst ``True.intro)
      let (domain', dp) ← compactGuard domain context procs
      let (body', bp) ← compactGuards body context procs
      if domain == domain' && body == body' then return unchanged
      return (← mkArrow domain' body',
        mkApp6 (mkConst ``imp_congr) domain body domain' body' dp bp)
    return ← withLocalDecl name bi domain fun parameter => do
      let body := body.instantiate1 parameter
      let (result, proof) ← compactGuards body context procs
      if result == body then return unchanged
      return (← mkForallFVars #[parameter] result,
        mkApp4 (mkConst ``forall_congr' [← getLevel domain]) domain
          (← mkLambdaFVars #[parameter] body) (← mkLambdaFVars #[parameter] result)
          (← mkLambdaFVars #[parameter] proof))
  return (input, mkApp (mkConst ``Iff.refl) input)

private def compactGoalImpl (goal : MVarId) (kvars : List KVar) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let mut lemmas : SimpTheorems := {}
  for name in #[``eq_self, ``and_true, ``true_and, ``and_false, ``false_and,
      ``or_true, ``true_or, ``or_false, ``false_or, ``and_self, ``or_self,
      ``not_true_eq_false, ``not_false_eq_true, ``Classical.not_not, ``iff_self,
      ``true_implies, ``false_implies, ``imp_true_iff, ``exists_false] do
    lemmas ← lemmas.addConst name
  let context ← Simp.mkContext { maxSteps := 2000, decide := false } #[lemmas]
  -- Simplify inner witnesses first, before constructing proofs for outer existentials.
  let procs ← ({} : Simp.Simprocs).add ``ExistsAndEq.existsAndEq true
  let declarations ← kvars.toArray.mapM fun k => return (k.name, ← k.mvarId.getType)
  -- The simproc can work directly on parameters instead of abstracting κ-mvars at every node.
  let (result, proof) ← withNewMCtxDepth <| withLocalDeclsDND declarations fun symbols => do
    let replacements := (kvars.toArray.zip symbols).foldl
      (fun map (k, symbol) => map.insert k.mvarId symbol) ({} : Std.HashMap MVarId Expr)
    let input := target.replace fun e => if e.isMVar then replacements[e.mvarId!]? else none
    let ((result, proof), _) ← (compactGuards input context #[procs]).run {}
    let mvars := kvars.toArray.map fun k => mkMVar k.mvarId
    return (result.replaceFVars symbols mvars, proof.replaceFVars symbols mvars)
  if result == target then return goal
  goal.replaceTargetEq result (mkApp3 (mkConst ``propext) target result proof)

/-- Optional witness compaction: bounded work, no guard expansion or growth.
A failed pass leaves the goal unchanged. -/
def compactGoal (goal : MVarId) (kvars : List KVar) : MetaM MVarId := do
  let saved ← saveState
  let budget ← if (← getMaxHeartbeats) == 0 then pure 1000000 else
    pure (min 1000000 (← getRemainingHeartbeats))
  if budget == 0 then return goal
  -- Exhausting the budget raises a runtime exception, which plain `try`/`catch` would not
  -- catch; it would escape and fail the enclosing pass, discarding earlier cleanup.
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget }) <|
      Core.withCurrHeartbeats (compactGoalImpl goal kvars))
    fun error => do
      saved.restore
      if error.isInterrupt then throw error
      Core.checkInterrupted
      return goal

end Flex.Preprocess
