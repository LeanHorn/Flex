import Lean

import Flex.Core
import Flex.PA.Qualifier
import Flex.PA.Check

open Lean Meta Elab Term Tactic

-- Simply, take [e₁, ... , eₙ] where eᵢ
-- and turn it into (e₁ ∧ ...) ∧ eₙ
def conjoinExprs : List Expr → Expr
  | []  => mkConst ``True
  | [e] => e
  | e :: es => es.foldl (fun acc x => mkApp2 (mkConst ``And) acc x) e

/-- Substitute nested predicate arguments before replacing the enclosing application. -/
private partial def substituteCandidates (assignment : List (KVar × Expr)) (e : Expr) : Expr :=
  e.replace fun term =>
    if !term.getAppFn.isMVar then none else
      match assignment.find? (fun (κ, _) => κ.mvarId == term.getAppFn.mvarId!) with
      | none => none
      | some (κ, solution) =>
        let args := term.getAppArgs.map (substituteCandidates assignment)
        some (substKVarInExpr κ solution (mkAppN term.getAppFn args))

/-- Substitute current predicates in premises and replace the selected head. -/
partial def specializeClauseWithHead
    (headKVar   : KVar)
    (headRepl   : Array Expr → KM Expr)
    (assignment : List (KVar × Expr))
    (e          : Expr) : KM Expr := do
  let e ← whnf e
  if e.isForall then
    let dom := substituteCandidates assignment e.bindingDomain!
    withLocalDeclD e.bindingName! dom fun fvar => do
      let body  := e.bindingBody!.instantiate1 fvar
      let body' ← specializeClauseWithHead headKVar headRepl assignment body
      let abstr := body'.abstract #[fvar]
      pure (Expr.forallE e.bindingName! dom abstr e.bindingInfo!)
  else if let some (l, r) := e.and? then
    let l' ← specializeClauseWithHead headKVar headRepl assignment l
    let r' ← specializeClauseWithHead headKVar headRepl assignment r
    return mkApp2 (mkConst ``And) l' r'
  else
    let fn := e.getAppFn
    if fn.isMVar && fn.mvarId! == headKVar.mvarId then
      headRepl (e.getAppArgs.map (substituteCandidates assignment))
    else
      return substituteCandidates assignment e

/-- Replace the head with one candidate instance. -/
def specializeClauseForHead
    (headKVar   : KVar)
    (q          : Expr)
    (qSlots     : List Nat)
    (assignment : List (KVar × Expr))
    (e          : Expr) : KM Expr :=
  specializeClauseWithHead headKVar
    (fun args => liftM (Expr.instQualifier q ((qSlots.map fun i => args[i]!).toArray)))
    assignment e

/-- Replace the head with `False` to test whether the premises are inconsistent. -/
def specializeClauseAsNeg
    (headKVar   : KVar)
    (assignment : List (KVar × Expr))
    (e          : Expr) : KM Expr :=
  specializeClauseWithHead headKVar (fun _ => pure (mkConst ``False)) assignment e

/-- Conjoin a predicate's candidates at its canonical parameters. -/
def candidateSolution (κ : KVar) (candidates : List (Expr × List Nat)) : MetaM Expr := do
  let params := (κ.params.map fun n => Expr.fvar (FVarId.mk n)).toArray
  let bodies ← candidates.mapM fun (q, slots) =>
    Expr.instQualifier q ((slots.map fun i => params[i]!).toArray)
  return conjoinExprs bodies

/-- Build predicate bodies for substitution and witness construction. -/
def finalizeSolutions (assignment : List (KVar × List (Expr × List Nat)))
    : MetaM (List (KVar × Expr)) :=
  assignment.mapM fun (κ, candidates) => return (κ, ← candidateSolution κ candidates)

/-- Check one clause against a fixed assignment. Unknown checks drop candidates;
    the resulting assignment still requires independent proof certification. -/
def weakenClause
    (kctx : KContext) (clause : Expr) (head : KVar)
    (candidates : List (Expr × List Nat)) (solutions : List (KVar × Expr))
    (oracle : PAOracle := proveLeaf) (synthOracle : Option PASynthOracle := none)
    : TermElabM (List (Expr × List Nat)) := do
  if candidates.isEmpty then return []
  match synthOracle with
  | none =>
    if ← checkExprUnsat (← (specializeClauseAsNeg head solutions clause).run kctx) oracle then
      return candidates
    candidates.filterM fun (q, slots) => do
      let vc ← (specializeClauseForHead head q slots solutions clause).run kctx
      checkExprVC vc oracle
  | some synth =>
    -- Specialize the premises once and open them as local hypotheses, which the
    -- oracle asserts once; the checks differ only in the head.
    let opened ← (specializeClauseWithHead head (pure <| mkAppN (.mvar head.mvarId) ·)
      solutions clause).run kctx
    let results ← forallTelescope opened fun _ conclusion => do
      let guard ← (specializeClauseAsNeg head solutions conclusion).run kctx
      let vcs ← candidates.toArray.mapM fun (q, slots) =>
        (specializeClauseForHead head q slots solutions conclusion).run kctx
      synth (#[guard] ++ vcs)
    unless results.size == candidates.length + 1 do
      throwError "PA synthesis oracle returned {results.size} results for {candidates.length + 1} queries"
    -- A proved inconsistent premise validates every candidate, even if an
    -- individual query times out or is unsupported by the backend.
    if let .valid := results[0]! then return candidates
    return (candidates.zip results.toList.tail!).filterMap fun (candidate, result) =>
      match result with
      | .valid => some candidate
      | .invalid | .unknown _ => none

/-- A full scan of all head clauses, retained as the reference Houdini step. -/
def weakenOnce
    (kctx : KContext) (flatCs : List Expr)
    (assignment : List (KVar × List (Expr × List Nat)))
    (oracle : PAOracle := proveLeaf) (synthOracle : Option PASynthOracle := none)
    : TermElabM (List (KVar × List (Expr × List Nat))) := do
  let mut out := assignment
  let mut solutions ← finalizeSolutions out
  for clause in flatCs do
    let some head ← (findHeadKVar clause).run kctx | continue
    let some (_, candidates) := out.find? (·.1 == head) | continue
    let kept ← weakenClause kctx clause head candidates solutions oracle synthOracle
    if kept.length < candidates.length then
      out := out.map fun (κ, qs) => if κ == head then (κ, kept) else (κ, qs)
      let sol ← candidateSolution head kept
      solutions := solutions.map fun (κ, body) => if κ == head then (κ, sol) else (κ, body)
  return out
