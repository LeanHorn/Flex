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

/-- Generic clause specializer.
    Walks the ∀-chain, substitutes hypothesis κ-apps via `assignment`, and
    at the head leaf calls `headRepl` with the κ-app's args to produce the
    replacement. Used by both candidate-VC build and sat-VC build. -/
partial def specializeClauseWithHead
    (headKVar   : KVar)
    (headRepl   : Array Expr → KM Expr)
    (assignment : List (KVar × Expr))
    (e          : Expr) : KM Expr := do
  let e ← whnf e
  if e.isForall then
    let mut dom := e.bindingDomain!
    for (κ, sol) in assignment do
      dom := substKVarInExpr κ sol dom
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
      headRepl e.getAppArgs
    else
      let mut acc := e
      for (κ, sol) in assignment do
        acc := substKVarInExpr κ sol acc
      return acc

/-- Specialize for a candidate qualifier (existing behavior). -/
def specializeClauseForHead
    (headKVar   : KVar)
    (q          : Expr)            -- qualifier lambda (unapplied, e.g. `q_le`)
    (qSlots     : List Nat)        -- slot mapping: qualifier-param i → κ-slot qSlots[i]
    (assignment : List (KVar × Expr))
    (e          : Expr) : KM Expr :=
  specializeClauseWithHead headKVar
    (fun args => liftM (Expr.instQualifier q ((qSlots.map fun i => args[i]!).toArray)))
    assignment e

/-- Specialize but write `False` at the head κ-leaf — used by the sat-guard
    to test whether the clause's hypothesis is itself unsatisfiable. -/
def specializeClauseAsNeg
    (headKVar   : KVar)
    (assignment : List (KVar × Expr))
    (e          : Expr) : KM Expr :=
  specializeClauseWithHead headKVar (fun _ => pure (mkConst ``False)) assignment e

/-- Build a per-κ "current solution" map: each κ's surviving candidate
    qualifier-instances β-applied at canonical-param fvars, then conjoined.
    `substKVarInExpr` later re-substitutes those placeholders with actual
    κ-app args at each hypothesis site. -/
private def buildCurrentSols
    (assignment : List (KVar × List (Expr × List Nat)))
    : MetaM (List (KVar × Expr)) :=
  assignment.mapM fun (κ, cands) => do
    let paramFvars : Array Expr :=
      (κ.params.map fun n => Expr.fvar (FVarId.mk n)).toArray
    let bodies ← cands.mapM fun (q, slots) => do
      let chosen : Array Expr := (slots.map fun i => paramFvars[i]!).toArray
      Expr.instQualifier q chosen
    return (κ, conjoinExprs bodies)

/-- One iteration of Houdini weakening.

    For each flat clause whose conclusion is a κ-application:
    · Identify the head κ.
    · Sat-guard (A1): if hypothesis (with current sols substituted) is
      inconsistent, every candidate would pass via vacuous truth — SKIP
      this clause this iter (don't drop candidates; dropping would be
      unsound). Other clauses processed in this iter usually shrink `out`
      enough that the inconsistency disappears next pass.
    · Otherwise, for each candidate `(q, qSlots)`, specialize and check
      via `checkExprVC`. Keep candidate iff it passes.

    A2: `currentSols` is rebuilt INSIDE the per-clause loop so each clause
    sees the latest `out` (post earlier-clause refinements within this iter). -/
partial def weakenOnce
    (kctx       : KContext)
    (flatCs     : List Expr)
    (assignment : List (KVar × List (Expr × List Nat)))
    (oracle : PAOracle := proveLeaf)
    : TermElabM (List (KVar × List (Expr × List Nat))) := do
  -- A2: `currentSols` is rebuilt INSIDE the per-clause loop so each clause
  -- sees the latest `out` (post earlier-clause refinements within this iter).
  -- Matches liquid-fixpoint's worklist behavior more closely.
  let mut out := assignment
  for fc in flatCs do
    let some headKVar ← (findHeadKVar fc).run kctx | continue
    let some (_, candidates) := out.find? (·.1 == headKVar) | continue
    let currentSols ← buildCurrentSols out
    -- A1: sat-guard. If hypothesis is unsat (with current sols substituted),
    -- every candidate would pass via vacuous truth. SKIP this clause —
    -- don't touch `out`. Other clauses processed in this iter shrink `out`,
    -- usually breaking the inconsistency on the next pass.
    let negVC ← (specializeClauseAsNeg headKVar currentSols fc).run kctx
    let vacuous ← checkExprUnsat negVC oracle
    match vacuous with
    | true  => pure ()
    | false =>
      let mut kept : List (Expr × List Nat) := []
      for (q, slots) in candidates do
        let vc ← (specializeClauseForHead headKVar q slots currentSols fc).run kctx
        if ← checkExprVC vc oracle then
          kept := kept.concat (q, slots)
      out := out.map fun (κ, qs) =>
        if κ == headKVar then (κ, kept) else (κ, qs)
  return out
