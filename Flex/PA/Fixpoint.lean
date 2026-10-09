import Lean

import Flex.Core
import Flex.PA.Qualifier
import Flex.PA.Instantiation
import Flex.PA.Weaken

open Lean Meta Elab Term Tactic

/-- Build the initial Houdini assignment: every cyclic κ maps to the union
    of every `@[qualif]`-tagged lambda instantiated over every type-compatible
    ordered slot-tuple of `κ.paramTypes`.

    For 4-arg `k0` with 4 tagged qualifiers, this produces on the order of
    4 + 12 + 12 + 12 = 40 candidates. -/
def buildInitialAssignment (cyclicKs : List KVar)
    : MetaM (List (KVar × List (Expr × List Nat))) := do
  let qs ← getQualifiers
  cyclicKs.mapM fun κ => do
    let mut cands : List (Expr × List Nat) := []
    for q in qs do
      let instantiations ← instantiateQualifier q κ.paramTypes
      cands := cands ++ instantiations.toList
    return (κ, cands)

/-- Iterate `weakenOnce` until the total candidate count across all κ's stops
    shrinking. Monotone: the total count is strictly decreasing per iteration
    until the fixpoint, so termination is guaranteed given finite candidates. -/
partial def solveFixpoint
    (kctx       : KContext)
    (flatCs     : List Expr)
    (assignment : List (KVar × List (Expr × List Nat)))
    : TermElabM (List (KVar × List (Expr × List Nat))) := do
  let next ← weakenOnce kctx flatCs assignment
  let beforeCount := assignment.foldl (fun acc (_, cs) => acc + cs.length) 0
  let afterCount  := next.foldl       (fun acc (_, cs) => acc + cs.length) 0
  if afterCount == beforeCount then
    return next
  else
    solveFixpoint kctx flatCs next

/-- Turn the final Houdini assignment into one `Expr` per κ, ready for witness
    synthesis. Per κ, β-apply every surviving candidate at κ's canonical fvar
    placeholders (`FVarId.mk "z0"`, …), then conjoin.

    Output shape matches what `solToWitnessExpr` in `Core/Elab.lean` expects. -/
def finalizeSolutions (assignment : List (KVar × List (Expr × List Nat)))
    : MetaM (List (KVar × Expr)) := do
  assignment.mapM fun (κ, cands) => do
    let paramFvars : Array Expr :=
      (κ.params.map fun n => Expr.fvar (FVarId.mk n)).toArray
    let bodies ← cands.mapM fun (q, slots) => do
      let chosen : Array Expr := (slots.map fun i => paramFvars[i]!).toArray
      Expr.instQualifier q chosen
    return (κ, conjoinExprs bodies)

/-- One-shot PA: from cyclic κ list + flat constraint + κ-context, run the full
    Houdini pipeline and return the final solution Expr per κ.

    Typical caller:  after fusion has eliminated acyclic κ's, hand the still-
    cyclic κ's and the residual flat clauses to this function. -/
def predicateAbstraction
    (kctx     : KContext)
    (cyclicKs : List KVar)
    (flatCs   : List Expr)
    : TermElabM (List (KVar × Expr)) := do
  let initial ← buildInitialAssignment cyclicKs
  let fixed   ← solveFixpoint kctx flatCs initial
  finalizeSolutions fixed
