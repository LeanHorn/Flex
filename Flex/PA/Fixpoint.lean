import Lean

import Flex.Core
import Flex.PA.Qualifier
import Flex.PA.Instantiation
import Flex.PA.Weaken

open Lean Meta Elab Term Tactic

inductive PAProgress where
  | setup (scraped standard tagged : Nat) (candidates : Array (Name × Nat))
  | roundStarted (candidates : Nat)
  | roundFinished (before after : Nat)
  | converged (candidates : Nat)

abbrev PAObserver := PAProgress → TermElabM Unit

private structure InitialCandidates where
  entries : Array (Expr × List Nat) := #[]
  seen : ExprSet := {}
  instances : Nat := 0
  truncated : Bool := false
  instancesTruncated : Bool := false

/-- Instantiate tagged qualifiers, then the supplied extras, deduplicating predicates.
    Per-κ limits bound unique candidates and visited slot assignments. -/
def buildInitialAssignment (cyclicKs : List KVar) (extraQualifiers : Array Expr := #[])
    (maxCandidates : Option Nat := none)
    (maxInstances : Option Nat := none)
    : MetaM (List (KVar × List (Expr × List Nat))) := do
  let qs := (← getQualifiers) ++ extraQualifiers
  cyclicKs.mapM fun κ => do
    let params := (κ.params.map fun n => Expr.fvar (FVarId.mk n)).toArray
    let mut state : InitialCandidates := {}
    for q in qs do
      state ← foldQualifierInstances q κ.paramTypes state fun state slots => do
        if maxInstances.any (state.instances >= ·) then
          return ({ state with instancesTruncated := true }, false)
        let state := { state with instances := state.instances + 1 }
        let args := (slots.map fun i => params[i]!).toArray
        let body ← Expr.instQualifier q args
        if state.seen.contains body then return (state, true)
        if maxCandidates.any (state.entries.size >= ·) then
          return ({ state with truncated := true }, false)
        return ({ state with
          entries := state.entries.push (q, slots)
          seen := state.seen.insert body }, true)
      if state.truncated || state.instancesTruncated then break
    if state.truncated then
      logWarning m!"fix: candidate limit ({state.entries.size}) reached for {κ.name}; additional candidates omitted"
    if state.instancesTruncated then
      logWarning m!"fix: instance limit ({state.instances}) reached for {κ.name}; further slot assignments omitted"
    return (κ, state.entries.toList)

/-- Iterate `weakenOnce` until the total candidate count across all κ's stops
    shrinking. Monotone: the total count is strictly decreasing per iteration
    until the fixpoint, so termination is guaranteed given finite candidates. -/
partial def solveFixpoint
    (kctx       : KContext)
    (flatCs     : List Expr)
    (assignment : List (KVar × List (Expr × List Nat)))
    (oracle : PAOracle := proveLeaf)
    (observe : PAObserver := fun _ => pure ())
    : TermElabM (List (KVar × List (Expr × List Nat))) := do
  let beforeCount := assignment.foldl (fun acc (_, cs) => acc + cs.length) 0
  observe (.roundStarted beforeCount)
  let next ← weakenOnce kctx flatCs assignment oracle
  let afterCount  := next.foldl       (fun acc (_, cs) => acc + cs.length) 0
  observe (.roundFinished beforeCount afterCount)
  if afterCount == beforeCount then
    observe (.converged afterCount)
    return next
  else
    solveFixpoint kctx flatCs next oracle observe

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
