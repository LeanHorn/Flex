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

private structure PAClause where
  expression : Expr
  head : KVar
  deriving Inhabited

/-- Dependencies include premise types and head argument terms, but exclude the
    replaced head symbol. Self-dependencies must be revisited after weakening. -/
private def clauseDependencies (kctx : KContext) (clause : Expr) : MetaM (List KVar) := do
  forallTelescopeReducing clause (whnfType := true) fun binders head => do
    let mut dependencies : List KVar := []
    for binder in binders do
      dependencies := dependencies ++ (← (KM.exprKVars (← inferType binder)).run kctx)
    for arg in head.getAppArgs do
      dependencies := dependencies ++ (← (KM.exprKVars arg).run kctx)
    return dependencies.eraseDups

/-- Weaken only clauses whose premises changed. A reported round is one wave
    of pending clauses; the queue is empty exactly when no affected checks remain. -/
partial def solveFixpoint
    (kctx : KContext) (flatCs : List Expr)
    (assignment : List (KVar × List (Expr × List Nat)))
    (oracle : PAOracle := proveLeaf)
    (observe : PAObserver := fun _ => pure ())
    (synthOracle : Option PASynthOracle := none)
    : TermElabM (List (KVar × List (Expr × List Nat))) := do
  let mut contextDeps : List KVar := []
  for decl in ← getLCtx do
    contextDeps := contextDeps ++ (← (KM.exprKVars decl.type).run kctx)
    if let some value := decl.value? then
      contextDeps := contextDeps ++ (← (KM.exprKVars value).run kctx)
  contextDeps := contextDeps.eraseDups
  let mut clauses : Array PAClause := #[]
  let mut dependents : Std.HashMap MVarId (Array Nat) := {}
  for expression in flatCs do
    let some head ← (findHeadKVar expression).run kctx | continue
    unless assignment.any (·.1 == head) do continue
    let index := clauses.size
    clauses := clauses.push { expression, head }
    for κ in ((← clauseDependencies kctx expression) ++ contextDeps).eraseDups do
      dependents := dependents.insert κ.mvarId ((dependents[κ.mvarId]?.getD #[]).push index)
  let mut out := assignment
  let mut solutions ← finalizeSolutions out
  let mut count := out.foldl (fun n (_, qs) => n + qs.length) 0
  let mut pending := Array.range clauses.size
  let mut queued : Std.HashSet Nat := pending.foldl (·.insert ·) {}
  while !pending.isEmpty do
    let before := count
    observe (.roundStarted before)
    let mut next : Array Nat := #[]
    for index in pending do
      queued := queued.erase index
      let clause := clauses[index]!
      let some (_, candidates) := out.find? (·.1 == clause.head) | continue
      let kept ← weakenClause kctx clause.expression clause.head candidates solutions oracle synthOracle
      if kept.length < candidates.length then
        count := count - (candidates.length - kept.length)
        out := out.map fun (κ, qs) => if κ == clause.head then (κ, kept) else (κ, qs)
        let sol ← candidateSolution clause.head kept
        solutions := solutions.map fun (κ, body) =>
          if κ == clause.head then (κ, sol) else (κ, body)
        for dependent in dependents[clause.head.mvarId]?.getD #[] do
          unless queued.contains dependent do
            queued := queued.insert dependent
            next := next.push dependent
    observe (.roundFinished before count)
    pending := next
  observe (.converged count)
  return out

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
