import Lean

import Flex.Core
import Flex.Fusion.Flatten

open Lean Meta

-- Dependencies for a single flat clause: (body κ, head κ) pairs.
partial def exprFlatDeps (e : Expr) : KM (List (KVar × KVar)) := do
  let (bodyKs, headKs) ← go e
  return bodyKs.flatMap fun kb => headKs.map fun kh => (kb, kh)
where
  go (e : Expr) : KM (List KVar × List KVar) := do
    let e ← whnf e
    if e.isForall then
      withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
        let domKs ← KM.exprKVars e.bindingDomain!
        let (bodyKs, headKs) ← go (e.bindingBody!.instantiate1 fvar)
        return (domKs ++ bodyKs, headKs)
    else
      return ([], ← KM.exprKVars e)

-- Dependencies for an `Expr`: flatten then compute deps on each piece.
def exprDeps (e : Expr) : KM (List (KVar × KVar)) := do
  let flats ← exprFlat e
  let deps ← flats.mapM exprFlatDeps
  return deps.flatten

/-- Collect κ-vars from an Expr in left-to-right depth-first order,
    matching the traversal order of `Constraint.kvars`. -/
partial def exprKVarsOrdered (e : Expr) : KM (List KVar) := do
  let e ← whnf e
  if let some (l, r) := e.and? then
    return (← exprKVarsOrdered l) ++ (← exprKVarsOrdered r)
  else if e.isForall then
    let dom := e.bindingDomain!
    let domKs ← KM.exprKVars dom
    withLocalDeclD e.bindingName! dom fun fvar => do
      let bodyKs ← exprKVarsOrdered (e.bindingBody!.instantiate1 fvar)
      return domKs ++ bodyKs
  else
    KM.exprKVars e

/-- Topologically sort the acyclic κ-vars so dependency sinks come first.
    If `(u, v) ∈ deps` (u in body where v in head), then u must be eliminated
    before v so v's sol doesn't leak a free reference to u. -/
partial def topoSortAcyclic (acyclic : List KVar) (deps : List (KVar × KVar)) :
    List KVar :=
  let rec go (remaining : List KVar) (acc : List KVar) : List KVar :=
    match remaining with
    | [] => acc.reverse
    | _ =>
      -- Pick κ with no predecessor in `remaining`: no `(κ', κ) ∈ deps`
      -- such that κ' is still in `remaining` and κ' ≠ κ.
      let ready? := remaining.find? fun κ =>
        !deps.any fun (u, v) => v == κ && u != κ && remaining.contains u
      match ready? with
      | some κ => go (remaining.filter (· != κ)) (κ :: acc)
      | none   => acc.reverse ++ remaining  -- cycle in "acyclic" (shouldn't happen)
  go acyclic []

-- IMPLEMENTATION OF SCC Algorithm

private structure TarjanState where
  nextIdx   : Nat       := 0
  stack     : List KVar := []
  onStack   : List KVar := []
  indexMap  : List (KVar × Nat) := []
  lowMap    : List (KVar × Nat) := []
  sccs      : List (List KVar)  := []

private def tsGetIdx (s : TarjanState) (k : KVar) : Option Nat :=
  (s.indexMap.find? fun (k', _) => k' == k).map (·.2)

private def tsGetLow (s : TarjanState) (k : KVar) : Nat :=
  ((s.lowMap.find? fun (k', _) => k' == k).map (·.2)).getD 0

private def tsSetLow (s : TarjanState) (k : KVar) (v : Nat) : TarjanState :=
  { s with lowMap := s.lowMap.map fun (k', n) =>
      if k' == k then (k', v) else (k', n) }

-- Pop stack until `k` is found (inclusive). Returns (scc, remainingStack)
private def tsPopUntil (stack : List KVar) (k : KVar) :
    List KVar × List KVar :=
  let rec go (rest : List KVar) (scc : List KVar) :=
    match rest with
    | []      => (scc, [])
    | x :: xs =>
        if x == k
        then (k :: scc, xs)
        else go xs (x :: scc)
  go stack []

private partial def strongConnect
    (k : KVar) (succs : KVar → List KVar)
    (s : TarjanState) : TarjanState :=
  let s := { s with
    indexMap  := (k, s.nextIdx) :: s.indexMap
    lowMap    := (k, s.nextIdx) :: s.lowMap
    nextIdx   := s.nextIdx + 1
    stack     := k :: s.stack
    onStack   := k :: s.onStack
    }
  let s := (succs k).foldl (fun s w =>
    match tsGetIdx s w with
    | none =>
      let s := strongConnect w succs s
      tsSetLow s k (min (tsGetLow s k) (tsGetLow s w))
    | some _ =>
      if s.onStack.contains w then
        let wIdx := (tsGetIdx s w).getD 0
        tsSetLow s k (min (tsGetLow s k) wIdx)
      else s
  ) s
  if tsGetLow s k == (tsGetIdx s k).getD 0 then
    let (scc, remaining) := tsPopUntil s.stack k
    { s with
      stack   := remaining
      onStack := s.onStack.filter fun x => !scc.contains x
      sccs    := scc :: s.sccs }
  else s

-- Tarjan's SCC, reverse topological order.
def tarjanSCC (nodes : List KVar) (edges : List (KVar × KVar)) :
    List (List KVar) :=
  let succs (k : KVar) : List KVar :=
    edges.filterMap fun (u, v) => if u == k then some v else none
  let s := nodes.foldl (fun s k =>
    if (tsGetIdx s k).isSome then s
    else strongConnect k succs s
  ) {}
  s.sccs

-- Does this κ have a self-loop?
def hasSelfLoop (k : KVar) (edges : List (KVar × KVar)) : Bool :=
  edges.any fun (u, v) => u == k && v == k

-- Iteratively remove high-degree nodes and recompute SCCs
-- until all SCCs are singletons without self-loops.
partial def cutVarsIterative (nodes : List KVar)
    (edges : List (KVar × KVar)) : List KVar :=
  let sccs := tarjanSCC nodes edges
  let cyclicSCC := sccs.find? fun scc =>
    scc.length > 1 || (scc.length == 1 && hasSelfLoop scc.head! edges)
  match cyclicSCC with
  | none     => []
  | some scc =>
    let pick := scc.foldl (fun best k =>
      let deg := edges.filter (fun (u, v) =>
        (u == k || v == k) && scc.contains u && scc.contains v) |>.length
      match best with
      | none => some (k, deg)
      | some (_, bd) => if deg > bd then some (k, deg) else best
    ) none |>.map (·.1) |>.getD scc.head!
    let remainingNodes := nodes.filter (· != pick)
    let remainingEdges := edges.filter fun (u, v) => u != pick && v != pick
    pick :: cutVarsIterative remainingNodes remainingEdges

-- Classify all κ-vars into (acyclicInTopoOrder, cyclic)
def classifyKVars (allKs : List KVar) (deps : List (KVar × KVar)) :
    List KVar × List KVar :=
  let khat := cutVarsIterative allKs deps
  let acyclic := allKs.filter fun k => !khat.contains k
  let acyclicDeps := deps.filter fun (u, v) =>
    acyclic.contains u && acyclic.contains v
  let acyclicSorted := topoSortAcyclic acyclic acyclicDeps
  (acyclicSorted, khat)
