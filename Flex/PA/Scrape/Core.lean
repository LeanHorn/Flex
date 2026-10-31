import Flex.PA.Scrape.Config

/-! Shared scope checks, candidate abstraction, deduplication, and budgets. -/

open Lean Meta

namespace PAScrape.Internal

/-- Local constants are allowed; metavariables and loose bound variables are not. -/
def isResolved (e : Expr) : Bool := !e.hasMVar && !e.hasLooseBVars

def support (e : Expr) : Array FVarId :=
  (collectFVars {} e).fvarIds

/-- Exact occurrence of a predicate argument, including compound arguments. -/
def containsArgument (e : Expr) (arguments : Array Expr) : Bool :=
  arguments.any fun argument => (e.find? (· == argument)).isSome

/-- Sharing a local variable counts even when the whole argument does not occur. -/
def dependsOnArguments (e : Expr) (arguments : Array Expr) : Bool :=
  let ids := support e
  arguments.any fun argument => (support argument).any ids.contains

/-- Check a candidate's type and scope, not its truth. Resource failures propagate. -/
def isCandidate (e : Expr) : MetaM Bool := withNewMCtxDepth do
  if !isResolved e then return false
  try
    check e
    return ← isProp e
  catch error =>
    if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
    return false

/-- Keep valid candidates in discovery order. Callers handle instantiation and budgets. -/
def appendCandidate (out : Array Expr) (e : Expr) : MetaM (Array Expr) := do
  if out.contains e then return out
  unless ← isCandidate e do return out
  return out.push e

/-- Quantify indexed properties over optional lower/upper bounds.
Nat indices are coerced when compared with Int bounds; reads stay with the caller. -/
def indexedPredicates (domain : Expr) (lower upper : Option Expr)
    (build : Expr → MetaM (Array Expr)) : MetaM (Array Expr) :=
  withLocalDeclD `index domain fun index => do
    let guard (relation : Name) (bound : Expr) (isLower : Bool) := do
      let mut value := index
      if domain.isConstOf ``Nat then
        if (← whnf (← inferType bound)).isConstOf ``Int then
          value ← mkAppM ``Int.ofNat #[index]
      mkAppM relation (if isLower then #[bound, value] else #[value, bound])
    let lower ← lower.mapM (fun bound => guard ``LE.le bound true)
    let upper ← upper.mapM (fun bound => guard ``LT.lt bound false)
    (← build index).mapM fun body => do
      let body ← match upper with | some guard => mkArrow guard body | none => pure body
      let body ← match lower with | some guard => mkArrow guard body | none => pure body
      mkForallFVars #[index] body

inductive Source where
  | goal | definition | generated | guarded | observation
  deriving BEq

structure Candidate where
  expr : Expr
  origin : String

structure Definition where
  fn : Expr
  typeArgs : Array Expr := #[]
  depth : Nat := 0
  requested : Bool := false
  deriving BEq, Inhabited

structure ScrapeState where
  fixed : FVarIdSet := {}
  goal : Array Candidate := #[]
  definitions : Array Candidate := #[]
  generated : Array Candidate := #[]
  guarded : Array Candidate := #[]
  observations : Array Candidate := #[]
  seen : Std.HashSet Expr := {}
  pending : Array Definition := #[]
  visited : Array (Expr × Array Expr) := #[]
  nodes : Nat := 0
  rejected : Nat := 0
  inspected : Nat := 0
  limitsHit : Array String := #[]
  guardPairs : Nat := 0
  observationPairs : Nat := 0
  anchored : Array PAAnchoredQualifier := #[]
  anchoredAttempts : Nat := 0
  anchoredSeen : Std.HashSet (Expr × Expr) := {}

abbrev ScrapeM := StateRefT ScrapeState MetaM

def limit (name : String) : ScrapeM Unit :=
  modify fun s => if s.limitsHit.contains name then s else
    { s with limitsHit := s.limitsHit.push name }

def visit (cfg : PAScrapeConfig) (depth : Nat) : ScrapeM Bool := do
  if depth > cfg.maxDepth then limit "depth"; return false
  if (← get).nodes >= cfg.maxNodes then limit "nodes"; return false
  modify fun s => { s with nodes := s.nodes + 1 }
  return true

def reject : ScrapeM Unit :=
  modify fun s => { s with rejected := s.rejected + 1 }

/-- Capture the caller's context and abstract clause-local data parameters. -/
def addPredicate (cfg : PAScrapeConfig) (origin : String) (source : Source)
    (p : Expr) : ScrapeM Unit := do
  let p ← instantiateMVars p
  if !isResolved p then reject; return
  unless ← isProp p do reject; return
  if p.isConstOf ``True || p.isConstOf ``False ||
      (p.isForall && source != .observation) then return
  let fixed := (← get).fixed
  let ids := (collectFVars {} p).fvarIds.filter (!fixed.contains ·)
  if ids.isEmpty then return
  if ids.size > cfg.maxParams then reject; return
  let mut types := #[]
  for id in ids do
    let ty ← instantiateMVars (← inferType (mkFVar id))
    if ty.hasFVar || !isResolved ty then reject; return
    if (← isProp ty) || (← whnf ty).isSort then reject; return
    types := types.push ty
  let mut q := p.abstract (ids.map mkFVar)
  for i in (List.range ids.size).reverse do
    q := .lam (Name.mkSimple s!"q{i}") types[i]! q .default
  if q.hasMVar || q.hasLooseBVars ||
      (collectFVars {} q).fvarIds.any (!fixed.contains ·) then reject; return
  if (← get).seen.contains q then return
  let s ← get
  let target := match source with
    | .goal => s.goal
    | .definition => s.definitions
    | .generated => s.generated
    | .guarded => s.guarded
    | .observation => s.observations
  let (cap, label) := match source with
    | .guarded => (cfg.maxGuardedQualifiers, "guarded templates")
    | .observation => (cfg.maxObservationQualifiers, "observation templates")
    | _ => (cfg.maxQualifiers, "templates")
  if target.size >= cap then limit label; return
  let target := target.push ⟨q, origin⟩
  let s := { s with seen := s.seen.insert q }
  set <| match source with
    | .goal => { s with goal := target }
    | .definition => { s with definitions := target }
    | .generated => { s with generated := target }
    | .guarded => { s with guarded := target }
    | .observation => { s with observations := target }
  trace[flex.scrape] "{origin}: {q}"

partial def predicates (cfg : PAScrapeConfig) (origin : String) (source : Source)
    (p : Expr) (depth : Nat := 0) : ScrapeM Unit := do
  unless ← visit cfg depth do return
  let p := p.consumeMData.headBeta
  if let .letE _ _ v b _ := p then
    predicates cfg origin source (b.instantiate1 v) (depth + 1)
  else if let some (l, r) := p.and? then
    predicates cfg origin source l (depth + 1)
    predicates cfg origin source r (depth + 1)
  else
    addPredicate cfg origin source p

def automatic (cfg : PAScrapeConfig) : Bool :=
  cfg.mode == .standard || cfg.mode == .deep

def numericLiteral (ty e : Expr) : MetaM Bool := do
  if ty.isConstOf ``Nat then return (← getNatValue? e).isSome
  return (← getIntValue? e).isSome

def subset (xs ys : Array FVarId) : Bool :=
  xs.all ys.contains

def predicateApplication (e : Expr) : MetaM Bool := do
  unless e.isApp && (e.getAppFn.isFVar || e.getAppFn.isMVar) do return false
  isProp e

end PAScrape.Internal
