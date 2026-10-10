import Lean

open Lean Meta

/-- Like liquid-fixpoint's Horn scraper: heads only, or heads and premises. -/
inductive PAScrapeMode where
  | no | head | both
  deriving BEq, Inhabited

structure PAScrapeConfig where
  mode : PAScrapeMode := .no
  defs : Array Name := #[]
  maxParams : Nat := 3
  maxQualifiers : Nat := 128

initialize Lean.registerTraceClass `flex.scrape

namespace PAScrape

abbrev ScrapeM := StateRefT (Array Expr) MetaM

/-- Abstract the free data variables of a concrete predicate. The current
    instantiator supports independent, monomorphic slots; skip predicates that
    need dependent parameters, proof parameters, or unresolved κ metavariables. -/
private def addPredicate (cfg : PAScrapeConfig) (p : Expr) : ScrapeM Unit := do
  if (← get).size >= cfg.maxQualifiers then return
  -- Resolve assigned term/universe metavariables before structural deduplication.
  let p ← instantiateMVars p
  if p.hasExprMVar || p.hasLooseBVars || !(← isProp p) then return
  if p.isConstOf ``True || p.isConstOf ``False || p.isForall then return
  let ids := (collectFVars {} p).fvarIds
  if ids.isEmpty || ids.size > cfg.maxParams then return
  let mut types := #[]
  for id in ids do
    let ty ← inferType (mkFVar id)
    if ty.hasFVar || ty.hasExprMVar || (← isProp ty) || (← whnf ty).isSort then return
    types := types.push ty
  let mut q := p.abstract (ids.map mkFVar)
  for i in (List.range ids.size).reverse do
    q := .lam (Name.mkSimple s!"q{i}") types[i]! q .default
  unless (← get).contains q do
    trace[flex.scrape] "candidate: {q}"
    modify (·.push q)

/-- Split concrete conjunctions, but never mine the arguments of a κ as
    propositions. A negative/compound predicate is retained as one candidate. -/
private partial def predicates (cfg : PAScrapeConfig) (p : Expr) : ScrapeM Unit := do
  if let some (l, r) := p.and? then
    predicates cfg l
    predicates cfg r
  else
    addPredicate cfg p

private partial def clause (cfg : PAScrapeConfig) (e : Expr) : ScrapeM Unit := do
  if (← get).size >= cfg.maxQualifiers then return
  let e := e.consumeMData.headBeta
  if let .letE _ _ value body _ := e then
    clause cfg (body.instantiate1 value)
    return
  if e.isForall then
    let dom := e.bindingDomain!
    if cfg.mode == .both && (← isProp dom) then predicates cfg dom
    withLocalDecl e.bindingName! e.bindingInfo! dom fun x =>
      clause cfg (e.bindingBody!.instantiate1 x)
  else if let some (l, r) := e.and? then
    clause cfg l
    clause cfg r
  else
    predicates cfg e

/-- Lift a selected function call into a graph predicate `fun v xs => v = f xs`.
    In particular `fib (n - 1)` produces `fun v n => v = fib (n - 1)`.
    This is a candidate template, NOT an assertion about an arbitrary `v`. -/
private def graphPredicate (cfg : PAScrapeConfig) (e : Expr) : ScrapeM Unit := do
  let ty ← inferType e
  if ty.hasFVar || ty.hasExprMVar || (← isProp e) || (← whnf ty).isForall ||
      (← whnf ty).isSort then return
  withLocalDeclD `value ty fun v => do
    addPredicate cfg (← mkEq v e)

/-- Inspect a finite equation body, without unfolding recursive calls.
    Equation lemmas avoid the implementation details of well-founded recursion.
    Pattern-match branches are exposed by the equation compiler; `if` guards
    contribute both polarities. Calls to explicitly selected definitions
    contribute graph predicates, including calls nested in arithmetic. -/
private partial def definitionExpr (cfg : PAScrapeConfig) (e : Expr) : ScrapeM Unit := do
  if (← get).size >= cfg.maxQualifiers then return
  match e with
  | .forallE n ty body bi | .lam n ty body bi =>
    if ← isProp ty then predicates cfg ty
    withLocalDecl n bi ty fun x => definitionExpr cfg (body.instantiate1 x)
  | .letE _ _ value body _ => definitionExpr cfg (body.instantiate1 value)
  | .mdata _ body => definitionExpr cfg body
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const name _ := fn then
      if cfg.defs.contains name && !e.hasLooseBVars then graphPredicate cfg e
      if (name == ``ite || name == ``dite) && args.size == 5 then
        let cond := args[1]!
        predicates cfg cond
        predicates cfg (mkNot cond)
    -- Visit full arguments, rather than every partially applied function spine.
    for arg in args do
      definitionExpr cfg arg
  | .proj _ _ body => definitionExpr cfg body
  | _ => pure ()

end PAScrape

/-- Per-invocation candidates, merged with `@[qualif]` by `pa_cert`/`fix`.
    Scraping never registers declarations or marks candidates as proven facts. -/
def scrapePAQualifiers (body : Expr) (cfg : PAScrapeConfig) : MetaM (Array Expr) := do
  let body ← instantiateMVars body
  let (_, qs) ← (do
    if cfg.mode != .no then PAScrape.clause cfg body
    for name in cfg.defs do
      let info ← getConstInfo name
      unless info matches .defnInfo _ do
        throwError "fix: `{name}` is not a definition to scrape"
      let some eqns ← getEqnsFor? name
        | throwError "fix: no equation lemmas available for `{name}`"
      for eqn in eqns do
        PAScrape.definitionExpr cfg (← inferType (← mkConstWithLevelParams eqn))
    : PAScrape.ScrapeM Unit).run #[]
  return qs
