import Lean

open Lean Meta

inductive PAScrapeMode where
  | no | basic | standard | deep
  deriving BEq, Inhabited

/-- Limits apply to one scraping invocation; candidate limits apply per κ. -/
structure PAScrapeLimits where
  maxParams : Nat := 3
  maxQualifiers : Nat := 128
  maxNodes : Nat := 20000
  maxDepth : Nat := 64
  maxDefinitions : Nat := 16
  maxDefinitionDepth : Nat := 2
  maxCandidatesPerKappa : Nat := 2048
  maxInstancesPerKappa : Nat := 8192

structure PAScrapeConfig extends PAScrapeLimits where
  mode : PAScrapeMode := .no
  defs : Array Name := #[]

structure PAScrapeResult where
  qualifiers : Array Expr := #[]
  origins : Array String := #[]
  visitedNodes : Nat := 0
  inspectedDefinitions : Nat := 0
  rejected : Nat := 0
  limitsHit : Array String := #[]

initialize Lean.registerTraceClass `flex.scrape

namespace PAScrape

private inductive Source where
  | goal | definition | generated
  deriving BEq

private structure Candidate where
  expr : Expr
  origin : String

private structure Definition where
  fn : Expr
  typeArgs : Array Expr := #[]
  depth : Nat := 0
  requested : Bool := false
  deriving BEq, Inhabited

private structure ScrapeState where
  goal : Array Candidate := #[]
  definitions : Array Candidate := #[]
  generated : Array Candidate := #[]
  seen : Std.HashSet Expr := {}
  pending : Array Definition := #[]
  visited : Array (Expr × Array Expr) := #[]
  nodes : Nat := 0
  rejected : Nat := 0
  inspected : Nat := 0
  limitsHit : Array String := #[]

private abbrev ScrapeM := StateRefT ScrapeState MetaM

private def limit (name : String) : ScrapeM Unit :=
  modify fun s => if s.limitsHit.contains name then s else
    { s with limitsHit := s.limitsHit.push name }

private def visit (cfg : PAScrapeConfig) (depth : Nat) : ScrapeM Bool := do
  if depth > cfg.maxDepth then limit "depth"; return false
  if (← get).nodes >= cfg.maxNodes then limit "nodes"; return false
  modify fun s => { s with nodes := s.nodes + 1 }
  return true

private def reject : ScrapeM Unit :=
  modify fun s => { s with rejected := s.rejected + 1 }

/-- Close independent data parameters; temporary binders must never escape. -/
private def addPredicate (cfg : PAScrapeConfig) (origin : String) (source : Source)
    (p : Expr) : ScrapeM Unit := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLooseBVars || !(← isProp p) then reject; return
  if p.isConstOf ``True || p.isConstOf ``False || p.isForall then return
  let ids := (collectFVars {} p).fvarIds
  if ids.isEmpty then return
  if ids.size > cfg.maxParams then reject; return
  let mut types := #[]
  for id in ids do
    let ty ← instantiateMVars (← inferType (mkFVar id))
    if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars ||
        (← isProp ty) || (← whnf ty).isSort then reject; return
    types := types.push ty
  let mut q := p.abstract (ids.map mkFVar)
  for i in (List.range ids.size).reverse do
    q := .lam (Name.mkSimple s!"q{i}") types[i]! q .default
  if q.hasFVar || q.hasMVar || q.hasLooseBVars then reject; return
  if (← get).seen.contains q then return
  let s ← get
  let target := if source == Source.goal then s.goal else if source == Source.definition then s.definitions else s.generated
  if target.size >= cfg.maxQualifiers then limit "templates"; return
  let target := target.push ⟨q, origin⟩
  set { s with
    seen := s.seen.insert q
    goal := if source == Source.goal then target else s.goal
    definitions := if source == Source.definition then target else s.definitions
    generated := if source == Source.generated then target else s.generated }
  trace[flex.scrape] "{origin}: {q}"

private partial def predicates (cfg : PAScrapeConfig) (origin : String) (source : Source)
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

private def automatic (cfg : PAScrapeConfig) : Bool :=
  cfg.mode == .standard || cfg.mode == .deep

/-- Library implementation details need explicit selection; common measures do not. -/
private def discoverable (name : Name) : MetaM Bool := do
  let userName := (privateToUserName? name).getD name
  if userName.isInternalDetail then return false
  unless (← getConstInfo name) matches .defnInfo _ do return false
  if [``List.length, ``Array.size, ``String.length].contains name then return true
  let env ← getEnv
  if let some idx := env.getModuleIdxFor? name then
    let mod := env.header.moduleNames[idx.toNat]!
    if [ `Init, `Lean, `Std, `Mathlib, `Auto, `Smt, `Aesop ].any (·.isPrefixOf mod) then
      return false
  return true

/-- Store only closed type/instance arguments, never equation-local data variables. -/
private def definitionAt (e : Expr) (depth : Nat) : MetaM Definition := do
  let fn := e.getAppFn
  let mut ty ← inferType fn
  let mut typeArgs := #[]
  for arg in e.getAppArgs do
    ty ← whnf ty
    unless ty.isForall do break
    let dom := ty.bindingDomain!
    unless (← whnf dom).isSort || ty.bindingInfo! == .instImplicit do break
    let arg ← instantiateMVars arg
    if arg.hasFVar || arg.hasMVar || arg.hasLooseBVars then break
    typeArgs := typeArgs.push arg
    ty := ty.bindingBody!.instantiate1 arg
  return { fn, typeArgs, depth }

private def enqueue (cfg : PAScrapeConfig) (d : Definition) : ScrapeM Unit := do
  if d.fn.hasMVar then reject; return
  let key := (d.fn, d.typeArgs)
  if (← get).visited.contains key ||
      (← get).pending.any (fun x => x.fn == d.fn && x.typeArgs == d.typeArgs) then return
  let depthLimit := if cfg.mode == .deep then cfg.maxDefinitionDepth else 0
  if !d.requested && d.depth > depthLimit then return
  if (← get).pending.size + (← get).visited.size >= cfg.maxDefinitions then
    limit "definitions"
    return
  modify fun s => { s with pending := s.pending.push d }

private def graphPredicate (cfg : PAScrapeConfig) (origin : String) (source : Source)
    (e : Expr) : ScrapeM Unit := do
  let ty ← instantiateMVars (← inferType e)
  if ty.hasFVar || ty.hasMVar || (← isProp e) ||
      (← whnf ty).isForall || (← whnf ty).isSort then return
  withLocalDeclD `value ty fun v => do
    addPredicate cfg origin source (← mkEq v e)

/-- Inspect finite terms and equation types, without unfolding recursive calls. -/
private partial def terms (cfg : PAScrapeConfig) (origin : String) (source : Source)
    (e : Expr) (depth defDepth : Nat) : ScrapeM Unit := do
  unless ← visit cfg depth do return
  let e := e.consumeMData.headBeta
  match e with
  | .forallE n ty body bi | .lam n ty body bi =>
    if source == Source.definition && (← isProp ty) then predicates cfg origin source ty (depth + 1)
    withLocalDecl n bi ty fun x => terms cfg origin source (body.instantiate1 x) (depth + 1) defDepth
  | .letE _ _ v b _ => terms cfg origin source (b.instantiate1 v) (depth + 1) defDepth
  | .app .. =>
    if let .const name _ := e.getAppFn then
      let selected := cfg.defs.contains name || (automatic cfg && (← discoverable name))
      if selected then
        graphPredicate cfg (origin ++ ": call") source e
        if automatic cfg then enqueue cfg (← definitionAt e defDepth)
      let args := e.getAppArgs
      if (name == ``ite || name == ``dite) && args.size == 5 then
        predicates cfg (origin ++ ": guard") source args[1]! (depth + 1)
        predicates cfg (origin ++ ": guard") source (mkNot args[1]!) (depth + 1)
    for arg in e.getAppArgs do terms cfg origin source arg (depth + 1) defDepth
  | .proj _ _ body => terms cfg origin source body (depth + 1) defDepth
  | .fvar _ =>
    if automatic cfg && (← inferType e).isConstOf ``Bool then
      addPredicate cfg (origin ++ ": bool") source (← mkEq e (mkConst ``Bool.true))
      addPredicate cfg (origin ++ ": bool") source (← mkEq e (mkConst ``Bool.false))
  | _ => pure ()

private partial def clause (cfg : PAScrapeConfig) (e : Expr) (depth : Nat := 0) : ScrapeM Unit := do
  unless ← visit cfg depth do return
  let e := e.consumeMData.headBeta
  if let .letE _ _ v b _ := e then
    clause cfg (b.instantiate1 v) (depth + 1)
  else if e.isForall then
    let dom := e.bindingDomain!
    if automatic cfg && (← isProp dom) then
      predicates cfg "premise" .goal dom (depth + 1)
      terms cfg "premise" .goal dom (depth + 1) 0
    withLocalDecl e.bindingName! e.bindingInfo! dom fun x =>
      clause cfg (e.bindingBody!.instantiate1 x) (depth + 1)
  else if let some (l, r) := e.and? then
    clause cfg l (depth + 1)
    clause cfg r (depth + 1)
  else
    predicates cfg "head" .goal e (depth + 1)
    if automatic cfg then terms cfg "head" .goal e (depth + 1) 0

private def inspectDefinition (cfg : PAScrapeConfig) (d : Definition) : ScrapeM Unit := do
  let name := d.fn.constName!
  let eqns? ← try getEqnsFor? name catch e => do
    if d.requested || e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
    trace[flex.scrape] "skipping {name}: {e.toMessageData}"
    pure none
  let some eqns := eqns? | do
    if d.requested then throwError "fix: no equation lemmas available for `{name}`"
    trace[flex.scrape] "skipping {name}: no equation lemmas"
    reject
    return
  modify fun s => { s with inspected := s.inspected + 1 }
  for eqn in eqns do
    if (← get).nodes >= cfg.maxNodes then limit "nodes"; break
    let info ← getConstInfo eqn
    let eq := if info.levelParams.length == d.fn.constLevels!.length then
      mkConst eqn d.fn.constLevels! else mkConst eqn (info.levelParams.map Level.param)
    let mut ty ← inferType eq
    for arg in d.typeArgs do
      unless ty.isForall do return
      unless ← isDefEq (← inferType arg) ty.bindingDomain! do return
      ty := ty.bindingBody!.instantiate1 arg
    terms cfg s!"definition {name}" .definition ty 0 (d.depth + 1)

private def numericLiteral (ty e : Expr) : MetaM Bool := do
  if ty.isConstOf ``Nat then return (← getNatValue? e).isSome
  return (← getIntValue? e).isSome

/-- Propose at most three variants of a closed numeric qualifier.
    Replace a literal bound with a parameter, or propose `≤` from `<`.
    These are candidates for PA to check, not proved implications. -/
def deepScrapeVariants (q : Expr) : MetaM (Array Expr) := do
  if q.hasFVar || q.hasMVar || q.hasLooseBVars then return #[]
  lambdaTelescope q fun xs body => do
    let body := body.consumeMData.headBeta
    let fn := body.getAppFn
    let some name := fn.constName? | return #[]
    let args := body.getAppArgs
    let arity :=
      if name == ``Eq then 3
      else if name == ``LE.le || name == ``LT.lt then 4
      else if name == ``Nat.le || name == ``Nat.lt ||
          name == ``Int.le || name == ``Int.lt then 2
      else 0
    if arity == 0 || args.size != arity then return #[]
    let lhs := args[arity - 2]!
    let rhs := args[arity - 1]!
    let ty ← whnf (← inferType lhs)
    unless ty.isConstOf ``Nat || ty.isConstOf ``Int do return #[]
    let mut variants := #[]
    if name == ``LT.lt || name == ``Nat.lt || name == ``Int.lt then
      let rel := if ty.isConstOf ``Nat then ``Nat.le else ``Int.le
      let weaker := mkApp2 (mkConst rel) lhs rhs
      variants := variants.push (← mkLambdaFVars xs (← instantiateMVars weaker))
    for i in #[arity - 2, arity - 1] do
      if ← numericLiteral ty args[i]! then
        let variant ← withLocalDeclD `bound ty fun bound =>
          mkLambdaFVars (xs.push bound) (mkAppN fn (args.set! i bound))
        variants := variants.push variant
    return variants

private def collect (cfg : PAScrapeConfig) (body : Expr) : ScrapeM Unit := do
  for name in cfg.defs do
    unless (← getConstInfo name) matches .defnInfo _ do
      throwError "fix: `{name}` is not a definition to scrape"
    enqueue cfg { fn := ← mkConstWithLevelParams name, requested := true }
  if cfg.mode != .no then clause cfg body
  repeat
    let s ← get
    if s.pending.isEmpty then break
    if s.nodes >= cfg.maxNodes then limit "nodes"; break
    let d := s.pending[0]!
    set { s with
      pending := s.pending.extract 1 s.pending.size
      visited := s.visited.push (d.fn, d.typeArgs) }
    inspectDefinition cfg d
  if cfg.mode == .deep then
    let originals := (← get).goal ++ (← get).definitions
    for candidate in originals do
      unless ← visit cfg 0 do break
      for q in ← deepScrapeVariants candidate.expr do
        unless ← visit cfg 0 do break
        lambdaTelescope q fun _ p => addPredicate cfg (candidate.origin ++ ": generalized") .generated p

/-- Interleave sources so a large goal cannot consume every definition/template slot. -/
private def finish (cfg : PAScrapeConfig) (s : ScrapeState) : PAScrapeResult := Id.run do
  let mut selected := #[]
  for i in [:max s.goal.size (max s.definitions.size s.generated.size)] do
    for source in #[s.goal, s.definitions, s.generated] do
      if let some q := source[i]? then
        if selected.size < cfg.maxQualifiers then selected := selected.push q
  let count := s.goal.size + s.definitions.size + s.generated.size
  let limitsHit := if count > selected.size && !s.limitsHit.contains "templates" then
    s.limitsHit.push "templates" else s.limitsHit
  return {
    qualifiers := selected.map (·.expr)
    origins := selected.map (·.origin)
    visitedNodes := s.nodes
    inspectedDefinitions := s.inspected
    rejected := s.rejected
    limitsHit }

end PAScrape

/-- Scraped expressions are candidate templates, never assumed facts. -/
def scrapePAQualifiersWithReport (body : Expr) (cfg : PAScrapeConfig) : MetaM PAScrapeResult := do
  let (_, state) ← (PAScrape.collect cfg (← instantiateMVars body)).run {}
  let result := PAScrape.finish cfg state
  unless result.limitsHit.isEmpty do
    trace[flex.scrape] "limits reached: {result.limitsHit}"
  return result

def scrapePAQualifiers (body : Expr) (cfg : PAScrapeConfig) : MetaM (Array Expr) := do
  return (← scrapePAQualifiersWithReport body cfg).qualifiers
