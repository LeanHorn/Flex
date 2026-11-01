import Flex.PA.Scrape.Core

/-! Goal traversal and bounded discovery of definition equations and recursive calls. -/

open Lean Meta

namespace PAScrape.Internal

/-- Library implementation details need explicit selection; common measures do not. -/
def discoverable (name : Name) : MetaM Bool := do
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

def enqueue (cfg : PAScrapeConfig) (d : Definition) : ScrapeM Unit := do
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
  if ty.hasFVar || ty.hasMVar then return
  if ← isProp e then return
  let normalized ← whnf ty
  if normalized.isForall || normalized.isSort then return
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
      let selected ← if cfg.defs.contains name then pure true
        else if automatic cfg then discoverable name else pure false
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

partial def clause (cfg : PAScrapeConfig) (e : Expr) (depth : Nat := 0) : ScrapeM Unit := do
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

def inspectDefinition (cfg : PAScrapeConfig) (d : Definition) : ScrapeM Unit := do
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

end PAScrape.Internal
