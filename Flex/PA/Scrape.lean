import Lean
import Flex.PA.Structured

open Lean Meta

inductive PAScrapeMode where
  | no | basic | standard | deep
  deriving BEq, Inhabited

/-- Limits apply per invocation, except guard atoms per clause and candidates per κ. -/
structure PAScrapeLimits where
  maxParams : Nat := 3
  maxQualifiers : Nat := 128
  maxNodes : Nat := 20000
  maxDepth : Nat := 64
  maxDefinitions : Nat := 16
  maxDefinitionDepth : Nat := 2
  maxCandidatesPerKappa : Nat := 2048
  maxInstancesPerKappa : Nat := 8192
  maxGuardedQualifiers : Nat := 32
  maxGuardAtoms : Nat := 12
  maxGuardPairs : Nat := 256
  maxObservationQualifiers : Nat := 16
  maxObservationPairs : Nat := 256
  maxObservationBinders : Nat := 1
  maxAnchoredCandidatesPerKappa : Nat := 64
  maxAnchoredAttempts : Nat := 256
  maxAnchoredNodes : Nat := 5000
  /-- Optional broader search; extra candidates can increase certification cost. -/
  maxCompoundCandidatesPerKappa : Nat := 0

structure PAScrapeConfig extends PAScrapeLimits where
  mode : PAScrapeMode := .no
  defs : Array Name := #[]

/-- A source-derived qualifier with its original predicate-slot assignment. -/
structure PAAnchoredQualifier where
  kvar : MVarId
  qualifier : Expr
  slots : List Nat
  origin : String

structure PAScrapeResult where
  qualifiers : Array Expr := #[]
  origins : Array String := #[]
  /-- Observation relations form the final, lowest-priority segment. -/
  observationCount : Nat := 0
  anchored : Array PAAnchoredQualifier := #[]
  visitedNodes : Nat := 0
  inspectedDefinitions : Nat := 0
  rejected : Nat := 0
  limitsHit : Array String := #[]

initialize Lean.registerTraceClass `flex.scrape

namespace PAScrape

private inductive Source where
  | goal | definition | generated | guarded | observation
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

/-- Capture the caller's context and abstract clause-local data parameters. -/
private def addPredicate (cfg : PAScrapeConfig) (origin : String) (source : Source)
    (p : Expr) : ScrapeM Unit := do
  let p ← instantiateMVars p
  if p.hasMVar || p.hasLooseBVars || !(← isProp p) then reject; return
  if p.isConstOf ``True || p.isConstOf ``False ||
      (p.isForall && source != .observation) then return
  let fixed := (← get).fixed
  let ids := (collectFVars {} p).fvarIds.filter (!fixed.contains ·)
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
  set { s with
    seen := s.seen.insert q
    goal := if source == Source.goal then target else s.goal
    definitions := if source == Source.definition then target else s.definitions
    generated := if source == Source.generated then target else s.generated
    guarded := if source == Source.guarded then target else s.guarded
    observations := if source == Source.observation then target else s.observations }
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

private def support (e : Expr) : Array FVarId :=
  (collectFVars {} e).fvarIds

private def subset (xs ys : Array FVarId) : Bool :=
  xs.all ys.contains

/-- Guard combinations stay in arithmetic; ordinary scraping still retains
    applications of user definitions. Products require a literal coefficient. -/
private partial def guardTerm (cfg : PAScrapeConfig) (e : Expr) (depth : Nat) : ScrapeM Bool := do
  unless ← visit cfg depth do return false
  let e := e.consumeMData.headBeta
  if let .letE _ _ value body _ := e then return ← guardTerm cfg (body.instantiate1 value) (depth + 1)
  let ty ← whnf (← inferType e)
  let isInt := ty.isConstOf ``Int
  unless isInt || ty.isConstOf ``Nat do return false
  if e.isFVar then return true
  if ← numericLiteral ty e then return true
  let name := e.getAppFn.constName?.getD .anonymous
  let args := e.getAppArgs
  if [``Neg.neg, ``Int.neg].contains name && isInt && !args.isEmpty then
    let arg := args.back!
    return (← guardTerm cfg arg (depth + 1)) && (← isDefEq e (mkApp (mkConst ``Int.neg) arg))
  if name == ``Int.ofNat && args.size == 1 then return ← guardTerm cfg args[0]! (depth + 1)
  let builtin ←
    if [``HAdd.hAdd, ``Int.add, ``Nat.add].contains name then
      pure (if isInt then ``Int.add else ``Nat.add)
    else if [``HSub.hSub, ``Int.sub, ``Nat.sub].contains name then
      pure (if isInt then ``Int.sub else ``Nat.sub)
    else if [``HMul.hMul, ``Int.mul, ``Nat.mul].contains name then
      pure (if isInt then ``Int.mul else ``Nat.mul)
    else if [``HDiv.hDiv, ``Int.ediv, ``Nat.div].contains name then
      pure (if isInt then ``Int.ediv else ``Nat.div)
    else if [``HMod.hMod, ``Int.emod, ``Nat.mod].contains name then
      pure (if isInt then ``Int.emod else ``Nat.mod)
    else return false
  if args.size < 2 then return false
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  unless (← guardTerm cfg lhs (depth + 1)) && (← guardTerm cfg rhs (depth + 1)) do return false
  if builtin == ``Int.mul || builtin == ``Nat.mul then
    unless (← numericLiteral ty lhs) || (← numericLiteral ty rhs) do return false
  if [``Int.ediv, ``Int.emod, ``Nat.div, ``Nat.mod].contains builtin then
    unless ← numericLiteral ty rhs do return false
  return ← isDefEq e (mkApp2 (mkConst builtin) lhs rhs)

/-- Expose arithmetic atoms under Boolean encodings without unfolding arithmetic. -/
private def arithmeticAtom? (cfg : PAScrapeConfig) (e : Expr) : ScrapeM (Option Expr) := do
  let name := e.getAppFn.constName?.getD .anonymous
  unless [``Eq, ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt,
      ``Int.le, ``Int.lt, ``Nat.le, ``Nat.lt].contains name do return none
  let args := e.getAppArgs
  if args.size < 2 then return none
  let lhs := args[args.size - 2]!
  let rhs := args[args.size - 1]!
  let ty ← whnf (← inferType lhs)
  unless ty.isConstOf ``Int || ty.isConstOf ``Nat do return none
  unless (← guardTerm cfg lhs 0) && (← guardTerm cfg rhs 0) do return none
  if name == ``Eq then return some (← mkEq lhs rhs)
  let rel := if [``LT.lt, ``GT.gt, ``Int.lt, ``Nat.lt].contains name then ``LT.lt else ``LE.le
  let (lhs, rhs) := if name == ``GE.ge || name == ``GT.gt then (rhs, lhs) else (lhs, rhs)
  return some (← mkAppM rel #[lhs, rhs])

private def predicateApplication (e : Expr) : MetaM Bool := do
  return e.isApp && (e.getAppFn.isFVar || e.getAppFn.isMVar) && (← isProp e)

private structure GuardAtoms where
  atoms : Array Expr := #[]
  relations : Array (Array FVarId) := #[]

private partial def guardAtoms (cfg : PAScrapeConfig) (e : Expr)
    (out : GuardAtoms) (depth : Nat) : ScrapeM GuardAtoms := do
  unless ← visit cfg depth do return out
  let e := e.consumeMData.headBeta
  if let .letE _ _ v b _ := e then
    return ← guardAtoms cfg (b.instantiate1 v) out (depth + 1)
  if ← predicateApplication e then
    let ids := e.getAppArgs.foldl (fun ids a =>
      (support a).foldl (fun ids id => if ids.contains id then ids else ids.push id) ids) #[]
    return { out with relations := out.relations.push ids }
  if let some atom ← arithmeticAtom? cfg e then
    return if out.atoms.contains atom then out else { out with atoms := out.atoms.push atom }
  -- Descending through Eq Prop, Iff, Not, and decide exposes their data tests.
  -- Positive existential guards are opened by `guardedPremises`.
  let mut out := out
  for a in e.getAppArgs do out ← guardAtoms cfg a out (depth + 1)
  return out

private def negateAtom (p : Expr) : MetaM Expr := do
  let args := p.getAppArgs
  let name := p.getAppFn.constName?.getD .anonymous
  if name == ``Not && args.size == 1 then return args[0]!
  if name == ``LE.le || name == ``LT.lt then
    return ← mkAppM (if name == ``LE.le then ``LT.lt else ``LE.le)
      #[args[args.size - 1]!, args[args.size - 2]!]
  return mkNot p

/-- Equality with a literal also proposes either interval boundary. -/
private def boundaryAtoms (p : Expr) : MetaM (Array Expr) := do
  let some (_, lhs, rhs) := p.eq? | return #[p]
  let ty ← inferType lhs
  unless (← numericLiteral ty lhs) || (← numericLiteral ty rhs) do return #[p]
  return #[p, ← mkAppM ``LE.le #[lhs, rhs], ← mkAppM ``LE.le #[rhs, lhs]]

/-- Propose `guard → property` over one predicate's arguments in one clause.
    Both polarities are candidates; none of these combinations is assumed valid. -/
private def guardedPredicates (cfg : PAScrapeConfig) (props : Array Expr) : ScrapeM Unit := do
  let mut found : GuardAtoms := {}
  for p in props do found ← guardAtoms cfg p found 0
  let mut atoms := #[]
  for p in found.atoms do
    let ids := support p
    if ids.isEmpty || !found.relations.any (subset ids) then continue
    for variant in ← boundaryAtoms p do
      if atoms.contains variant then continue
      if atoms.size >= cfg.maxGuardAtoms then limit "guard atoms"; break
      atoms := atoms.push variant
  for atom in atoms do
    addPredicate cfg "guard atom" .generated atom
    addPredicate cfg "guard atom" .generated (← negateAtom atom)
  for guard in atoms do
    for property in atoms do
      if (← get).guarded.size >= cfg.maxGuardedQualifiers then limit "guarded templates"; return
      if (← get).guardPairs >= cfg.maxGuardPairs then limit "guard pairs"; return
      modify fun s => { s with guardPairs := s.guardPairs + 1 }
      let gvars := support guard
      let pvars := support property
      -- Avoid pairing facts about precisely the same arguments.
      if subset gvars pvars && subset pvars gvars then continue
      unless found.relations.any (fun vars => subset gvars vars && subset pvars vars) do continue
      for g in #[guard, ← negateAtom guard] do
        for p in #[property, ← negateAtom property] do
          addPredicate cfg "guarded clause" .guarded (mkApp2 (mkConst ``Or) (← negateAtom g) p)

/-- Explore guard branches separately; close witness parameters before leaving their scope. -/
private partial def guardedPremises (cfg : PAScrapeConfig) (head : Expr)
    (pending : List (Expr × Nat)) (props : Array Expr := #[]) : ScrapeM Unit := do
  if (← get).guarded.size >= cfg.maxGuardedQualifiers ||
      (← get).guardPairs >= cfg.maxGuardPairs then return
  match pending with
  | [] => guardedPredicates cfg (props.push head)
  | (premise, depth) :: rest =>
    unless ← visit cfg depth do return
    let premise := premise.consumeMData.headBeta
    if let .letE _ _ value body _ := premise then
      guardedPremises cfg head ((body.instantiate1 value, depth + 1) :: rest) props
    else if let some (left, right) := premise.and? then
      guardedPremises cfg head ((left, depth + 1) :: (right, depth + 1) :: rest) props
    else if premise.isAppOfArity ``Or 2 then
      guardedPremises cfg head ((premise.getArg! 0, depth + 1) :: rest) props
      guardedPremises cfg head ((premise.getArg! 1, depth + 1) :: rest) props
    else if premise.isAppOfArity ``Exists 2 then
      let domain := premise.getArg! 0
      let predicate := premise.getArg! 1
      withLocalDeclD `witness domain fun witness =>
        guardedPremises cfg head ((predicate.beta #[witness], depth + 1) :: rest) props
    else
      guardedPremises cfg head rest (props.push premise)

private partial def guardedClauses (cfg : PAScrapeConfig) (e : Expr)
    (safety : Bool) (premises : Array Expr := #[]) (depth : Nat := 0) : ScrapeM Unit := do
  if (← get).guarded.size >= cfg.maxGuardedQualifiers ||
      (← get).guardPairs >= cfg.maxGuardPairs then return
  unless ← visit cfg depth do return
  let e := e.consumeMData.headBeta
  if let .letE _ _ v b _ := e then
    guardedClauses cfg (b.instantiate1 v) safety premises (depth + 1)
  else if e.isForall then
    let dom := e.bindingDomain!
    let premises := if ← isProp dom then premises.push dom else premises
    withLocalDecl e.bindingName! e.bindingInfo! dom fun x =>
      guardedClauses cfg (e.bindingBody!.instantiate1 x) safety premises (depth + 1)
  else if let some (l, r) := e.and? then
    guardedClauses cfg l safety premises (depth + 1)
    guardedClauses cfg r safety premises (depth + 1)
  else
    let isSafety := !(← predicateApplication e)
    if isSafety == safety then
      guardedPremises cfg e (premises.toList.map (·, 0))

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

/-- Guard cross-products are reserved for arithmetic theory goals. Recursive
    functions still contribute ordinary qualifiers through definition scraping. -/
private partial def arithmeticGoal (cfg : PAScrapeConfig) (e : Expr)
    (depth : Nat) : ScrapeM Bool := do
  unless ← visit cfg depth do return false
  let e := e.consumeMData.headBeta
  if let .letE _ _ value body _ := e then
    return ← arithmeticGoal cfg (body.instantiate1 value) (depth + 1)
  if e.isForall then
    let domain := e.bindingDomain!
    if (← isProp domain) && !(← arithmeticGoal cfg domain (depth + 1)) then return false
    return ← withLocalDecl e.bindingName! e.bindingInfo! domain fun x =>
      arithmeticGoal cfg (e.bindingBody!.instantiate1 x) (depth + 1)
  if e.isAppOfArity ``Exists 2 then
    let domain ← whnf e.appFn!.appArg!
    unless domain.isConstOf ``Int || domain.isConstOf ``Nat ||
        domain.isConstOf ``Bool || domain.isProp do return false
    return ← withLocalDeclD `witness domain fun x =>
      arithmeticGoal cfg (mkApp e.appArg! x).headBeta (depth + 1)
  let type ← whnf (← inferType e)
  if type.isConstOf ``Int || type.isConstOf ``Nat then return ← guardTerm cfg e depth
  if e.isFVar || e.isMVar then return true
  let name := e.getAppFn.constName?.getD .anonymous
  if [``True, ``False, ``Bool.true, ``Bool.false].contains name then return true
  unless (← predicateApplication e) || [``Eq, ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt,
      ``Int.le, ``Int.lt, ``Nat.le, ``Nat.lt, ``And, ``Or, ``Not, ``Iff,
      ``Bool.and, ``Bool.or, ``Bool.not, ``Bool.xor, ``BEq.beq, ``decide].contains name do
    return false
  for arg in e.getAppArgs do
    let argType ← whnf (← inferType arg)
    if (← isProp arg) || argType.isConstOf ``Int || argType.isConstOf ``Nat ||
        argType.isConstOf ``Bool then
      unless ← arithmeticGoal cfg arg (depth + 1) do return false
  return true

private structure Observations where
  relations : Array Expr := #[]
  predicates : Array Expr := #[]
  equalities : Array Expr := #[]

private partial def observationAtoms (cfg : PAScrapeConfig) (raw : Expr)
    (out : Observations) (depth : Nat := 0) : ScrapeM Observations := do
  unless ← visit cfg depth do return out
  let e := raw.consumeMData.headBeta
  if let .letE _ _ value body _ := e then
    return ← observationAtoms cfg (body.instantiate1 value) out (depth + 1)
  if let .forallE _ domain body _ := e then
    if (← isProp domain) && !body.hasLooseBVar 0 then
      let out ← observationAtoms cfg domain out (depth + 1)
      return ← observationAtoms cfg body out (depth + 1)
  let fn := e.getAppFn
  let fixed := (← get).fixed
  if ← predicateApplication e then
    unless fn.isFVar && fixed.contains fn.fvarId! do
      return if out.relations.contains e then out else
        { out with relations := out.relations.push e }
  let mut out := out
  if e.isAppOfArity ``Eq 3 && !e.hasMVar && !out.equalities.contains e then
    out := { out with equalities := out.equalities.push e }
  if e.isApp && !e.hasMVar && !e.hasLooseBVars && (← isProp e) then
    let semantic ← match fn with
      | .const name _ => discoverable name
      | .fvar id => pure (fixed.contains id)
      | _ => pure false
    if semantic && !out.predicates.contains e then
      out := { out with predicates := out.predicates.push e }
  -- Quantified observations need their own binding rule; do not cross binders here.
  for arg in e.getAppArgs do
    out ← observationAtoms cfg arg out (depth + 1)
  return out

private inductive ObservationMode where
  | relate | quantify | arguments | anchored | compound
  deriving BEq

/-- Abstract compound κ arguments, such as record fields, into template parameters. -/
private def observationArguments (cfg : PAScrapeConfig) (observation relation : Expr) : ScrapeM Unit := do
  let mut inputs := #[]
  let mut types := #[]
  for arg in relation.getAppArgs do
    if arg.isFVar || !arg.hasFVar || arg.hasMVar || inputs.contains arg then continue
    unless (observation.find? (· == arg)).isSome do continue
    let ty ← instantiateMVars (← inferType arg)
    if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars || (← isProp ty) ||
        (← whnf ty).isSort then continue
    inputs := inputs.push arg
    types := types.push ty
  if inputs.isEmpty || inputs.size > cfg.maxParams then return
  withLocalDeclsDND (types.map (`argument, ·)) fun parameters => do
    let property := observation.replace fun e =>
      inputs.findIdx? (· == e) |>.map (parameters[·]!)
    -- A retained argument may depend on a field that was abstracted.
    try
      check property
    catch e =>
      if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
      reject
      return
    addPredicate cfg "predicate arguments" .observation property

/-- Retain the observed slot assignment instead of enumerating type-compatible permutations. -/
private def anchorPredicate (cfg : PAScrapeConfig) (origin : String)
    (property relation : Expr) : ScrapeM Unit := do
  if property.isConstOf ``True then return
  if let some (_, lhs, rhs) := property.eq? then
    if lhs == rhs then return
  let .mvar kvar := relation.getAppFn | return
  if (← get).anchoredSeen.contains (property, relation) then return
  modify fun s => { s with anchoredSeen := s.anchoredSeen.insert (property, relation) }
  if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then
    limit "anchored attempts"
    return
  modify fun s => { s with anchoredAttempts := s.anchoredAttempts + 1 }
  if ((← get).anchored.filter (·.kvar == kvar)).size >= cfg.maxAnchoredCandidatesPerKappa then
    limit "anchored candidates"
    return
  if property.hasMVar || property.hasLooseBVars then return
  let args := relation.getAppArgs
  let mut inputs := #[]
  let mut types := #[]
  let mut slots := #[]
  for arg in args, i in [:args.size] do
    if !arg.hasFVar || arg.hasMVar || inputs.contains arg then continue
    unless (property.find? (· == arg)).isSome do continue
    let ty ← instantiateMVars (← inferType arg)
    if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars || (← isProp ty) ||
        (← whnf ty).isSort then continue
    inputs := inputs.push arg
    types := types.push ty
    slots := slots.push i
  if inputs.isEmpty then return
  if origin == "source arguments" && inputs.size <= cfg.maxParams &&
      inputs.all Expr.isFVar then return
  let fixed := (← get).fixed
  withLocalDeclsDND (types.map (`slot, ·)) fun parameters => do
    let body := property.replace fun e =>
      inputs.findIdx? (· == e) |>.map (parameters[·]!)
    let mut q := body.abstract parameters
    for i in (List.range parameters.size).reverse do
      q := .lam (Name.mkSimple s!"q{i}") types[i]! q .default
    if q.hasMVar || q.hasLooseBVars || (support q).any (!fixed.contains ·) then return
    try check q
    catch e =>
      if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
      reject
      return
    unless ← isProp body do return
    if (← get).anchored.any (fun old =>
        old.kvar == kvar && old.qualifier == q && old.slots == slots.toList) then return
    modify fun s => { s with anchored := s.anchored.push ⟨kvar, q, slots.toList, origin⟩ }
    trace[flex.scrape] "{origin}: {q} at slots {slots}"

private def normalizeOffsets (property : Expr) : MetaM Expr := do
  let mut lemmas : SimpTheorems := {}
  for name in #[``Int.sub_eq_add_neg, ``Int.neg_add, ``Int.neg_neg,
      ``Int.add_assoc, ``Int.add_zero, ``Int.zero_add,
      ``Int.add_left_neg, ``Int.add_right_neg] do
    lemmas ← lemmas.addConst name
  let context ← Simp.mkContext { maxSteps := 1000, failIfUnchanged := false } #[lemmas]
  return (← Meta.simp property context).1.expr

/-- Alias equations propose candidates only; PA still checks every resulting predicate. -/
private def anchoredObservation (cfg : PAScrapeConfig) (property relation : Expr)
    (equalities : Array Expr) : ScrapeM Unit := do
  anchorPredicate cfg "source arguments" property relation
  for candidate in ← Structured.absoluteIndexCandidates property do
    anchorPredicate cfg "absolute index" candidate relation
  let mut rewritten := property
  for _ in [:3] do
    let previous := rewritten
    for eq in equalities do
      let a := eq.getArg! 1
      let b := eq.getArg! 2
      let (lhs, rhs) := if a.isFVar then (a, b) else (b, a)
      unless lhs.isFVar && !relation.getAppArgs.contains lhs &&
          !rhs.containsFVar lhs.fvarId! do continue
      rewritten := rewritten.replaceFVar lhs rhs
    if rewritten == previous then break
  if rewritten != property then
    anchorPredicate cfg "source aliases" rewritten relation
    anchorPredicate cfg "source offsets" (← normalizeOffsets rewritten) relation
    for candidate in ← Structured.absoluteIndexCandidates rewritten do
      anchorPredicate cfg "absolute index" candidate relation

/-- Compare observations at κ arguments, optionally quantifying their extra inputs. -/
private def observationPredicates (cfg : PAScrapeConfig) (mode : ObservationMode)
    (props : Array Expr) : ScrapeM Unit := do
  let mut found : Observations := {}
  for p in props do found ← observationAtoms cfg p found
  if mode == .compound then
    for relation in found.relations do
      if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
      let .mvar kvar := relation.getAppFn | continue
      let count := ((← get).anchored.filter fun q =>
        q.kvar == kvar && q.origin == "compound arguments").size
      let budget := min 24 (min (cfg.maxCompoundCandidatesPerKappa - count)
        (cfg.maxAnchoredAttempts - (← get).anchoredAttempts))
      for candidate in ← Structured.compoundCandidates found.predicates relation.getAppArgs budget do
        anchorPredicate cfg "compound arguments" candidate relation
    return
  let fixed := (← get).fixed
  let observations := if mode == .anchored then
      found.predicates ++ found.equalities else found.predicates
  if mode == .anchored then
    for relation in found.relations do
      if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
      let .mvar kvar := relation.getAppFn | continue
      let count := ((← get).anchored.filter (·.kvar == kvar)).size
      let budget := min 24 (min (cfg.maxAnchoredCandidatesPerKappa - count)
        (cfg.maxAnchoredAttempts - (← get).anchoredAttempts))
      if budget == 0 then continue
      let arguments := relation.getAppArgs
      let families := #[
        ("array prefix", ← Structured.prefixCandidates props arguments budget),
        ("semantic arguments", ← Structured.slotCandidates found.predicates arguments budget),
        ("list structure", ← Structured.listCandidates props arguments budget),
        ("list prefix", ← Structured.listPrefixCandidates props arguments budget)]
      for i in [:families.foldl (fun n (_, candidates) => max n candidates.size) 0] do
        for (origin, candidates) in families do
          if let some candidate := candidates[i]? then
            anchorPredicate cfg origin candidate relation
  for observation in observations do
    let ids := (support observation).filter (!fixed.contains ·)
    for relation in found.relations do
      if mode == .anchored then
        if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
        let .mvar kvar := relation.getAppFn | continue
        if ((← get).anchored.filter (·.kvar == kvar)).size >= cfg.maxAnchoredCandidatesPerKappa then
          continue
        anchoredObservation cfg observation relation found.equalities
        continue
      if mode == .arguments then
        observationArguments cfg observation relation
        continue
      let args := observation.getAppArgs
      let extra := ids.filter (!(support relation).contains ·)
      if (mode == .quantify) != !extra.isEmpty || extra.size > cfg.maxObservationBinders then continue
      -- Extra observation inputs become universal binders, never extra κ parameters.
      -- Do not capture an input belonging to another predicate occurrence.
      let mut binderTypes := #[]
      for id in extra do
        let x := mkFVar id
        unless args.contains x do break
        if found.relations.any (fun r => (support r).contains id) then break
        let ty ← instantiateMVars (← inferType x)
        if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars || (← isProp ty) ||
            (← whnf ty).isSort || (← whnf ty).isForall then break
        binderTypes := binderTypes.push ty
      unless binderTypes.size == extra.size do continue
      let mut type ← inferType observation.getAppFn
      for i in [:args.size] do
        type ← whnf type
        unless type.isForall do break
        let domain := type.bindingDomain!
        let dependent := type.bindingBody!.hasLooseBVar 0
        let isInstance := type.bindingInfo! == .instImplicit
        type := type.bindingBody!.instantiate1 args[i]!
        let arg := args[i]!
        unless arg.isFVar && relation.getAppArgs.contains arg do continue
        if dependent || isInstance || domain.hasFVar || domain.hasMVar ||
            (← isProp domain) || (← whnf domain).isSort then continue
        for replacement in relation.getAppArgs do
          if (← get).observations.size >= cfg.maxObservationQualifiers then
            limit "observation templates"; return
          if (← get).observationPairs >= cfg.maxObservationPairs then
            limit "observation pairs"; return
          unless replacement.isFVar && replacement != arg do continue
          modify fun s => { s with observationPairs := s.observationPairs + 1 }
          let replacementType ← inferType replacement
          if replacementType.hasFVar || replacementType.hasMVar then continue
          unless ← isDefEq domain replacementType do continue
          let other := mkAppN observation.getAppFn (args.set! i replacement)
          let mut property := (mkApp2 (mkConst ``Iff) observation other).abstract (extra.map mkFVar)
          for j in (List.range extra.size).reverse do
            property := .forallE (Name.mkSimple s!"value{j}") binderTypes[j]! property .default
          addPredicate cfg "observation relation" .observation
            property

private partial def observationClauses (cfg : PAScrapeConfig) (mode : ObservationMode) (raw : Expr)
    (premises : Array Expr := #[]) (depth : Nat := 0) : ScrapeM Unit := do
  if mode == .anchored || mode == .compound then
    if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
  else if (← get).observations.size >= cfg.maxObservationQualifiers ||
      (← get).observationPairs >= cfg.maxObservationPairs then return
  unless ← visit cfg depth do return
  let e := raw.consumeMData.headBeta
  if let .letE _ _ value body _ := e then
    observationClauses cfg mode (body.instantiate1 value) premises (depth + 1)
  else if e.isForall then
    let domain := e.bindingDomain!
    let premises := if ← isProp domain then premises.push domain else premises
    withLocalDecl e.bindingName! e.bindingInfo! domain fun x =>
      observationClauses cfg mode (e.bindingBody!.instantiate1 x) premises (depth + 1)
  else if let some (left, right) := e.and? then
    observationClauses cfg mode left premises (depth + 1)
    observationClauses cfg mode right premises (depth + 1)
  else
    observationPredicates cfg mode (premises.push e)

private def interleavePredicates (candidates : Array PAAnchoredQualifier) (cap : Nat)
    : Array PAAnchoredQualifier := Id.run do
  let mut families : Array (MVarId × Name × Array PAAnchoredQualifier) := #[]
  for candidate in candidates do
    let mut body := candidate.qualifier
    while body.isLambda do body := body.bindingBody!
    let name := body.getAppFn.constName?.getD .anonymous
    if let some i := families.findIdx? (fun (k, n, _) => k == candidate.kvar && n == name) then
      let (k, n, old) := families[i]!
      families := families.set! i (k, n, old.push candidate)
    else
      families := families.push (candidate.kvar, name, #[candidate])
  let mut result := #[]
  for i in [:cap] do
    for (k, _, family) in families do
      if let some candidate := family[i]? then
        if (result.filter (·.kvar == k)).size < cap then result := result.push candidate
  return result

private def collect (cfg : PAScrapeConfig) (body : Expr) : ScrapeM Unit := do
  for name in cfg.defs do
    unless (← getConstInfo name) matches .defnInfo _ do
      throwError "fix: `{name}` is not a definition to scrape"
    enqueue cfg { fn := ← mkConstWithLevelParams name, requested := true }
  if cfg.mode != .no then clause cfg body
  if automatic cfg && cfg.maxGuardedQualifiers > 0 then
    -- Eligibility has its own bounded traversal; a rejected goal keeps ordinary scraping unchanged.
    let (eligible, _) ← (arithmeticGoal cfg body 0).run {}
    if eligible then
      -- Safety clauses expose demanded properties before transition-clause proposals.
      guardedClauses cfg body true
      guardedClauses cfg body false
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
  if automatic cfg && cfg.maxObservationQualifiers > 0 then
    observationClauses cfg .relate body
    if cfg.maxObservationBinders > 0 then observationClauses cfg .quantify body
    observationClauses cfg .arguments body
  if automatic cfg && cfg.maxAnchoredCandidatesPerKappa > 0 then
    observationClauses { cfg with maxNodes := (← get).nodes + cfg.maxAnchoredNodes } .anchored body
    -- Gather twice the supplemental quota, then share it across named predicates.
    if cfg.maxCompoundCandidatesPerKappa > 0 then
      let ordinary := (← get).anchored
      let quota := 2 * cfg.maxCompoundCandidatesPerKappa
      observationClauses { cfg with
        maxNodes := (← get).nodes + cfg.maxAnchoredNodes
        maxAnchoredAttempts := (← get).anchoredAttempts + cfg.maxAnchoredAttempts
        maxCompoundCandidatesPerKappa := quota
        maxAnchoredCandidatesPerKappa :=
          cfg.maxAnchoredCandidatesPerKappa + quota } .compound body
      let extra := (← get).anchored.extract ordinary.size (← get).anchored.size
      let selected := interleavePredicates extra cfg.maxCompoundCandidatesPerKappa
      modify fun s => { s with anchored := ordinary ++ selected }

/-- Interleave sources so a large goal cannot consume every definition/template slot. -/
private def finish (cfg : PAScrapeConfig) (s : ScrapeState) : PAScrapeResult := Id.run do
  let mut selected := #[]
  for i in [:max s.goal.size (max s.guarded.size (max s.definitions.size s.generated.size))] do
    for source in #[s.goal, s.guarded, s.definitions, s.generated] do
      if let some q := source[i]? then
        if selected.size < cfg.maxQualifiers then selected := selected.push q
  -- New observation templates use only slots left by existing scraping.
  let ordinaryCount := selected.size
  for candidate in s.observations do
    if selected.size < cfg.maxQualifiers then selected := selected.push candidate
  let count := s.goal.size + s.definitions.size + s.generated.size + s.guarded.size + s.observations.size
  let limitsHit := if count > selected.size && !s.limitsHit.contains "templates" then
    s.limitsHit.push "templates" else s.limitsHit
  return {
    qualifiers := selected.map (·.expr)
    origins := selected.map (·.origin)
    observationCount := selected.size - ordinaryCount
    anchored := s.anchored
    visitedNodes := s.nodes
    inspectedDefinitions := s.inspected
    rejected := s.rejected
    limitsHit }

end PAScrape

/-- Candidate templates may capture the caller's context, never temporary scraping binders. -/
def scrapePAQualifiersWithReport (body : Expr) (cfg : PAScrapeConfig) : MetaM PAScrapeResult := do
  let fixed := FVarIdSet.ofArray (← getLCtx).getFVarIds
  let (_, state) ← (PAScrape.collect cfg (← instantiateMVars body)).run { fixed }
  let result := PAScrape.finish cfg state
  unless result.limitsHit.isEmpty do
    trace[flex.scrape] "limits reached: {result.limitsHit}"
  return result

def scrapePAQualifiers (body : Expr) (cfg : PAScrapeConfig) : MetaM (Array Expr) := do
  return (← scrapePAQualifiersWithReport body cfg).qualifiers
