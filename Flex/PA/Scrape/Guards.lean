import Flex.PA.Scrape.Core

/-! Arithmetic guard combinations and numeric template generalization. -/

open Lean Meta

namespace PAScrape.Internal

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

partial def guardedClauses (cfg : PAScrapeConfig) (e : Expr)
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

/-- Guard cross-products are reserved for arithmetic theory goals. Recursive
    functions still contribute ordinary qualifiers through definition scraping. -/
partial def arithmeticGoal (cfg : PAScrapeConfig) (e : Expr)
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

end PAScrape.Internal

namespace PAScrape
open Internal

/-- Propose at most three variants of a numeric qualifier, preserving caller locals.
    Replace a literal bound with a parameter, or propose `≤` from `<`.
    These are candidates for PA to check, not proved implications. -/
def deepScrapeVariants (q : Expr) : MetaM (Array Expr) := do
  if q.hasMVar || q.hasLooseBVars then return #[]
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

end PAScrape
