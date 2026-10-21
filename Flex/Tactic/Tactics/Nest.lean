import Lean

open Lean Meta Elab Tactic

namespace Flex.Nesting

/-- The original proposition is equivalent to `expr`. -/
structure Result where
  expr : Expr
  proof : Expr
  deriving Inhabited

private def unchanged (e : Expr) : MetaM Result :=
  return ⟨e, ← mkAppM ``Iff.refl #[e]⟩

private def forward (r : Result) (h : Expr) : MetaM Expr := mkAppM ``Iff.mp #[r.proof, h]
private def backward (r : Result) (h : Expr) : MetaM Expr := mkAppM ``Iff.mpr #[r.proof, h]

private def conjunction (es : Array Expr) : Expr :=
  if es.size == 1 then es[0]!
  else es.toList.dropLast.foldr (mkApp2 (mkConst ``And)) es.back!

private partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then conjuncts e.appFn!.appArg! ++ conjuncts e.appArg!
  else #[e]

private partial def projections (e h : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then
    let p := e.appFn!.appArg!
    let q := e.appArg!
    projections p (mkApp3 (mkConst ``And.left) p q h) ++
      projections q (mkApp3 (mkConst ``And.right) p q h)
  else #[h]

private def projectParts (parts : Array Expr) (h : Expr) : Array Expr := Id.run do
  let mut out := #[]
  let mut rest := h
  for i in [:parts.size - 1] do
    let p := parts[i]!
    let q := conjunction (parts.extract (i + 1) parts.size)
    out := out.push (mkApp3 (mkConst ``And.left) p q rest)
    rest := mkApp3 (mkConst ``And.right) p q rest
  return out.push rest

private partial def rebuild (e : Expr) (hs : Array Expr) (i : Nat := 0) :
    MetaM (Expr × Nat) := do
  if e.isAppOfArity ``And 2 then
    let (l, i) ← rebuild e.appFn!.appArg! hs i
    let (r, i) ← rebuild e.appArg! hs i
    return (← mkAppM ``And.intro #[l, r], i)
  else return (hs[i]!, i + 1)

private def equivalence (old new : Expr)
    (toNew toOld : Expr → MetaM Expr) : MetaM Result := do
  let f ← withLocalDeclD `h old fun h => do mkLambdaFVars #[h] (← toNew h)
  let g ← withLocalDeclD `h new fun h => do mkLambdaFVars #[h] (← toOld h)
  return ⟨new, ← mkAppM ``Iff.intro #[f, g]⟩

private theorem curryGuard (p q r : Prop) : ((p ∧ q) → r) ↔ (p → q → r) := by
  constructor
  · intro h hp hq; exact h ⟨hp, hq⟩
  · intro h hpq; exact h hpq.1 hpq.2

private abbrev Anchor := FVarId × Nat

private partial def predicateCalls (k e : Expr) : Array (Array Expr) :=
  if e.getAppFn == k then #[e.getAppArgs]
  else match e with
    | .app f a => predicateCalls k f ++ predicateCalls k a
    | .forallE _ t b _ | .lam _ t b _ => predicateCalls k t ++ predicateCalls k b
    | .letE _ t v b _ => predicateCalls k t ++ predicateCalls k v ++ predicateCalls k b
    | .mdata _ b | .proj _ _ b => predicateCalls k b
    | _ => #[]

/-- Argument slots occupied by this binder at every occurrence of a predicate. -/
private def anchors (ks : Array Expr) (body x : Expr) : Array Anchor := Id.run do
  let mut result := #[]
  for k in ks do
    let calls := predicateCalls k body
    if calls.isEmpty then continue
    for i in [:calls[0]!.size] do
      if calls.all (fun args => args[i]? == some x) then
        result := result.push (k.fvarId!, i)
  return result

private structure Prefix where
  domain : Expr
  roles : Array Anchor
  guard : Bool

private def prefix? (ks : Array Expr) (e : Expr) : MetaM (Option Prefix) := do
  unless e.isForall do return none
  let domain := e.bindingDomain!
  let guard ← isProp domain
  if guard then return some ⟨domain, #[], true⟩
  let roles ← withLocalDecl e.bindingName! e.bindingInfo! domain fun x =>
    pure (anchors ks (e.bindingBody!.instantiate1 x) x)
  if roles.isEmpty then return none
  return some ⟨domain, roles, false⟩

private structure Group where
  indices : Array Nat
  pref : Option Prefix
  deriving Inhabited

private def groups (ks : Array Expr) (parts : Array Expr) : MetaM (Array Group) := do
  let mut out : Array Group := #[]
  for i in [:parts.size] do
    let pref ← prefix? ks parts[i]!
    let mut added := false
    if let some p := pref then
      for j in [:out.size] do
        let g := out[j]!
        if let some q := g.pref then
          if p.guard != q.guard then continue
          unless ← withNewMCtxDepth (isDefEq p.domain q.domain) do continue
          let common := q.roles.filter (p.roles.contains ·)
          if !p.guard && common.isEmpty then continue
          out := out.set! j ⟨g.indices.push i, some { q with roles := common }⟩
          added := true
          break
    unless added do out := out.push ⟨#[i], pref⟩
  return out

/-- Factor common prefixes without moving existential witnesses or unrelated siblings. -/
partial def nest (e : Expr) (ks : Array Expr := #[]) : MetaM Result := do
  if e.isAppOfArity ``Exists 2 then
    let p := e.appArg!
    let ty := e.appFn!.appArg!
    return ← withLocalDeclD p.bindingName! ty fun x => do
      let body := p.beta #[x]
      let r ← nest body (ks.push x)
      if r.expr == body then return ← unchanged e
      let pred ← mkLambdaFVars #[x] r.expr
      let proof ← mkAppM ``exists_congr #[← mkLambdaFVars #[x] r.proof]
      return ⟨← mkAppM ``Exists #[pred], proof⟩
  else if e.isForall then
    let dom := e.bindingDomain!
    if dom.isAppOfArity ``And 2 && !e.bindingBody!.hasLooseBVars then
      let p := dom.appFn!.appArg!
      let q := dom.appArg!
      let body := e.bindingBody!
      let curried ← mkArrow p (← mkArrow q body)
      let r ← nest curried ks
      return ⟨r.expr, ← mkAppM ``Iff.trans #[← mkAppM ``curryGuard #[p, q, body], r.proof]⟩
    return ← withLocalDecl e.bindingName! e.bindingInfo! dom fun x => do
      let body := e.bindingBody!.instantiate1 x
      let r ← nest body ks
      if r.expr == body then return ← unchanged e
      let result ← mkForallFVars #[x] r.expr
      return ⟨result, ← mkAppM ``forall_congr' #[← mkLambdaFVars #[x] r.proof]⟩
  else if e.isAppOfArity ``And 2 then
    let oldParts := conjuncts e
    let rs ← oldParts.mapM (nest · ks)
    let parts := rs.map (·.expr)
    let gs ← groups ks parts
    if parts == oldParts && e == conjunction parts && gs.all (·.indices.size == 1) then
      return ← unchanged e
    let grouped ← gs.mapM fun g => do
      if g.indices.size == 1 then return ← unchanged parts[g.indices[0]!]!
      let members := g.indices.map (parts[·]!)
      let first := members[0]!
      withLocalDecl first.bindingName! first.bindingInfo! first.bindingDomain! fun x => do
        let bodies := members.map (·.bindingBody!.instantiate1 x)
        let r ← nest (conjunction bodies) ks
        let result ← mkForallFVars #[x] r.expr
        equivalence (conjunction members) result
          (fun h => do
            let hs := projections (conjunction members) h
            let hBody ← mkAndIntroN (hs.toList.map (mkApp · x))
            mkLambdaFVars #[x] (← forward r hBody))
          (fun h => do
            let hBody ← backward r (mkApp h x)
            let hs := projectParts bodies hBody
            mkAndIntroN (← hs.toList.mapM fun hi => mkLambdaFVars #[x] hi))
    let result := conjunction (grouped.map (·.expr))
    equivalence e result
      (fun h => do
        let oldProofs := projections e h
        let hs ← rs.mapIdxM fun i r => forward r oldProofs[i]!
        let proofs ← gs.mapIdxM fun i g => do
          forward grouped[i]! (← mkAndIntroN (g.indices.toList.map (hs[·]!)))
        mkAndIntroN proofs.toList)
      (fun h => do
        let hs := projections result h
        let mut proofs := parts.map fun _ => mkConst ``True.intro
        for i in [:gs.size] do
          let g := gs[i]!
          let groupType := conjunction (g.indices.map (parts[·]!))
          let unpacked := projections groupType (← backward grouped[i]! hs[i]!)
          for j in [:g.indices.size] do
            let idx := g.indices[j]!
            proofs := proofs.set! idx (← backward rs[idx]! unpacked[j]!)
        return (← rebuild e proofs).1)
  else return ← unchanged e

end Flex.Nesting

/-- Factor shared binders and guards, leaving the equivalent goal visible before `zap`. -/
elab "nest_chc" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let exposed ← whnf target
  let r ← Flex.Nesting.nest exposed
  let next ← mkFreshExprSyntheticOpaqueMVar r.expr
  goal.assign (← mkAppM ``Iff.mpr #[r.proof, next])
  replaceMainGoal [next.mvarId!]
