import Flex.Core
import Flex.Fusion.Flatten
import Flex.Fusion.Graph
import Flex.Fusion.Scope

open Lean Meta

/-- Smart `And`: `(_ ∧ False) = (False ∧ _) = False`, `(_ ∧ True) = _`.
    Mirrors liquid-fixpoint's empty-cube absorption: when the inner sol1 is
    `False`, the binder predicate above it is dropped, so dead κ-references
    that would survive under `∧ False` never get built into the Expr. -/
private def mkAndSmart (l r : Expr) : Expr :=
  if l.isConstOf ``False || r.isConstOf ``False then mkConst ``False
  else if l.isConstOf ``True then r
  else if r.isConstOf ``True then l
  else mkApp2 (mkConst ``And) l r

/-- Smart `Or`: drops `False`, absorbs `True`. -/
private def mkOrSmart (l r : Expr) : Expr :=
  if l.isConstOf ``True || r.isConstOf ``True then mkConst ``True
  else if l.isConstOf ``False then r
  else if r.isConstOf ``False then l
  else mkApp2 (mkConst ``Or) l r


/-
sol1(κ, c₁ ∧ c₂)        ≡ sol1(κ, c₁) ∨ sol1(κ, c₂)
sol1(κ, ∀ x:b. p ⇒ c)   ≡ ∃x:b. p ∧ sol1(κ, c)
sol1(κ, κ(y₁, ..., yₙ)) ≡ x₁ = y₁ ∧ ... ∧ xₙ = yₙ
sol1(κ, p)              ≡ false
-/
/-- `sol1(κ, e)` — strongest solution (Section 5.2).
    Maps: `And → Or`, `∀(Prop) → And`, `∀(non-Prop) → ∃`, leaf κ-app → equality.
    Uses `mkAndSmart`/`mkOrSmart` and drops the ∃-wrap when the conjunct collapses
    to `False`, mirroring liquid-fixpoint's `first (b :) <$> [] = []` absorption. -/
partial def exprSol1 (κ : KVar) (e : Expr) : KM Expr := do
  -- let e ← whnf e
  let e ← exprScope κ e
  -- c₁ ∧ c₂
  if let some (l, r) := e.and? then
    return mkOrSmart (← exprSol1 κ l) (← exprSol1 κ r)
  -- ∀ x : b. p ⇒ c
  else if e.isForall then
    let name := e.bindingName!
    let dom := e.bindingDomain!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    if domSort.isProp then
      -- Bare implication `p ⇒ c`. Algorithm: emit p ∧ sol1(c) with no ∃ wrap,
      -- since there's no value binder at this level. The Prop binder is
      -- conventionally unused, but instantiate via withLocalDeclD just in case.
      return ← withLocalDeclD name dom fun pfvar => do
        let body ← whnf (e.bindingBody!.instantiate1 pfvar)
        let inner ← exprSol1 κ body
        return mkAndSmart dom inner

    else
      -- ∀ x:b. body -- open x, and boyd is expected to be 'p ⇒ c'
      return ← withLocalDeclD name dom fun fvar => do
        let body ← whnf (e.bindingBody!.instantiate1 fvar)
        let conjunct ← do
          if body.isForall then
            let p := body.bindingDomain!
            let pSort ← (inferType p >>= whnf : MetaM Expr)
            if pSort.isProp then
              -- Inline implication handling: extract p and c', recurse on c'
              -- Implication binder is unused; but introducing fresh fvar just in case
              withLocalDeclD body.bindingName! p fun pfvar => do
                let c'  := body.bindingBody!.instantiate1 pfvar
                let inner ← exprSol1 κ c'
                return mkAndSmart p inner
            else
              exprSol1 κ body
          else
            exprSol1 κ body
        -- If the conjunct collapsed to False, drop the ∃ wrapper too —
        -- this is the Expr-level analog of `first (b :) <$> [] = []`.
        if conjunct.isConstOf ``False then
          return mkConst ``False
        let abstr := conjunct.abstract #[fvar]
        let lam   := Expr.lam name dom abstr .default
        return mkApp2 (mkConst ``Exists [Level.one]) dom lam
  -- κ(y₁, ..., yₙ)
  else if e.getAppFn.isMVar && e.getAppFn.mvarId! == κ.mvarId then
    let args := e.getAppArgs.toList
    -- Build each equality `zᵢ = aᵢ`, but drop tautologies (`zᵢ = zᵢ`) that arise
    -- when `stripScopePrefix` has already substituted the outer binder into `aᵢ`.
    let eqs := (κ.params.zip (args.zip κ.paramTypes)).filterMap fun (pi, (ai, ty)) =>
      let lhs : Expr := .fvar (FVarId.mk pi)
      if lhs == ai then none
      else some (mkApp3 (mkConst ``Eq [Level.one]) ty lhs ai)
    match eqs with
    | []      => return mkConst ``True
    | [eq]    => return eq
    | eq :: rest => return rest.foldl mkAndSmart eq
  else
    return mkConst ``False
