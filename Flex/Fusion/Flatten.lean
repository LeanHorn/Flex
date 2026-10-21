
import Flex.Core

open Lean Meta
/-- Flatten: split `And` at top level, distribute `∀` over `And`.
The default exposes definitions with `whnf`. Exporters can supply a reducer that
preserves theory operators for a downstream translator. -/
partial def exprFlat (e : Expr) (expose : Expr → MetaM Expr := whnf) : KM (List Expr) := do
  let e ← expose e

  -- flat(true) ≃ ∅
  if e.isConstOf ``True then
    return []
  -- flat(cₗ ∧ cᵣ) ≃ flat(cₗ) ⋃ flat(cᵣ)
  else if let some (l, r) := e.and? then
    return (← exprFlat l expose) ++ (← exprFlat r expose)
  -- flat(∀ x : b. c)
  -- NOTE: this works with multiple guards
  -- so, c can be p₁ → p₂ → ... → pₙ → c
  -- in Expr, p → q is essentially ∀ _ : p, q
  -- so it will be covered by below case
  else if e.isForall then
    -- introduce a free-variable for `x`
    withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
      -- flatCs ≃ flatten(c'),
      -- where c' is instantiation of c with free variable x
      let flatBodies ← exprFlat (e.bindingBody!.instantiate1 fvar) expose
      -- {∀ x : b. p ⇒ c'' | c'' ∈ flatCs}
      flatBodies.mapM fun fb => do
        let abstr := fb.abstract #[fvar]
        pure (Expr.forallE e.bindingName! e.bindingDomain! abstr e.bindingInfo!)
  else
    return [e]
