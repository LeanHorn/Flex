import Flex.Core
import Flex.Fusion.Flatten
import Flex.Fusion.Graph

open Lean Meta

/-- `scope(κ, e)` — extract the sub-expression relevant to κ (Fig. 9). -/
partial def exprScope (κ : KVar) (e : Expr) : KM Expr := do
  go κ ((← KM.getKVarList).contains κ) e
where
  -- `tracked`: whether κ is in the predicate context, computed once per walk. A κ check is then a
  -- single traversal, `tracked && x.containsMVar κ.mvarId`, with the same answer as
  -- `(← KM.exprKVars x).contains κ`, which traverses `x` once per κ in the context.
  go (κ : KVar) (tracked : Bool) (e : Expr) : KM Expr := do
    -- let e ← whnf e
    -- scope(κ, cₗ ∧ cᵣ)
    if let some (cₗ, cᵣ) := e.and? then
      let inL := (tracked && cₗ.containsMVar κ.mvarId)
      let inR := (tracked && cᵣ.containsMVar κ.mvarId)
      -- κ ∈ Cₗ, κ ∉ Cᵣ
      if inL && !inR
        then go κ tracked cₗ
      -- κ ∉ Cₗ, κ ∈ Cᵣ
      else if !inL && inR
        then go κ tracked cᵣ
      -- fallback: scope(κ, c) = c
      else return e
    -- scope(κ, ∀ x : τ. body)
    -- Handles one forall at a time. The paper's `∀x:b. p ⇒ c'` pattern
    -- is two nested foralls, so this branch fires twice (once with dom = b,
    -- once with dom = p) — together that enforces κ ∉ p.
    else if e.isForall then
      let dom := e.bindingDomain!
      if !(tracked && dom.containsMVar κ.mvarId) then
        withLocalDeclD e.bindingName! e.bindingDomain! fun fvar => do
          let sc ← go κ tracked (e.bindingBody!.instantiate1 fvar)
          let abstr := sc.abstract #[fvar]
          pure (Expr.forallE e.bindingName! dom abstr e.bindingInfo!)
      else
        return mkConst ``False
    else
      return e
