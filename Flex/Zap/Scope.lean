import Lean
import Flex.Core

open Lean Meta Elab Tactic

-- NOTE: WE NEED TO MATCH FUSION LATER

-- Preserve-And scope/sol1 for ZapK
--
-- `exprScope` / `exprSol1` in `Core/Fusion.lean` strip non-κ branches
-- of `∧` — that form is what `solve_fixpoint` is tuned for. ZapK needs
-- the FULL And-tree preserved so the goal's And ↔ sol's Or position
-- mirror holds (otherwise `nav`'s orPath bits land on the wrong
-- Or branch). These local copies do exactly that.
partial def exprScopePres (κ : KVar) (e : Expr) : KM Expr := do
  -- Faithful to the paper's structure-preserving `scope′` (Fig. 3):
  --   c₁ ∧ c₂, κ in exactly one side : recurse that side, replace the κ-free
  --             side with ⊤ (keep the ∧-node for the And↔Or mirror).
  --   ∀x:b. c (value binder) / g → c with κ∉g : recurse under the binder/guard.
  --   everything else (κ in both ∧ sides, κ ∈ g, κ-app/atom leaf) : catch-all
  --             `scope′(κ,c) ≡ c` — return `c` unchanged (NOT False).
  -- The κ-uses that the old code zeroed out with `False` are now annihilated
  -- downstream by `simplifyAndExists` (`g ∧ ⊥ ≡ ⊥`), matching the paper.
  if let some (l, r) := e.and? then
    let lHas := (← KM.exprKVars l).contains κ
    let rHas := (← KM.exprKVars r).contains κ
    if lHas && !rHas then
      return mkApp2 (mkConst ``And) (← exprScopePres κ l) (mkConst ``True)
    else if rHas && !lHas then
      return mkApp2 (mkConst ``And) (mkConst ``True) (← exprScopePres κ r)
    else
      return e
  else if e.isForall then
    let dom := e.bindingDomain!
    if !(← KM.exprKVars dom).contains κ then
      withLocalDeclD e.bindingName! dom fun fvar => do
        let sc ← exprScopePres κ (e.bindingBody!.instantiate1 fvar)
        let abstr := sc.abstract #[fvar]
        pure (Expr.forallE e.bindingName! dom abstr e.bindingInfo!)
    else
      return e
  else
    return e
