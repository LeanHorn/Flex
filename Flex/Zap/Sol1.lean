import Lean
import Flex.Core

open Lean Meta Elab Tactic

-- NOTE: WE NEED TO MATCH FUSION LATER

/-! Preserve-And solution for ZapK.

`exprScope` / `exprSol1` in `Core/Fusion.lean` strip non-κ branches of `∧` — that form is what
`solve_fixpoint` is tuned for. ZapK needs the FULL And-tree preserved so the goal's And ↔ sol's
Or position mirror holds (otherwise `nav`'s orPath bits land on the wrong Or branch).

Scoping follows the paper's structure-preserving `scope′` (Fig. 3): at `c₁ ∧ c₂` with κ in exactly
one side, the κ-free side is replaced with ⊤, keeping the ∧-node for the And↔Or mirror; since
`sol₁(⊤) = ⊥`, that side contributes `False`. Everything else (κ in both sides or in neither,
binders and guards, κ-apps and atoms) keeps its structure. The κ-uses that older code zeroed out
with `False` are annihilated downstream by `simplifyAndExists` (`g ∧ ⊥ ≡ ⊥`), as in the paper.

Each subterm is visited once: the recursion returns whether κ occurs in its input, so `∧` decides
which side to drop from its children's answers instead of re-scanning them. -/

private def occurs (κ : KVar) (tracked : Bool) (e : Expr) : Bool :=
  tracked && e.containsMVar κ.mvarId

mutual

/-- The solution of `κ` in `e` and whether `κ` occurs in `e` (syntactically, before `whnf`).
`tracked` is false when `κ` is not in the predicate context, which is never scoped. -/
private partial def solve (κ : KVar) (tracked : Bool) (e : Expr) : KM (Expr × Bool) := do
  if let some (l, r) := e.and? then
    -- Both sides are solved before the κ-free one is known; a failure in a dropped side is
    -- ignored, as it was never visited before.
    let left ← attempt κ tracked l
    let right ← attempt κ tracked r
    let hasLeft := match left with | .ok (_, h) => h | .error _ => occurs κ tracked l
    let hasRight := match right with | .ok (_, h) => h | .error _ => occurs κ tracked r
    let pick (result : Except Exception (Expr × Bool)) (dropped : Bool) : KM Expr :=
      if dropped then return mkConst ``False else match result with
        | .ok (solution, _) => return solution
        | .error error => throw error
    let solLeft ← pick left (hasRight && !hasLeft)
    let solRight ← pick right (hasLeft && !hasRight)
    return (mkApp2 (mkConst ``Or) solLeft solRight, hasLeft || hasRight)
  else if e.isForall then
    let name := e.bindingName!
    let dom := e.bindingDomain!
    let domSort ← (inferType dom >>= whnf : MetaM Expr)
    if domSort.isProp then
      return ← withLocalDeclD name dom fun pfvar => do
        let (inner, h) ← exposed κ tracked (e.bindingBody!.instantiate1 pfvar)
        return (mkApp2 (mkConst ``And) dom inner, occurs κ tracked dom || h)
    else
      return ← withLocalDeclD name dom fun fvar => do
        let raw := e.bindingBody!.instantiate1 fvar
        let body ← whnf raw
        let (conjunct, h) ← do
          if body.isForall then
            let p := body.bindingDomain!
            let pSort ← (inferType p >>= whnf : MetaM Expr)
            if pSort.isProp then
              withLocalDeclD body.bindingName! p fun pfvar => do
                let (inner, h) ← solve κ tracked (body.bindingBody!.instantiate1 pfvar)
                pure (mkApp2 (mkConst ``And) p inner, occurs κ tracked p || h)
            else
              solve κ tracked body
          else
            solve κ tracked body
        let h := if body == raw then h else occurs κ tracked raw
        let lam := Expr.lam name dom (conjunct.abstract #[fvar]) .default
        return (mkApp2 (mkConst ``Exists [Level.one]) dom lam, occurs κ tracked dom || h)
  else if e.getAppFn.isMVar && e.getAppFn.mvarId! == κ.mvarId then
    let args := e.getAppArgs.toList
    let eqs := (κ.params.zip (args.zip κ.paramTypes)).map fun (pi, (ai, ty)) =>
      mkApp3 (mkConst ``Eq [Level.one]) ty (.fvar (FVarId.mk pi)) ai
    let solution := match eqs with
      | []      => mkConst ``True
      | [eq]    => eq
      | eq :: rest => rest.foldl (mkApp2 (mkConst ``And)) eq
    return (solution, tracked)
  else
    return (mkConst ``False, occurs κ tracked e)

/-- Solve the body after `whnf`; occurrence is that of the body before `whnf`. -/
private partial def exposed (κ : KVar) (tracked : Bool) (raw : Expr) : KM (Expr × Bool) := do
  let body ← whnf raw
  let (solution, h) ← solve κ tracked body
  return (solution, if body == raw then h else occurs κ tracked raw)

private partial def attempt (κ : KVar) (tracked : Bool) (e : Expr)
    : KM (Except Exception (Expr × Bool)) := do
  try return .ok (← solve κ tracked e)
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return .error error

end

/-- Structure-preserving solution of `κ` in `e` (see the module documentation). -/
def exprSol1Pres (κ : KVar) (e : Expr) : KM Expr := do
  let tracked := (← KM.getKVarList).any (·.mvarId == κ.mvarId)
  return (← solve κ tracked e).1
