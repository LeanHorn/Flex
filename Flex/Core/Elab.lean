import Lean
import Flex.Core.KVar

open Lean Meta

/-- Discharge each `∃` at the head of `goal` by supplying a fresh
    metavariable as the witness.

    For a goal `?goal : ∃ κ : T, P κ`, builds the proof term
        `Exists.intro T (fun κ => P κ) ?κ ?proof`
    and assigns `?goal` to it, where:
      • `?κ : T` is a fresh `syntheticOpaque` mvar — the witness slot
        that fusion will later fill via `?κ.assign`.
      • `?proof : P ?κ` is a fresh mvar — the new proof obligation.

    Recurses on `?proof` while its type is another `∃`. Returns:
      • the map of κ-mvars (`MVarId` ↦ KVars) for fusion's detection,
      • the κ-binder names in source order,
      • the residual proof goal — body of the innermost ∃, with each
        existentially-bound variable replaced by its mvar. -/
partial def peelExistentialsAndIntro (goal : MVarId) :
    MetaM (Std.HashMap MVarId KVar × List KVar × MVarId) :=
  go goal {} []
where
  go (goal : MVarId) (kvars : Std.HashMap MVarId KVar) (kvarsRev : List KVar)
    : MetaM (Std.HashMap MVarId KVar × List KVar × MVarId) := do

    let goalType ← whnf (← goal.getType)

    -- if goal is an existential: ∃ κ : α, P(κ)
    if goalType.isAppOfArity ``Exists 2 then
      let α     := goalType.getArg! 0 -- type α
      let pred  := goalType.getArg! 1 -- type P(κ)
      match pred with
      -- λ κ : α, P(κ)
      | .lam name tyBind body _ =>
        /-
          Fresh metavariable `?κ : α`, named after the binder so traces
          stay readable. This is the witness slot for the `∃`.

          It is `syntheticOpaque`: `isDefEq` never assigns such an mvar,
          treating it as an opaque constant. The residual goal `P ?κ` still
          mentions `?κ`, so without this any tactic run on that goal could
          unify `?κ` away. Only an explicit `MVarId.assign` can fill it,
          which is how fusion and PA install the computed solution.
        -/
        let κMVar ←
              mkFreshExprMVar (some α) (kind := .syntheticOpaque) (userName := name)
        /-
          Open the binder: replace the bound `κ` in `body` with `?κ`,
          giving the residual obligation `P ?κ`. Then, returns the
          new type `P ?κ`.
        -/
        let newType := body.instantiate1 κMVar

        -- `proofMVar` is a meta-variable for proof of `?k` meta-var.
        let proofMVar ← mkFreshExprMVar (some newType)

        -- Build `Exists.intro α pred ?κ ?proof` at the goal's own universe
        -- level, i.e. the proof term `⟨?κ, ?proof⟩` with two holes to fill.
        let lvls  := goalType.getAppFn.constLevels!
        let proof := mkApp4 (mkConst ``Exists.intro lvls) α pred κMVar proofMVar

        -- Assign the proof (it is sort of like a place holder)
        goal.assign proof

        -- Collect the parameter types of `κ`,
        -- i.e. for `∃ κ : Int → Int → Prop, ...` we get `pTypes = [Int, Int]`.
        let (_, pTypes) ← collectArrowTypes tyBind
        -- Canonical parameter names `z0, ..., z(n-1)` with `n = |pTypes|`, so every
        -- κ-solution is written over `κ(z0, ..., z(n-1))` regardless of how a clause
        -- names its arguments (`exprSol1` emits them, `solToWitnessExpr` binds them).
        let canonParams := (List.range pTypes.length).map fun i => Name.mkStr1 s!"z{i}"
        -- Create the `κ`-variable
        let kvar : KVar := {
          name
          params     := canonParams
          paramTypes := pTypes
          mvarId     := κMVar.mvarId!
        }

        /-
          Recurse on the residual goal `?proof : P ?κ` with this κ recorded:
          the map gains `?κ ↦ kvar`, and the list is consed (reversed once in
          the base case, so it ends up in binder order).

          Trace for `∃ k0, ∃ k1, C`:
            go ?g  {}           []        -- type `∃ k0, ∃ k1, C`
            go ?p1 {?k0}        [k0]      -- type `∃ k1, C[?k0]`
            go ?p2 {?k0, ?k1}   [k1, k0]  -- type `C[?k0, ?k1]`, not an `∃`
              ⇒ returns ({?k0, ?k1}, [k0, k1], ?p2)
        -/
        go proofMVar.mvarId!
            (kvars.insert κMVar.mvarId! kvar)
            (kvar :: kvarsRev)
      -- if goal is not existential then return.
      | _ =>
        return (kvars, kvarsRev.reverse, goal)
    else
      return (kvars, kvarsRev.reverse, goal)

  /-- Argument types of an arrow type, e.g. `Int → Int → Prop ↦ (2, [Int, Int])`.
      Each `A → B` is a `forallE` with domain `A`; take `A`, recurse into `B`,
      stop at the first non-arrow (the codomain, dropped). `whnf` first so
      aliases unfold. The `Nat` is just the list length. -/
  collectArrowTypes (ty : Expr) : MetaM (Nat × List Expr) := do
    let ty ← whnf ty
    if ty.isForall then
      let domTy := ty.bindingDomain!
      let (n, rest) ← collectArrowTypes ty.bindingBody!
      return (1 + n, domTy :: rest)
    else return (0, [])

/-- Build the witness `fun (z0 : T0) … (zₙ : Tₙ) => sol` that gets assigned to `?κ`.
    Inside `sol`, each parameter `zᵢ` is a placeholder fvar named `zᵢ`;
    `abstract` turns those placeholders into the lambda's bound variables. -/
def solToWitnessExpr (sol : Expr) (params : List Name) (paramTypes : List Expr) : MetaM Expr := do
  let body :=
    (← instantiateMVars sol).abstract (params.toArray.map fun z => mkFVar ⟨z⟩)
  return (params.zip paramTypes).foldr (fun (z, ty) b => .lam z ty b .default) body

/-- Assign κ's mvar the witness `fun z₀ ⋯ zₙ₋₁ => sol` -/
def KVar.assignSol (κ : KVar) (sol : Expr) : MetaM Unit := do
  κ.mvarId.assign (← solToWitnessExpr sol κ.params κ.paramTypes)
