import Flex.VCG.STLC.Soundness
import Flex.Tactic

-- Applies `under_exists` once, then dispatches `check_sound` inside it.
-- `args` (optional, default empty) are extra lemmas passed to `simp`.
macro "make_horn_under_k" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    under_exists =>
      apply check_sound
      · repeat (first | unfold check | unfold synth)
        simp [$args,*]; rfl
      focus simp)

macro "make_horn_under_k" : tactic => `(tactic| make_horn_under_k [])

/-- Transform `⊢ ∃ κ : KEnv, P κ` into a goal where `κ` is replaced by
    `mkKEnv [...]`, with each listed predicate left as its own metavariable.

    Usage:
    ```
    intro_kenv [("k1", liftKPred 1 ?k1), ("k2", liftKPred 2 ?k2)]
    · exact fun v => v = 99        -- fills ?k1
    · exact fun x y => x = y      -- fills ?k2
    · <proof of P (mkKEnv [...])>
    ``` -/
macro "intro_kenv" "[" es:term,* "]" : tactic =>
  `(tactic| apply STLC.exists_kenv_curried [$es,*])

section KEnvTactic
open Lean Elab Tactic Meta

private partial def countCons (e : Expr) : Nat :=
  if e.isAppOfArity `List.cons 3 then 1 + countCons e.appArg! else 0

private partial def collectKVarUses
    (κFVar : FVarId) (e : Expr) (acc : List (String × Nat)) : List (String × Nat) :=
  match e with
  | .app (.app (.fvar fv) (.lit (.strVal name))) args =>
    let acc' := if fv == κFVar && !acc.any (fun p => p.1 == name)
                then (name, countCons args) :: acc else acc
    collectKVarUses κFVar args acc'
  | .app f a =>
    collectKVarUses κFVar a (collectKVarUses κFVar f acc)
  | .lam _ t b _ | .forallE _ t b _ =>
    collectKVarUses κFVar b (collectKVarUses κFVar t acc)
  | .letE _ t v b _ =>
    collectKVarUses κFVar b (collectKVarUses κFVar v (collectKVarUses κFVar t acc))
  | .mdata _ e => collectKVarUses κFVar e acc
  | _ => acc

-- `intro_kenv`: scans `∃ κ : KEnv, body` for every `κ "name" args` application,
-- infers arities, and rewrites the goal to
-- `∃ (k1 : Int → Prop) ..., body[κ := mkKEnv [...]]`.
elab "intro_kenv" : tactic => do
  let goal ← getMainGoal
  let goalType ← whnf (← goal.getType)
  unless goalType.isAppOfArity ``Exists 2 do
    throwError "intro_kenv: goal must be `∃ κ : KEnv, ...`"
  let bodyFn := goalType.appArg!
  let .lam _ kenvTy innerBody _ := bodyFn
    | throwError "intro_kenv: expected lambda in ∃ body"
  withLocalDecl `κ₀ .default kenvTy fun κ₀ => do
    let openBody ← instantiateMVars (innerBody.instantiate1 κ₀)
    let kvars := collectKVarUses κ₀.fvarId! openBody []
    if kvars.isEmpty then
      throwError "intro_kenv: no κ-applications found; use `intro_kenv [...]` explicitly"
    let kvarArr := kvars.toArray
    let intTy  := mkConst ``Int
    let propTy := mkSort Level.zero
    -- Build `Int → Int → … → Int → Prop` (n times) for any arity n.
    let kPredTy : Nat → Expr := fun n =>
      (List.range n).foldr (fun _ acc => .forallE `_ intTy acc .default) propTy

    -- Fresh MVars for each k-predicate
    let kMVars ← kvarArr.mapM fun (name, arity) =>
      mkFreshExprMVar (kPredTy arity) (kind := .natural) (userName := name.toName)

    -- Build list [("k1", liftKPred n1 ?k1), ...] using direct mkApp (no AppBuilder).
    -- `liftKPred n` has type `KPred n → List (Σ b, b.interp) → Prop`; since
    -- `KPred n` is @[reducible] to `Int → … → Int → Prop`, it unifies with our MVars.
    let liftKPredC := mkConst ``STLC.liftKPred
    let mkLifted (arity : Nat) (kMVar : Expr) : Expr :=
      mkApp2 liftKPredC (mkNatLit arity) kMVar
    let lifted0  := mkLifted kvarArr[0]!.2 kMVars[0]!
    let liftedTy ← inferType lifted0          -- List (Σ b, b.interp) → Prop
    let strTy    := mkConst ``String
    -- Prod.mk.{u,v} takes universe indices where α : Type u.
    -- String : Type 0 → u = 0;  liftedTy : Type 0 → v = 0.
    let prodMkC  := mkConst ``Prod.mk [Level.zero, Level.zero]
    let elem0    := mkApp4 prodMkC strTy liftedTy (mkStrLit kvarArr[0]!.1) lifted0
    let elemTy   ← inferType elem0             -- KVar × (List ... → Prop)
    -- List.{u} (α : Type u): α : Type 0 → u = 0.
    let nilC  := mkConst ``List.nil  [Level.zero]
    let consC := mkConst ``List.cons [Level.zero]
    let mut kenvListExpr := mkApp nilC elemTy
    for i in (List.range kvarArr.size).reverse do
      let (name, arity) := kvarArr[i]!
      let liftedKi := mkLifted arity kMVars[i]!
      let elem := mkApp4 prodMkC strTy liftedTy (mkStrLit name) liftedKi
      kenvListExpr := mkApp3 consC elemTy elem kenvListExpr
    let kenvExpr := mkApp (mkConst ``STLC.mkKEnv) kenvListExpr

    -- Fresh MVar for the body proof P(mkKEnv [...])
    let mainGoalType := innerBody.instantiate1 kenvExpr
    let mainGoalMVar ← mkFreshExprMVar mainGoalType (kind := .natural)

    -- Compute the universe level of kenvTy (needed for Exists.intro level arg)
    let kenvLvl : Level ← do
      match ← whnf (← inferType kenvTy) with
      | .sort u => pure u
      | srt => throwError "intro_kenv: unexpected KEnv sort {srt}"
    -- Exists.{u} / Classical.choose.{u} : {α : Sort u} → ...
    -- kPredTy is Int → Prop or Int → Int → Prop, both in Sort 1 = Type 0.
    let kLvl : Level := Level.succ Level.zero

    -- Close original goal via Exists.intro with explicit level (bypasses AppBuilder)
    let exIntroC := mkConst ``Exists.intro [kenvLvl]
    goal.assign (mkApp4 exIntroC kenvTy bodyFn kenvExpr mainGoalMVar)

    -- Build ∃ k1 k2 ... goal by abstracting each kMVar out of mainGoalType
    let existsC := mkConst ``Exists [kLvl]
    let mut newTarget := mainGoalType
    for i in (List.range kvarArr.size).reverse do
      let (name, arity) := kvarArr[i]!
      let kTy      := kPredTy arity
      let abstBody ← kabstract newTarget kMVars[i]! (occs := .all)
      newTarget := mkApp2 existsC kTy (mkLambda name.toName .default kTy abstBody)

    -- Create the final ∃ k1 k2 ... goal MVar
    let decl ← mainGoalMVar.mvarId!.getDecl
    let finalGoalMVar ← mkFreshExprMVarAt decl.lctx decl.localInstances newTarget

    -- Extract k-witnesses and body proof via Classical.choose chain
    let chooseC     := mkConst ``Classical.choose     [kLvl]
    let chooseSpecC := mkConst ``Classical.choose_spec [kLvl]
    let mut specProof : Expr := finalGoalMVar
    for i in [:kvarArr.size] do
      let kTy  := kPredTy kvarArr[i]!.2
      let pred := (← whnf (← inferType specProof)).appArg!
      kMVars[i]!.mvarId!.assign (mkApp3 chooseC     kTy pred specProof)
      specProof :=                mkApp3 chooseSpecC kTy pred specProof
    mainGoalMVar.mvarId!.assign specProof

    replaceMainGoal [finalGoalMVar.mvarId!]

end KEnvTactic

/-- `vc_generate` — discharge the soundness bridge under the `∃ κ`, turning
    `∃ κ, Check κ Γ e T` into its verification conditions (a CHC goal over `κ`). -/
macro "vc_generate" : tactic =>
  `(tactic|
    under_exists =>
      apply check_sound
      simp ; rfl
      simp)

/-- `vc_reify` — reify the single `KEnv` into typed per-κ unknowns (arities
    inferred automatically) and normalize the environment lookups, leaving a
    clean curried CHC goal. Handles any arity via `liftKPred`. -/
macro "vc_reify" : tactic =>
  `(tactic| intro_kenv <;> simp [STLC.mkKEnv, List.lookup, STLC.liftKPred,
                                  STLC.liftKPred_zero, STLC.liftKPred_succ_int])

/-! ## Splitting a verification condition on the sorts it reads

  A verification condition for polymorphic code reads a `B`-kinded type
  variable `a` at the base `γ.sorts.fv a` it stands for, which is either `Int`
  or `Bool`. `split_sorts` case-splits every such base, leaving ordinary `Int`
  and `Bool` goals. -/

section SplitSorts
open Lean Elab Tactic Meta

/-- The first read of a type-variable sort, `σ.fv a`, in `e` (outside binders). -/
private partial def findSortRead (e : Expr) : Option Expr :=
  if e.isAppOfArity ``STLC.SortEnv.fv 2 && !e.hasLooseBVars then some e else
  match e with
  | .app f a => (findSortRead f).orElse fun _ => findSortRead a
  | .lam _ t b _ | .forallE _ t b _ => (findSortRead t).orElse fun _ => findSortRead b
  | .letE _ t v b _ =>
    ((findSortRead t).orElse fun _ => findSortRead v).orElse fun _ => findSortRead b
  | .mdata _ e => findSortRead e
  | _ => none

/-- Case-split one type-variable sort read in the goal. -/
elab "split_sort" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := findSortRead t | throwError "split_sort: no type-variable sort is read"
  let (fvs, g') ← g.generalize #[{ expr := e, xName? := `s }]
  let gs ← g'.cases fvs[0]!
  replaceMainGoal (gs.toList.map (·.mvarId))

end SplitSorts

/-- Introduce the environment and split every type-variable sort it reads. -/
macro "split_sorts" : tactic =>
  `(tactic| (intro γ; repeat' split_sort; all_goals dsimp only))
