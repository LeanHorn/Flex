import Flex.VCG.STLC.Tactics.Setup
import Flex.VCG.STLC.Notation
import Flex.VCG.STLC.Proofs.Soundness
import Flex.VCG.STLC.Spec.Theorems
import Flex.Tactic

open STLC


/-! # Examples — full port of pre-refactor suite, LN + deep Formula + κ

  All examples re-stated under:
  - LN binders (`Exp.lam (.bvar 0)` etc.)
  - Deep `Formula` refinements
  - κ-aware judgements (`topVC κ`, `Check [] κ`, `Hastype [] κ`)

  Programs and types are written with the surface syntax of `Notation.lean`
  (`<| … |>`, `<ty| … |>`), which elaborates to exactly these locally-nameless
  terms.

  Proofs preserve the *spirit* of the original tactics:
  `simp + solve_fixpoint`, `make_horn_under_k + solve_fixpoint`,
  `topVC_decl_sound + simp + intros`.

-/

/-! ## Refinement helpers -/

abbrev TT  : Ty := <ty| Int |>

abbrev Pos : Ty := <ty| Int{ν : 1 ≤ ν} |>

/-- `IntN n = {ν : Int | ν = n}`. -/
abbrev IntN (n : Int) : Ty := <ty| Int{ν : ν = ⌜n⌝} |>

/-- Identity function under LN. -/
abbrev exId : Exp := <| λ x, x |>

/-! ## Example 1: `5 ⇐ Pos` -/

def ex1Exp : Exp := <| 5 |>

def ex1Ty  : Ty  := Pos

example (κ : KEnv) : topVC κ [] ex1Exp ex1Ty := by
  simp only [topVC, check, synth, sub, ex1Exp, ex1Ty, Pos, prim, implyBindCstr, Ty.hyp?_int,
             if_true, Cstr.interp, Cstr.triv, Refinement.openBVar,
             Formula.openBVar, Term.openBVar, REnv.update, REnv.write,
             Refinement.interp, Formula.interp, Term.interp]
  solve_fixpoint

/-! ## Example 2: identity `λx. x ⇐ Pos → Pos` -/

def ex2Exp : Exp := exId

def ex2Ty  : Ty  := <ty| ⌜Pos⌝ -> ⌜Pos⌝ |>

set_option maxHeartbeats 800000 in
example (κ : KEnv) : topVC κ [] ex2Exp ex2Ty := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        Refinement.openBVar, Formula.openBVar, Term.openBVar, ex2Exp, exId, ex2Ty,
        Pos, self, Refinement.interp, Formula.interp, Term.interp, REnv.get,
        TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar,
        Term.openBVar]

/-! ## Example 3: `let z = 5 in z ⇐ Pos` -/

def ex3Exp : Exp := <| let z = 5 in z |>

def ex3Ty  : Ty  := Pos

example (κ : KEnv) : topVC κ [] ex3Exp ex3Ty := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        Refinement.openBVar, Formula.openBVar, Term.openBVar, ex3Exp, ex3Ty, Pos,
        prim, self, Refinement.interp, Formula.interp, Term.interp, REnv.get,
        TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv,
        Exp.openVar]

/-! ## κ-example: `let z = 99 in (λx. x : Int{k} → Int{k}) z ⇐ Pos`

  Original used `make_horn_under_k [List.lookup]; solve_fixpoint`.
  Here the κ surfaces from `Refinement.interp`'s `.kapp` case (post-stratification)
  and is discharged via the now fully-proven `check_sound` + `solve_fixpoint`. -/

@[qualif]
def Ge1 (i : Int) : Prop := 1 ≤ i

example :
    ∃ κ : KEnv,
      Check [] κ []
        <| let z = 99 in (⌜exId⌝ : Int{ν : k ν} -> Int{ν : k ν}) z |>
        Pos := by
  generate
  zap
  grind

/-! ## κ-example: same shape at `x:Int → Int{k(x, ν)}`, output type `IntN 99` -/

example :
    ∃ κ : KEnv,
      Check [] κ []
        <| let z = 99 in (⌜exId⌝ : (x : Int) -> Int{ν : k x ν}) z |>
        (IntN 99) := by
  generate
  zap
  grind

-- /-! ## Example 3 again: prove `topVC` without solver -/

example (κ : KEnv) : topVC κ [] ex3Exp ex3Ty := by
  simp [topVC, ex3Exp, ex3Ty]

/-! ## `exGt`: `λ x. λ y. let c = x ≤ y in ¬c  ⇐  TT → TT → {ν | ν = true ↔ x > y}`

  Uses `not_var`: the letin names the leq result as a fvar, then `.not (.bvar 0)` opens
  to `.not (.fvar c)` which matches the `not_var` rule. -/

abbrev exGt : Exp :=
  <| λ x y, let c = x ≤ y in ¬c |>

/-- `ν = true ↔ ¬(x ≤ y)` (`↔` unfolds to the two implications). -/
abbrev tyGt : Ty :=
  <ty| (x : Int) -> (y : Int) -> Bool{ν : ν = true ↔ ¬(x ≤ y)} |>

example (κ : KEnv) : topVC κ [] exGt tyGt := by
  simp [topVC, exGt, tyGt]

/-! ## `exEq`: `λ x. λ y. let u = x ≤ y in let v = y ≤ x in u ∧ v`
                                             `⇐  TT → TT → {ν | ν = true ↔ x = y}`

  Uses `and_var`: both letin-bound booleans become fvars, then `.and (.bvar 1) (.bvar 0)`
  opens to `.and (.fvar u) (.fvar v)` which matches the `and_var` rule. -/

abbrev exEq : Exp :=
  <| λ x y, let u = x ≤ y in let v = y ≤ x in u ∧ v |>

/-- `ν = true ↔ (x ≤ y ∧ y ≤ x)`, i.e. x = y. -/
abbrev tyEq : Ty :=
  <ty| (x : Int) -> (y : Int) -> Bool{ν : ν = true ↔ (x ≤ y ∧ y ≤ x)} |>

example (κ : KEnv) : topVC κ [] exEq tyEq := by
  simp [topVC, exEq, tyEq]
  solve_fixpoint

/-! ## `exMax`: `λx. λy. let c = x ≤ y in if c then y else x`. -/


abbrev exMax : Exp :=
  <| λ x y, let c = x ≤ y in if c then y else x |>

/-! ## κ flagship: `let a = 99 in let b = 100 in exMax a b ⇐ {ν | ν = 100 ∨ ν = 99}` -/

example :
    ∃ κ : KEnv,
      Check [] κ []
        <| let a = 99 in let b = 100 in
           (⌜exMax⌝ : (x : Int) -> (y : Int) -> Int{ν : k x y ν}) a b |>
        <ty| Int{ν : ν = 100 ∨ ν = 99} |> := by
  generate
  zap
  grind

/-! ## Arithmetic: `let a = 3 in let b = 4 in a + b ⇐ IntN 7` -/

def exAddExp : Exp :=
  <| let a = 3 in let b = 4 in a + b |>

def exAddTy : Ty := IntN 7

example (κ : KEnv) : topVC κ [] exAddExp exAddTy := by
  simp [topVC, exAddExp, exAddTy]

/-! ## `unreachable`: a dead `else`-branch typechecks via ex falso

  `λ x. let z = 0 in let c = x ≤ z in if c then 1 else unreachable`
  at `{ν:Int | ν ≤ 0} → Pos`.

  The `else` branch's context binds `x ≤ 0` (the param refinement), `z = 0`,
  `c ↔ (x ≤ z)`, and the path condition `c = false`. Since `x ≤ 0 ∧ z = 0`
  forces `x ≤ z`, the `c ↔ (x ≤ z)` hypothesis then forces `c = true`,
  contradicting `c = false` — so the branch context is unsatisfiable and
  `unreach` typechecks there at *any* result type, including `Pos`. -/

abbrev exUnreachable : Exp :=
  <| λ x, let z = 0 in let c = x ≤ z in if c then 1 else unreachable |>

abbrev tyUnreachable : Ty :=
  <ty| Int{ν : ν ≤ 0} -> Int{ν : 1 ≤ ν} |>

example (κ : KEnv) : topVC κ [] exUnreachable tyUnreachable := by
  simp [topVC]

-- Declarative-side: `unreach` is directly derivable from a contradictory `Entail`.
example (κ : KEnv) (Γ : TEnv) (t : Ty)
    (h : Entail κ Γ (fun _ => False)) (hwf : Ty.WFBVars t) :
    Hastype [] κ Γ .unreach t := .unreach h hwf

-- Sanity check: `unreach` genuinely gets stuck — it has no `Eval` rule, not
-- even a timeout, at any fuel.
example (n : Nat) : ¬ ∃ o, Eval n .unreach o := by
  rintro ⟨o, ho⟩
  cases ho

/-! ## Declarative-side examples (via `topVC_decl_sound`) -/

-- Identity (λx. x) is declaratively typeable at Pos → Pos.
example (κ : KEnv) : Hastype [] κ [] ex2Exp ex2Ty := by
  apply topVC_decl_sound
    <;> simp [topVC, ex2Exp, exId, ex2Ty, Pos]
  · simp [Exp.WFBVars]
  · unfold Ty.WFBVars
    simp [Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]



-- let z = 5 in z is declaratively typeable at Pos.
example (κ : KEnv) : Hastype [] κ [] ex3Exp ex3Ty := by
  apply topVC_decl_sound <;>
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        Refinement.openBVar, Formula.openBVar, Term.openBVar, ex3Exp, ex3Ty, Pos,
        prim, self, Refinement.interp, Formula.interp, Term.interp, REnv.get,
        Exp.openVar, Exp.WFBVars, Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar,
        Formula.hasBVar, Term.hasBVar]

/-! ## Declarative-side: direct constructor derivations -/

example (κ : KEnv) : Hastype [] κ [] (.iconst 5) (prim 5) := .int_const

example (κ : KEnv) : Hastype [] κ [] (.bconst true) (primBool true) := .bool_const

example (κ : KEnv) : Hastype [] κ [] (.ann (.iconst 5) (prim 5)) (prim 5) := by
  constructor
  constructor
  simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]

example (κ : KEnv) (Γ : TEnv) (x y : EVar) (r₁ r₂ : Refinement)
    (hx : Γ.lookup x = some (.refine .int r₁))
    (hy : Γ.lookup y = some (.refine .int r₂)) :
    Hastype [] κ Γ (.add (.fvar x) (.fvar y))
      (.refine .int (.fmla (.eq .int (.bvar .int 0)
                          (.add (.fvar .int x) (.fvar .int y))))) := by
  apply Hastype.add_var <;> assumption


/-! ## Recursive functions (`Exp.fix`)

  `Exp.fix body` is the recursive function `fix f. λx. body`, where inside
  `body` `BVar 1` is the self-reference `f` and `BVar 0` is the parameter `x`.
  The body is checked assuming `f` already has the annotated type
  (assume–guarantee, Chapter 4), so these specs are *partial* correctness
  guarantees. The book's `rec f = e₁ : t in e₂` is `letin (ann (fix e₁) t) e₂`,
  written `let f : t = fix f x, … in e₂`.
-/

/-- `sum : n:Int → {ν : 0 ≤ ν ∧ n ≤ ν}` (in the codomain, `BVar 1` is `n`). -/
def sumTy : Ty :=
  <ty| (n : Int) -> Int{ν : 0 ≤ ν ∧ n ≤ ν} |>

/-- `sum` (there is no `sub`, so `n - 1` is `n + m` with `m = -1`). -/
def sumE : Exp :=
  <| fix sum n,
       let z = 0 in let c = n ≤ z in
       if c then 0
       else let m = -1 in let n1 = n + m in let t1 = sum n1 in n + t1 |>

/-- `sum` meets its spec. -/
example (κ : KEnv) : topVC κ [] sumE sumTy := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        sumE, sumTy, self, prim, Refinement.interp, Formula.interp, Term.interp, REnv.get,
        TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv, Exp.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar, Term.openBVar]
  intros; omega

/-- A client, via the `rec` encoding: `rec sum = … : sumTy in sum 5 ⇐ {ν : 5 ≤ ν}`. -/
def sumClient : Exp :=
  <| let sum : ⌜sumTy⌝ = ⌜sumE⌝ in let five = 5 in sum five |>

example (κ : KEnv) :
    topVC κ [] sumClient <ty| Int{ν : 5 ≤ ν} |> := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        sumClient, sumE, sumTy, self, prim, Refinement.interp, Formula.interp, Term.interp,
        REnv.get, TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv, Exp.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar, Term.openBVar]
  intros; omega

/-! ### Partial correctness: a diverging function

  `loop = fix f. λx. f x` checks against `Int → {ν : false}`: the type promises
  nothing about termination. Safety then says the only way to run `loop 0`
  without getting stuck is to time out — at *every* fuel budget. -/

def loopTy : Ty := <ty| Int -> Int{ν : ⊥} |>

def loop : Exp := <| fix f x, f x |>

example (κ : KEnv) : topVC κ [] loop loopTy := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        loop, loopTy, self, Refinement.interp, Formula.interp, Term.interp,
        REnv.get, TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv, Exp.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar, Term.openBVar]

/-- `rec loop = … : loopTy in loop 0`. -/
def loopMain : Exp :=
  <| let loop : ⌜loopTy⌝ = ⌜loop⌝ in let zero = 0 in loop zero |>

theorem loopMain_vc (κ : KEnv) : topVC κ [] loopMain <ty| Int{ν : ⊥} |> := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        loopMain, loop, loopTy, self, prim, Refinement.interp, Formula.interp, Term.interp,
        REnv.get, TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv, Exp.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar, Term.openBVar]

/-- By `vcgen_partial_correct`, `loop 0` never returns a value, whatever the fuel. -/
example (n : Nat) : ¬ ∃ v m, Run n loopMain (.val v m) := by
  rintro ⟨v, m, hev⟩
  obtain ⟨_, hr⟩ := vcgen_partial_correct (κ := fun _ _ => True) rfl
    (by simp [loopMain, loop, loopTy, Exp.WFBVars, Ty.WFBVars, Ty.WFBVarCtx,
              Refinement.hasBVar, Formula.hasBVar])
    (by simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar])
    (loopMain_vc _) hev
  simp [Refinement.interp, Formula.interp] at hr

/-! ### Recursion + refinement inference: `sum` with an inferred spec

  Same `sum` body, but now its output refinement is a κ-hole:
  `sum : n:Int → {ν | k(n, ν)}`. Only the *client* states what it needs,
  `sum 5 ≥ 5`. Because `sum` calls itself, the Horn constraints are recursive
  (κ appears on both sides of the recursive-call clause):

    n ≤ 0                    → k(n, 0)          -- base case
    n ≥ 1 ∧ k(n - 1, t₁)     → k(n, n + t₁)     -- recursive call
    k(5, v)                  → 5 ≤ v            -- client

  so κ is *cyclic*: fusion (`zap`) cannot eliminate it, and we solve it by
  predicate abstraction (Houdini, the `fix` tactic) over the `@[qualif]`s below. It infers the
  inductive invariant `k(n, ν) := 0 ≤ ν ∧ n ≤ ν`. (`n ≤ ν` alone already
  suffices — it is inductive because the recursive call only happens when
  `n ≥ 1` — whereas `0 ≤ ν` alone cannot establish the client's `5 ≤ v`; and
  the false client claim `16 ≤ sum 5` is rejected.) -/

@[qualif] def QGe0 (a : Int) : Prop := 0 ≤ a

@[qualif] def QLe (a b : Int) : Prop := a ≤ b

/-- `sum : n:Int → {ν | k(n, ν)}`: output refinement left for the solver. -/
abbrev sumTyK : Ty := <ty| (n : Int) -> Int{ν : k n ν} |>

theorem sum_infer :
    ∃ κ : KEnv,
      Check [] κ []
        <| let sum : ⌜sumTyK⌝ = ⌜sumE⌝ in let five = 5 in sum five |>
        <ty| Int{ν : 5 ≤ ν} |> := by
  simp only [sumE]
  generate
  fix

/-! ## Type polymorphism (λ_RF-style)

  `Exp.tabs k e` is `Λα:k. e` and `Exp.tapp e τ` is `e[τ]`; inside a polymorphic
  type `α` is `Base.tbvar 0`. Kinds: `B` variables may be refined and are
  instantiated with refined base types; `⋆` variables are refined only with
  `true` and may be instantiated with anything — including polymorphic types
  (impredicativity). Instances are written explicitly, with κ-templates for the
  refinements to infer. Instantiating `α{r}` at `b{r'}` yields `b{r' ∧ r}`. -/

attribute [local simp] Exp.ftv Ty.ftv Refinement.ftv Formula.ftv Term.ftv Base.ftv TEnv.ftv TVar.fresh
  Exp.openTv Ty.openTv Refinement.substB Formula.substB Term.substB Base.substB BSubst.openAt
  BSubst.instAt Ty.instTy Ty.strengthen Ty.sortOf Ty.kindOf Kind.le Ty.wfB Refinement.wfB
  Formula.wfB Term.wfB Base.isTv Base.sortOK Base.fvOK Base.tyOK Base.isStarB Refinement.isTT
  Ty.optBase Base.shiftT

/-! ### `id : ∀α:B. x:α → α{ν = x}` — refinement strengthening at instantiation -/

abbrev idTy : Ty := <ty| ∀ α : B, (x : α) -> α{ν : ν = x} |>

abbrev idPoly : Exp := <| Λ α : B, λ x, x |>

theorem poly_id (κ : KEnv) : topVC κ [] idPoly idTy := by
  simp [topVC, idPoly, idTy]

/-- `let five = 5 in id[int{k}] five ⇐ {ν = 5}`: the instance's result type is
    `int{k(ν) ∧ ν = five}` — the `ν = x` of `id`'s signature is conjoined into
    the instance, so any `k` admitting `5` works. -/
theorem poly_id_client : ∃ κ : KEnv, Check [] κ []
    <| let five = 5 in (⌜idPoly⌝ : ⌜idTy⌝)[Int{ν : k ν}] five |>
    (IntN 5) := by
  generate
  zap
  grind

/-! ### The book's §6.1 client, with `choose : ∀α:B. Bool → α → α → α`

  (`max` would need a polymorphic `≤`; our `leq` primitive is `Int`-only.) The
  instance refinement `k` is inferred: it must admit `0` and `5` and give
  `0 < r + 1`. -/

abbrev chooseTy : Ty := <ty| ∀ α : B, Bool -> α -> α -> α |>

abbrev choosePoly : Exp := <| Λ α : B, λ c x y, if c then x else y |>

theorem poly_choose (κ : KEnv) : topVC κ [] choosePoly chooseTy := by
  simp [topVC, choosePoly, chooseTy]

/-- `λc. let z = 0; let f = 5; let r = choose[int{k}] c z f; let one = 1; r + one`
    `⇐ Bool → {0 < ν}`. -/
theorem poly_choose_client : ∃ κ : KEnv, Check [] κ []
    <| λ c, let z = 0 in let f = 5 in
         let r = (⌜choosePoly⌝ : ⌜chooseTy⌝)[Int{ν : k ν}] c z f in
         let one = 1 in r + one |>
    <ty| Bool -> Int{ν : 1 ≤ ν} |> := by
  generate
  zap
  grind

/-! ### Impredicative instantiation: `idF[∀β:⋆. β → β] idF` -/

abbrev idFTy : Ty := <ty| ∀ α : ⋆, α -> α |>

abbrev idF : Exp := <| Λ α : ⋆, λ x, x |>

theorem poly_impredicative (κ : KEnv) : topVC κ []
    <| let idF : ⌜idFTy⌝ = ⌜idF⌝ in idF[∀ β : ⋆, β -> β] idF |> idFTy := by
  simp [topVC, idF, idFTy]

/-! ### Polymorphism + recursion + inference: `iter : ∀α:⋆. (α → α) → Int → α → α`

  `iter f n x` applies `f` to `x` `n` times. Instantiated at `int{k}` and used
  with `inc` from `0`, the instance refinement `k` must be an *invariant* of
  `inc` — a cyclic κ, solved by predicate abstraction (`fix`), which infers
  `k(ν) := 0 ≤ ν`. -/

abbrev iterTy : Ty := <ty| ∀ α : ⋆, (α -> α) -> Int -> α -> α |>

abbrev iterPoly : Exp :=
  <| Λ α : ⋆, fix iter f, λ n x,
       let z = 0 in let c = n ≤ z in
       if c then x
       else let m = -1 in let n1 = n + m in let fx = f x in
            let g1 = iter f in let g2 = g1 n1 in g2 fx |>

theorem poly_iter (κ : KEnv) : topVC κ [] iterPoly iterTy := by
  simp [topVC, iterPoly, iterTy]

/-- `inc : x:Int → {ν = x + 1}` -/
abbrev incTy : Ty := <ty| (x : Int) -> Int{ν : ν = x + 1} |>

abbrev incE : Exp := <| λ x, let one = 1 in x + one |>

/-- `let inc = …; let three = 3; let zero = 0; iter[int{k}] inc three zero ⇐ {0 ≤ ν}`. -/
theorem poly_iter_client : ∃ κ : KEnv, Check [] κ []
    <| let inc : ⌜incTy⌝ = ⌜incE⌝ in let three = 3 in let zero = 0 in
       let g = (⌜iterPoly⌝ : ⌜iterTy⌝)[Int{ν : k ν}] inc in
       let h = g three in h zero |>
    <ty| Int{ν : 0 ≤ ν} |> := by
  generate
  fix

/-! ### Type arguments may mention program variables

  `λn. let m = n in id[Int{n ≤ ν}] m ⇐ n:Int → Int{n ≤ ν}`: the instance refers
  to the enclosing binder `n`. The argument is rebound because the application
  rule requires it not to occur in the result type, which now mentions `n`. -/

theorem poly_tapp_var (κ : KEnv) : topVC κ []
    <| λ n, let m = n in (⌜idPoly⌝ : ⌜idTy⌝)[Int{ν : n ≤ ν}] m |>
    <ty| (n : Int) -> Int{ν : n ≤ ν} |> := by
  simp [topVC, idPoly, idTy]
  intros; omega

/-! ### Polymorphic recursion

  `nest : ∀α:⋆. α → Int → Nat` calls itself at the instance `Int → α`: its own
  name is generalized over `α` inside its body (`Check.fix`), which the VC
  generator does because the body type-applies it. -/

attribute [local simp] TEnv.genVars Ty.closeTv BSubst.closeAt List.eraseDups_cons

abbrev nestTy : Ty := <ty| ∀ α : ⋆, α -> Int -> Int{ν : 0 ≤ ν} |>

abbrev nestE : Exp :=
  <| Λ α : ⋆, fix f x, λ n,
       let z = 0 in let c = n ≤ z in
       if c then z
       else let g = ((λ _, x) : Int -> α) in let m1 = -1 in let m = n + m1 in
            let h = f[Int -> α] g in h m |>

theorem poly_nest (κ : KEnv) : topVC κ [] nestE nestTy := by
  simp [topVC]

/-- With a monomorphic recursive call `f g m`, the argument `g : Int → α` is not
    an `α`: rejected. -/
abbrev nestMonoE : Exp :=
  <| Λ α : ⋆, fix f x, λ n,
       let z = 0 in let c = n ≤ z in
       if c then z
       else let g = ((λ _, x) : Int -> α) in let m1 = -1 in let m = n + m1 in
            let h = f g in h m |>

theorem poly_nest_mono_bad (κ : KEnv) : ¬ topVC κ [] nestMonoE nestTy := by
  simp [topVC]
