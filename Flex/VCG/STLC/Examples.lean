import Flex.VCG.STLC.VCGen
import Flex.VCG.STLC.Declarative
import Flex.Tactic
import Flex.VCG.STLC.Soundness
import Flex.VCG.STLC.MakeHornUnderK
import Flex.VCG.STLC.Safety

open STLC

/-! # Examples — full port of pre-refactor suite, LN + deep Formula + κ

  All examples re-stated under:
  - LN binders (`Exp.lam (.bvar 0)` etc.)
  - Deep `Formula` refinements
  - κ-aware judgements (`topVC κ`, `Check [] κ`, `Hastype [] κ`)

  Proofs preserve the *spirit* of the original tactics:
  `simp + solve_fixpoint`, `make_horn_under_k + solve_fixpoint`,
  `topVC_decl_sound + simp + intros`.

-/

/-! ## Refinement helpers -/

abbrev TT  : Ty := <ty| Int{ν : ⊤}|>

abbrev Pos : Ty :=  <ty| Int{ν : 1 ≤ ν}|>

/-- `IntN n = {ν : Int | ν = n}`. -/
abbrev IntN (n : Int) : Ty := <ty| Int{ν : ν = ⌜n⌝}|>

/-- κ-refinement on int: `{ν : Int | k(ν)}` for κ-symbol `k`. -/
abbrev IntK (k : STLC.KVar) : Ty :=
  .refine .int (.kapp k [⟨.int, .bvar .int 0⟩])

/-- κ-refinement on int: `{ν | k(x, y, ν)}` for the two enclosing arrow binders.
    `bvar 2` = x (outer arg), `bvar 1` = y (inner arg), `bvar 0` = ν. -/
abbrev IntK3 (k : STLC.KVar) : Ty :=
  .refine .int (.kapp k [⟨.int, .bvar .int 2⟩, ⟨.int, .bvar .int 1⟩, ⟨.int, .bvar .int 0⟩])

/-- κ-refinement on int referencing both an outer variable and ν: `{ν | k(x, ν)}`.
    `x` is the enclosing arrow binder (`BVar 1`, since ν occupies `BVar 0`). -/
abbrev IntR (k : STLC.KVar) : Ty :=
  .refine .int (.kapp k [⟨.int, .bvar .int 1⟩, ⟨.int, .bvar .int 0⟩])

/-- Identity function under LN. -/
abbrev exId : Exp := .lam (.bvar 0)

/-- Function type for identity at `IntK k → IntK k`. -/
abbrev ty_k (k : STLC.KVar) : Ty := .arrow (IntK k) (IntK k)

/-- Function type for `TT → IntR x k`. -/
abbrev ty_xk (k : STLC.KVar) : Ty := .arrow TT (IntR k)

/-! ## Example 1: `5 ⇐ Pos` -/

def ex1Exp : Exp := .iconst 5
def ex1Ty  : Ty  := Pos

example (κ : KEnv) : topVC κ [] ex1Exp ex1Ty := by
  simp only [topVC, check, synth, sub, ex1Exp, ex1Ty, Pos, prim, implyBindCstr, Ty.hyp?_int,
             if_true, Cstr.interp, Cstr.triv, Refinement.openBVar,
             Formula.openBVar, Term.openBVar, REnv.update, REnv.write,
             Refinement.interp, Formula.interp, Term.interp]
  solve_fixpoint

/-! ## Example 2: identity `λx. x ⇐ Pos → Pos` -/

def ex2Exp : Exp := exId
def ex2Ty  : Ty  := .arrow Pos Pos

set_option maxHeartbeats 800000 in
example (κ : KEnv) : topVC κ [] ex2Exp ex2Ty := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        Refinement.openBVar, Formula.openBVar, Term.openBVar, ex2Exp, exId, ex2Ty,
        Pos, self, Refinement.interp, Formula.interp, Term.interp, REnv.get,
        TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar,
        Term.openBVar]

/-! ## Example 3: `let z = 5 in z ⇐ Pos` -/

def ex3Exp : Exp := .letin (.iconst 5) (.bvar 0)
def ex3Ty  : Ty  := Pos

example (κ : KEnv) : topVC κ [] ex3Exp ex3Ty := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        Refinement.openBVar, Formula.openBVar, Term.openBVar, ex3Exp, ex3Ty, Pos,
        prim, self, Refinement.interp, Formula.interp, Term.interp, REnv.get,
        TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv,
        Exp.openVar]

/-! ## κ-example with `ty_k`: `let z = 99 in (λx. x : IntK k → IntK k) z ⇐ Pos`

  Original used `make_horn_under_k [List.lookup]; solve_fixpoint`.
  Here the κ surfaces from `Refinement.interp`'s `.kapp` case (post-stratification)
  and is discharged via the now fully-proven `check_sound` + `solve_fixpoint`. -/

attribute [simp] check synth sub EVar.fresh implyBindCstr prim self Refinement.interp Formula.interp TEnv.dom
attribute [simp] Cstr.interp Cstr.triv Refinement.openBVar Formula.openBVar Term.openBVar REnv.update REnv.write
attribute [simp] Term.interp REnv.get Exp.openVar Ty.openVar Exp.fv Refinement.fv Formula.fv Term.fv Ty.fv
attribute [simp] Refinement.openBVar Formula.openBVar Term.openBVar String.length EVar.maxLen
attribute [simp] List.lookup TEnv.tyFv
attribute [simp] DataDecl.ctors Ty.tuple DEnv.ctorRefine DEnv.nFields DEnv.fields? Exp.tupleVarsN
  DEnv.ctorFacts DEnv.ctorMeasures DataDecl.ctorMeasures DEnv.altTy Exp.var? Ty.strengthenLast
  DEnv.caseFacts Formula.conjAll MBody.toTerm DEnv.measEqs DEnv.measNames

macro "generate" : tactic => `(tactic| (vc_generate ; all_goals vc_reify))

@[qualif]
def Ge1 (i : Int) : Prop := 1 ≤ i

example :
    ∃ κ : KEnv,
      Check [] κ []
        (.letin (.iconst 99) (.app (.ann exId (ty_k "k")) (.bvar 0)))
        Pos := by
  generate
  zap
  grind

/-! ## κ-example with `ty_xk`: same shape, output type `IntN 99` -/

example :
    ∃ κ : KEnv,
      Check [] κ []
        (.letin (.iconst 99) (.app (.ann exId (ty_xk "k")) (.bvar 0)))
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
  .lam (.lam (.letin (.leq (.bvar 1) (.bvar 0)) (.not (.bvar 0))))

/-- `ν = true ↔ ¬(x ≤ y)`, using bvars for the two arrow-bound ints. ν is
    `BVar 0`, so the inner arg `y` is `BVar 1` and the outer arg `x` is `BVar 2`. -/
abbrev tyGt : Ty :=
  .arrow TT (.arrow TT
    (.refine .bool (.fmla (.and
      (.imp (.eq .bool (.bvar .bool 0) (.const .bool true))
            (.not (.leqI (.bvar .int 2) (.bvar .int 1))))
      (.imp (.not (.leqI (.bvar .int 2) (.bvar .int 1)))
            (.eq .bool (.bvar .bool 0) (.const .bool true)))))))

example (κ : KEnv) : topVC κ [] exGt tyGt := by
  simp [topVC, exGt, tyGt]

/-! ## `exEq`: `λ x. λ y. let u = x ≤ y in let v = y ≤ x in u ∧ v`
                                             `⇐  TT → TT → {ν | ν = true ↔ x = y}`

  Uses `and_var`: both letin-bound booleans become fvars, then `.and (.bvar 1) (.bvar 0)`
  opens to `.and (.fvar u) (.fvar v)` which matches the `and_var` rule. -/

abbrev exEq : Exp :=
  .lam (.lam
    (.letin (.leq (.bvar 1) (.bvar 0))       -- let u = x ≤ y
      (.letin (.leq (.bvar 1) (.bvar 2))     -- let v = y ≤ x
        (.and (.bvar 1) (.bvar 0)))))         -- u ∧ v

/-- `ν = true ↔ (x ≤ y ∧ y ≤ x)`, i.e. x = y. ν is `BVar 0`, so the inner arg
    `y` is `BVar 1` and the outer arg `x` is `BVar 2`. -/
abbrev tyEq : Ty :=
  .arrow TT (.arrow TT
    (.refine .bool (.fmla (.and
      (.imp (.eq .bool (.bvar .bool 0) (.const .bool true))
            (.and (.leqI (.bvar .int 2) (.bvar .int 1))
                  (.leqI (.bvar .int 1) (.bvar .int 2))))
      (.imp (.and (.leqI (.bvar .int 2) (.bvar .int 1))
                  (.leqI (.bvar .int 1) (.bvar .int 2)))
            (.eq .bool (.bvar .bool 0) (.const .bool true)))))))

example (κ : KEnv) : topVC κ [] exEq tyEq := by
  simp [topVC, exEq, tyEq]
  solve_fixpoint

/-! ## `exMax`: `λx. λy. let c = x ≤ y in if c then y else x`. -/


abbrev exMax : Exp :=
  .lam       -- λ x.
    (.lam    -- λ y.
      (.letin (.leq (.bvar 1) (.bvar 0))    -- let c = x ≤ y
        (.ite (.bvar 0)                      -- in if c
              (.bvar 1)                      -- then y
              (.bvar 2))))                   -- else x

/-! ## κ flagship: `let a = 99 in let b = 100 in exMax a b ⇐ {ν | ν = 100 ∨ ν = 99}` -/

example :
    ∃ κ : KEnv,
      Check [] κ []
        (.letin (.iconst 99)
          (.letin (.iconst 100)
            (.app (.app (.ann exMax
                          (.arrow TT
                            (.arrow TT (IntK3 "k"))))
                        (.bvar 1)) (.bvar 0))))
        (.refine .int (.fmla (.or
          (.eq .int (.bvar .int 0) (.const .int 100))
          (.eq .int (.bvar .int 0) (.const .int  99))))) := by
  generate
  zap
  grind

/-! ## Arithmetic: `let a = 3 in let b = 4 in a + b ⇐ IntN 7` -/

def exAddExp : Exp :=
  .letin (.iconst 3)
    (.letin (.iconst 4)
      (.add (.bvar 1) (.bvar 0)))
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
  .arrow (<ty| Int{ν : ν ≤ 0}|>) Pos

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
  guarantees. The book's `rec f = e₁ : t in e₂` is `letin (ann (fix e₁) t) e₂`.
-/

/-- `sum : n:Int → {ν : 0 ≤ ν ∧ n ≤ ν}` (in the codomain, `BVar 1` is `n`). -/
def sumTy : Ty :=
  .arrow TT
    (.refine .int (.fmla (.and (.leqI (.const .int 0) (.bvar .int 0))
                               (.leqI (.bvar .int 1) (.bvar .int 0)))))

/-- Body of `sum` (there is no `sub`, so `n - 1` is `n + m` with `m = -1`):
    ```
    let z = 0; let c = leq n z;
    if c then 0
    else let m = -1; let n1 = add n m; let t1 = sum n1; add n t1
    ``` -/
def sumBody : Exp :=
  .letin (.iconst 0)                          -- z      (n = 1, sum = 2)
  (.letin (.leq (.bvar 1) (.bvar 0))          -- c      (z = 1, n = 2, sum = 3)
  (.ite (.bvar 0)
    (.iconst 0)
    (.letin (.iconst (-1))                    -- m      (n = 3, sum = 4)
    (.letin (.add (.bvar 3) (.bvar 0))        -- n1     (n = 4, sum = 5)
    (.letin (.app (.bvar 5) (.bvar 0))        -- t1     (n1 = 1, n = 5, sum = 6)
    (.add (.bvar 5) (.bvar 0)))))))           -- n + t1

/-- `sum` meets its spec. -/
example (κ : KEnv) : topVC κ [] (.fix sumBody) sumTy := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        sumBody, sumTy, self, prim, Refinement.interp, Formula.interp, Term.interp, REnv.get,
        TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv, Exp.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar, Term.openBVar]
  intros; omega

/-- A client, via the `rec` encoding: `rec sum = … : sumTy in sum 5 ⇐ {ν : 5 ≤ ν}`. -/
def sumClient : Exp :=
  .letin (.ann (.fix sumBody) sumTy)
  (.letin (.iconst 5)
  (.app (.bvar 1) (.bvar 0)))

example (κ : KEnv) :
    topVC κ [] sumClient (.refine .int (.fmla (.leqI (.const .int 5) (.bvar .int 0)))) := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        sumClient, sumBody, sumTy, self, prim, Refinement.interp, Formula.interp, Term.interp,
        REnv.get, TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv, Exp.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar, Term.openBVar]
  intros; omega

/-! ### Partial correctness: a diverging function

  `loop = fix f. λx. f x` checks against `Int → {ν : false}`: the type promises
  nothing about termination. Safety then says the only way to run `loop 0`
  without getting stuck is to time out — at *every* fuel budget. -/

def loopTy : Ty := .arrow TT (.refine .int (.fmla .ff))
def loop : Exp := .fix (.app (.bvar 1) (.bvar 0))

example (κ : KEnv) : topVC κ [] loop loopTy := by
  simp [topVC, check, synth, sub, implyBindCstr, Cstr.interp, Cstr.triv,
        loop, loopTy, self, Refinement.interp, Formula.interp, Term.interp,
        REnv.get, TEnv.dom, TEnv.tyFv, Ty.fv, Refinement.fv, Formula.fv, Term.fv, Exp.fv,
        Exp.openVar, Ty.openVar, Refinement.openBVar, Formula.openBVar, Term.openBVar]

/-- `rec loop = … : loopTy in loop 0`. -/
def loopMain : Exp :=
  .letin (.ann loop loopTy) (.letin (.iconst 0) (.app (.bvar 1) (.bvar 0)))

theorem loopMain_vc (κ : KEnv) : topVC κ [] loopMain (.refine .int (.fmla .ff)) := by
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
abbrev sumTyK : Ty := .arrow TT (IntR "k")

theorem sum_infer :
    ∃ κ : KEnv,
      Check [] κ []
        (.letin (.ann (.fix sumBody) sumTyK)          -- rec sum = … : sumTyK in
          (.letin (.iconst 5) (.app (.bvar 1) (.bvar 0))))   -- sum 5
        (.refine .int (.fmla (.leqI (.const .int 5) (.bvar .int 0)))) := by
  simp only [sumBody]
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

/-- `α{r}` for the innermost bound type variable. -/
abbrev TV (r : Refinement) : Ty := .refine (.tbvar 0) r
abbrev ttR : Refinement := .fmla .tt
abbrev BoolT : Ty := .refine .bool ttR

/-! ### `id : ∀α:B. x:α → α{ν = x}` — refinement strengthening at instantiation -/

abbrev idTy : Ty :=
  .forall .B (.arrow (TV ttR)
    (TV (.fmla (.eq (.tbvar 0) (.bvar (.tbvar 0) 0) (.bvar (.tbvar 0) 1)))))
abbrev idPoly : Exp := .tabs .B (.lam (.bvar 0))

theorem poly_id (κ : KEnv) : topVC κ [] idPoly idTy := by
  simp [topVC, idPoly, idTy]

/-- `let five = 5 in id[int{k}] five ⇐ {ν = 5}`: the instance's result type is
    `int{k(ν) ∧ ν = five}` — the `ν = x` of `id`'s signature is conjoined into
    the instance, so any `k` admitting `5` works. -/
theorem poly_id_client : ∃ κ : KEnv, Check [] κ []
    (.letin (.iconst 5) (.app (.tapp (.ann idPoly idTy) (IntK "k")) (.bvar 0)))
    (IntN 5) := by
  generate
  zap
  grind

/-! ### The book's §6.1 client, with `choose : ∀α:B. Bool → α → α → α`

  (`max` would need a polymorphic `≤`; our `leq` primitive is `Int`-only.) The
  instance refinement `k` is inferred: it must admit `0` and `5` and give
  `0 < r + 1`. -/

abbrev chooseTy : Ty := .forall .B (.arrow BoolT (.arrow (TV ttR) (.arrow (TV ttR) (TV ttR))))
abbrev choosePoly : Exp := .tabs .B (.lam (.lam (.lam (.ite (.bvar 2) (.bvar 1) (.bvar 0)))))

theorem poly_choose (κ : KEnv) : topVC κ [] choosePoly chooseTy := by
  simp [topVC, choosePoly, chooseTy]

/-- `λc. let z = 0; let f = 5; let r = choose[int{k}] c z f; let one = 1; r + one`
    `⇐ Bool → {0 < ν}`. -/
theorem poly_choose_client : ∃ κ : KEnv, Check [] κ []
    (.lam
      (.letin (.iconst 0)
      (.letin (.iconst 5)
      (.letin (.app (.app (.app (.tapp (.ann choosePoly chooseTy) (IntK "k")) (.bvar 2)) (.bvar 1))
                (.bvar 0))
      (.letin (.iconst 1)
      (.add (.bvar 1) (.bvar 0)))))))
    (.arrow BoolT Pos) := by
  generate
  zap
  grind

/-! ### Impredicative instantiation: `idF[∀β:⋆. β → β] idF` -/

abbrev idFTy : Ty := .forall .star (.arrow (TV ttR) (TV ttR))
abbrev idF : Exp := .tabs .star (.lam (.bvar 0))

theorem poly_impredicative (κ : KEnv) : topVC κ []
    (.letin (.ann idF idFTy) (.app (.tapp (.bvar 0) idFTy) (.bvar 0))) idFTy := by
  simp [topVC, idF, idFTy]

/-! ### Polymorphism + recursion + inference: `iter : ∀α:⋆. (α → α) → Int → α → α`

  `iter f n x` applies `f` to `x` `n` times. Instantiated at `int{k}` and used
  with `inc` from `0`, the instance refinement `k` must be an *invariant* of
  `inc` — a cyclic κ, solved by predicate abstraction (`fix`), which infers
  `k(ν) := 0 ≤ ν`. -/

abbrev iterTy : Ty :=
  .forall .star (.arrow (.arrow (TV ttR) (TV ttR)) (.arrow TT (.arrow (TV ttR) (TV ttR))))

/-- `Λα. fix iter. λf. λn. λx. let z = 0; let c = n ≤ z;
      if c then x else let m = -1; let n1 = n + m; let fx = f x;
                       let g1 = iter f; let g2 = g1 n1; g2 fx` -/
abbrev iterPoly : Exp :=
  .tabs .star (.fix
    (.lam (.lam                                  -- n, x
      (.letin (.iconst 0)                        -- z      x=1 n=2 f=3 self=4
      (.letin (.leq (.bvar 2) (.bvar 0))         -- c      z=1 x=2 n=3 f=4 self=5
      (.ite (.bvar 0)
        (.bvar 2)
        (.letin (.iconst (-1))                   -- m      c=1 z=2 x=3 n=4 f=5 self=6
        (.letin (.add (.bvar 4) (.bvar 0))       -- n1     m=1 .. x=4 n=5 f=6 self=7
        (.letin (.app (.bvar 6) (.bvar 4))       -- fx     n1=1 .. x=5 n=6 f=7 self=8
        (.letin (.app (.bvar 8) (.bvar 7))       -- g1     fx=1 n1=2 .. f=8 self=9
        (.letin (.app (.bvar 0) (.bvar 2))       -- g2     g1=1 fx=2 n1=3
        (.app (.bvar 0) (.bvar 2)))))))))))))    -- g2 fx

theorem poly_iter (κ : KEnv) : topVC κ [] iterPoly iterTy := by
  simp [topVC, iterPoly, iterTy]

/-- `inc : x:Int → {ν = x + 1}` -/
abbrev incTy : Ty :=
  .arrow TT (.refine .int (.fmla (.eq .int (.bvar .int 0) (.add (.bvar .int 1) (.const .int 1)))))
abbrev incE : Exp := .lam (.letin (.iconst 1) (.add (.bvar 1) (.bvar 0)))

/-- `let inc = …; let three = 3; let zero = 0; iter[int{k}] inc three zero ⇐ {0 ≤ ν}`. -/
theorem poly_iter_client : ∃ κ : KEnv, Check [] κ []
    (.letin (.ann incE incTy)
    (.letin (.iconst 3)
    (.letin (.iconst 0)
    (.letin (.app (.tapp (.ann iterPoly iterTy) (IntK "k")) (.bvar 2))   -- iter[k] inc
    (.letin (.app (.bvar 0) (.bvar 2))                                   -- … three
    (.app (.bvar 0) (.bvar 2)))))))                                      -- … zero
    (.refine .int (.fmla (.leqI (.const .int 0) (.bvar .int 0)))) := by
  generate
  fix

/-! ### Type arguments may mention program variables

  `λn. let m = n in id[Int{n ≤ ν}] m ⇐ n:Int → Int{n ≤ ν}`: the instance refers
  to the enclosing binder `n` (in the instance, ν is 0, `m` is 1 and `n` is 2).
  The argument is rebound because the application rule requires it not to occur
  in the result type, which now mentions `n`. -/

theorem poly_tapp_var (κ : KEnv) : topVC κ []
    (.lam (.letin (.bvar 0)
      (.app (.tapp (.ann idPoly idTy) (.refine .int (.fmla (.leqI (.bvar .int 2) (.bvar .int 0)))))
        (.bvar 0))))
    (.arrow TT (.refine .int (.fmla (.leqI (.bvar .int 1) (.bvar .int 0))))) := by
  simp [topVC, idPoly, idTy]
  intros; omega

/-! ### Polymorphic recursion

  `nest : ∀α:⋆. α → Int → Nat` calls itself at the instance `Int → α`: its own
  name is generalized over `α` inside its body (`Check.fix`), which the VC
  generator does because the body type-applies it. -/

attribute [local simp] TEnv.genVars Ty.closeTv BSubst.closeAt List.eraseDups_cons

abbrev NatTy : Ty := .refine .int (.fmla (.leqI (.const .int 0) (.bvar .int 0)))
abbrev nestTy : Ty := .forall .star (.arrow (TV ttR) (.arrow TT NatTy))

/-- `Λα. fix f. λx. λn. let z = 0; let c = n ≤ z;
       if c then z else let g = (λ_. x : Int → α); let m = n - 1; f[Int → α] g m` -/
abbrev nestE (recCall : Exp) : Exp := .tabs .star (.fix (.lam   -- n=0 x=1 f=2
  (.letin (.iconst 0)                                           -- z      n=1 x=2 f=3
  (.letin (.leq (.bvar 1) (.bvar 0))                            -- c      z=1 n=2 x=3 f=4
  (.ite (.bvar 0)
    (.bvar 1)
    (.letin (.ann (.lam (.bvar 4)) (.arrow TT (TV ttR)))         -- g      c=1 z=2 n=3 x=4 f=5
    (.letin (.iconst (-1))                                      -- m1     g=1 … n=4 x=5 f=6
    (.letin (.add (.bvar 4) (.bvar 0))                          -- m      m1=1 g=2 … n=5 f=7
    (.letin recCall                                             -- h      m=1 m1=2 g=3
    (.app (.bvar 0) (.bvar 1)))))))))))

theorem poly_nest (κ : KEnv) : topVC κ []
    (nestE (.app (.tapp (.bvar 7) (.arrow TT (TV ttR))) (.bvar 2))) nestTy := by
  simp [topVC]

/-- With a monomorphic recursive call `f g m`, the argument `g : Int → α` is not
    an `α`: rejected. -/
theorem poly_nest_mono_bad (κ : KEnv) : ¬ topVC κ []
    (nestE (.app (.bvar 7) (.bvar 2))) nestTy := by
  simp [topVC]
