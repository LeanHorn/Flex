import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Substitution
import Flex.VCG.STLC.Entailment
import Flex.VCG.STLC.Notation

open STLC

/-! # Bidirectional Refinement Typing (LN + deep Formula + κ-assignments)

  All judgements are indexed by `κ : KEnv` (the κ-assignment that the solver
  picks). The user typically writes `∃ κ, Check de κ [] e t`.

  Binding sites use locally-nameless: `Exp.lam`/`letin` carry no binder name;
  the body has `BVar 0` for the parameter.

  Refinements are deeply-embedded `Formula`s. Both binder rules — `Subtyp.arrow`
  and `Subtyp.refine` — are stated in *opened* form: they introduce a fresh name
  and check the codomain / opened refinement under the extended context.

-/

/-! ## Subtyping  κ; Γ ⊢ s <: t -/

inductive Subtyp : DEnv → KEnv → TEnv → Ty → Ty → Prop where
  | refine {de κ Γ b r₁ r₂ x} :
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv →
      Entail κ ((x, .refine b r₁) :: Γ) (fun γ => Refinement.interp κ (r₂.openBVar 0 x) γ) →
      Subtyp de κ Γ (.refine b r₁) (.refine b r₂)

  /-- SUB-FUN (explicit witness): contravariant input, covariant output. -/
  | arrow {de κ Γ s₁ t₁ s₂ t₂ x} :
      Subtyp de κ Γ s₂ s₁ →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ s₁.fv ++ s₂.fv ++ t₁.fv ++ t₂.fv →
      Subtyp de κ ((x, s₂) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) →
      Subtyp de κ Γ (.arrow s₁ t₁) (.arrow s₂ t₂)

  /-- S-POLY: open both bodies with the same fresh type variable. -/
  | «forall» {de κ Γ k t₁ t₂ a} :
      a.2 = k →
      a ∉ TEnv.ftv Γ ++ t₁.ftv ++ t₂.ftv →
      Subtyp de κ Γ (t₁.openTv 0 a) (t₂.openTv 0 a) →
      Subtyp de κ Γ (.forall k t₁) (.forall k t₂)

  /-- Dependent pairs: covariant in both components; the second is compared
      with the first component bound at the subtype. -/
  | prod {de κ Γ s₁ t₁ s₂ t₂ x} :
      Subtyp de κ Γ s₁ s₂ →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ s₁.fv ++ s₂.fv ++ t₁.fv ++ t₂.fv →
      Subtyp de κ ((x, s₁) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) →
      Subtyp de κ Γ (.prod s₁ t₁) (.prod s₂ t₂)

  /-- Datatypes: the same datatype, with each type argument related according
      to the parameter's declared variance (covariant: `<:`; contravariant:
      `:>`; invariant: both), and the refinements related as in `refine`. -/
  | data {de κ Γ C n args₁ args₂ r₁ r₂ x} :
      (∀ i : Fin n, de.var C i.val ≠ .contra → Subtyp de κ Γ (args₁ i) (args₂ i)) →
      (∀ i : Fin n, de.var C i.val ≠ .co → Subtyp de κ Γ (args₂ i) (args₁ i)) →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv →
      Entail κ ((x, .data C n args₁ r₁) :: Γ) (fun γ => Refinement.interp κ (r₂.openBVar 0 x) γ) →
      Subtyp de κ Γ (.data C n args₁ r₁) (.data C n args₂ r₂)

/-- The result type of a comparison at sort `b`: `Bool{ν ⇔ x ≤ y}`. -/
abbrev leqTy (b : Base) (x y : EVar) : Ty :=
  .refine .bool (.fmla (.and
    (.imp (.eq .bool (.bvar .bool 0) (.const .bool true)) (.leq b (.fvar b x) (.fvar b y)))
    (.imp (.leq b (.fvar b x) (.fvar b y)) (.eq .bool (.bvar .bool 0) (.const .bool true)))))

/-! ## Bidirectional typing -/

mutual
  -- κ; Γ ⊢ e ⇒ t : "e synthesizes type t under κ"
  inductive Synth : DEnv → KEnv → TEnv → Exp → Ty → Prop where
    | var {de κ Γ x t} :
        Γ.lookup x = some t →
        Synth de κ Γ (.fvar x) (self x t)

    | int_const {de κ Γ n} :
        Synth de κ Γ (.iconst n) (prim n)

    | bool_const {de κ Γ b} :
        Synth de κ Γ (.bconst b) (primBool b)

    | ann {de κ Γ e t} :
        Check de κ Γ e t →
        Synth de κ Γ (.ann e t) t

    | app {de κ Γ e₁ y s t} :
        Synth de κ Γ e₁ (.arrow s t) →
        Check de κ Γ (.fvar y) s        →
        y ∉ t.fv →
        Synth de κ Γ (.app e₁ (.fvar y)) (t.openVar 0 y)

    /-- Comparison is polymorphic over the comparable sorts: `Int`, `Bool`
        and `B`-kinded type variables (`Base.fvOK`). -/
    | leq_var {de κ Γ x y b r₁ r₂} :
        Γ.lookup x = some (.refine b r₁) →
        Γ.lookup y = some (.refine b r₂) →
        b.fvOK = true →
        Synth de κ Γ (.leq (.fvar x) (.fvar y)) (leqTy b x y)

    | add_var {de κ Γ x y r₁ r₂} :
        Γ.lookup x = some (.refine .int r₁) →
        Γ.lookup y = some (.refine .int r₂) →
        Synth de κ Γ (.add (.fvar x) (.fvar y)) <ty| Int{ν : ν = x + y}|>

    | not_var {de κ Γ x r} :
        Γ.lookup x = some (.refine .bool r) →
        Synth de κ Γ (.not (.fvar x)) <ty|Bool{ν : ν = ¬x}|>

    | and_var {de κ Γ x y rx ry} :
        Γ.lookup x = some (.refine .bool rx) →
        Γ.lookup y = some (.refine .bool ry) →
        Synth de κ Γ (.and (.fvar x) (.fvar y)) <ty|Bool{ν : ν = x ∧ y} |>

    /-- T-TAPP: instantiate a polymorphic type with a (well-formed) type of an
        appropriate kind; refinements on the type variable strengthen the instance. -/
    | tapp {de κ Γ e k t s} :
        Synth de κ Γ e (.forall k t) →
        Kind.le s.kindOf k →
        (Ty.forall k t).wfB [] [] = true →
        s.wfB [] [] = true →
        (Ty.instTy 0 s t).wfB [] [] = true →
        Synth de κ Γ (.tapp e s) (Ty.instTy 0 s t)

    /-- CTOR: check the payload against the constructor's payload type at the
        given type arguments. -/
    | ctor {de κ Γ C j τs e P} :
        de.payload? C j = some P →
        de.instOK C τs = true →
        Check de κ Γ e (Ty.instTys τs P) →
        Synth de κ Γ (.ctor C j τs e) (Ty.dataL C τs)

  inductive Check : DEnv → KEnv → TEnv → Exp → Ty → Prop where
    | sub {de κ Γ e s t} :
        Synth de κ Γ e s  →
        Subtyp de κ Γ s t →
        Check de κ Γ e t

    /-- UNREACH: `unreachable` typechecks at any type, provided the ambient
        context is provably contradictory (no model of `Γ` exists). It is not
        a value and has no `BigStep` rule — it can only appear in dead code. -/
    | unreach {de κ Γ t} :
        Entail κ Γ (fun _ => False) →
        Check de κ Γ .unreach t

    | lam {de κ Γ e s₁ s₂ x} :
        x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s₁.fv ++ s₂.fv →
        Check de κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) →
        Check de κ Γ (.lam e) (.arrow s₁ s₂)

    | letin {de κ Γ e₁ e₂ s t x} :
        Synth de κ Γ e₁ s →
        x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₂.fv ++ s.fv ++ t.fv →
        Check de κ ((x, s) :: Γ) (e₂.openVar 0 x) t →
        Check de κ Γ (.letin e₁ e₂) t

    | ite {de κ Γ x y e₁ e₂ r t} :
        Γ.lookup x = some (.refine .bool r) →
        y ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₁.fv ++ e₂.fv ++ t.fv ++ [x] →
        Check de κ ((y, <ty|Bool{ν : x = true }|>) :: Γ) e₁ t →
        Check de κ ((y, <ty|Bool{ν : x = false}|>) :: Γ) e₂ t →
        Check de κ Γ (.ite (.fvar x) e₁ e₂) t

    /-- FIX (Chk-Rec, assume–guarantee): check the body of the recursive
        function `fix f. λx. e` assuming `f` already has the annotated type,
        *generalized* over type variables `as` that the context does not
        mention — polymorphic recursion: the recursive calls may instantiate
        them differently (`as = []` is the monomorphic rule). -/
    | fix {de κ Γ e s t f x} (as : List TVar) :
        (∀ a ∈ as, a ∉ TEnv.ftv Γ) →
        f ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s.fv ++ t.fv →
        x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s.fv ++ t.fv ++ [f] →
        Check de κ ((x, s) :: (f, Ty.gen as (.arrow s t)) :: Γ)
          ((e.openVar 1 f).openVar 0 x) (t.openVar 0 x) →
        Check de κ Γ (.fix e) (.arrow s t)

    /-- T-TABS: check the body against the opened type, with a fresh type
        variable of the abstraction's kind. -/
    | tabs {de κ Γ k e t a} :
        a.2 = k →
        a ∉ TEnv.ftv Γ ++ e.ftv ++ t.ftv →
        Check de κ Γ (e.openTv 0 a) (t.openTv 0 a) →
        Check de κ Γ (.tabs k e) (.forall k t)

    /-- PAIR (ANF): the first component is a variable, which the second
        component's type may mention. -/
    | pair {de κ Γ x e₂ s t} :
        Check de κ Γ (.fvar x) s →
        x ∉ t.fv →
        Check de κ Γ e₂ (t.openVar 0 x) →
        Check de κ Γ (.pair (.fvar x) e₂) (.prod s t)

    /-- SPLIT: bind both components of a pair. -/
    | split {de κ Γ e body s t t' x y} :
        Synth de κ Γ e (.prod s t) →
        x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t.fv ++ t'.fv →
        y ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t.fv ++ t'.fv ++ [x] →
        Check de κ ((y, t.openVar 0 x) :: (x, s) :: Γ) ((body.openVar 1 x).openVar 0 y) t' →
        Check de κ Γ (.split e body) t'

    /-- CASE: one alternative per constructor, in declaration order; each binds
        the constructor's payload at the scrutinee's type arguments. -/
    | case {de κ Γ e C n args r m alts t} (zs : Fin m → EVar) :
        Synth de κ Γ e (.data C n args r) →
        de.nCtors C = some m →
        de.instOK C (List.ofFn args) = true →
        (∀ j, zs j ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ (alts j).fv ++ t.fv) →
        (∀ (j : Fin m) P, de.payload? C j.val = some P →
          zs j ∉ (Ty.instTys (List.ofFn args) P).fv) →
        (∀ (j : Fin m) P, de.payload? C j.val = some P →
          Check de κ ((zs j, Ty.instTys (List.ofFn args) P) :: Γ)
            ((alts j).openVar 0 (zs j)) t) →
        Check de κ Γ (.case e m alts) t
end
