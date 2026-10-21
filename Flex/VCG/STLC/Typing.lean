import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Substitution
import Flex.VCG.STLC.Entailment
import Flex.VCG.STLC.Notation

open STLC

/-! # Bidirectional Refinement Typing (LN + deep Formula + κ-assignments)

  All judgements are indexed by `κ : KEnv` (the κ-assignment that the solver
  picks). The user typically writes `∃ κ, Check κ [] e t`.

  Binding sites use locally-nameless: `Exp.lam`/`letin` carry no binder name;
  the body has `BVar 0` for the parameter.

  Refinements are deeply-embedded `Formula`s. Both binder rules — `Subtyp.arrow`
  and `Subtyp.refine` — are stated in *opened* form: they introduce a fresh name
  and check the codomain / opened refinement under the extended context.

-/

/-! ## Subtyping  κ; Γ ⊢ s <: t -/

inductive Subtyp : KEnv → TEnv → Ty → Ty → Prop where
  | refine {κ Γ b r₁ r₂ x} :
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv →
      Entail κ ((x, .refine b r₁) :: Γ) (fun γ => Refinement.interp κ (r₂.openBVar 0 x) γ) →
      Subtyp κ Γ (.refine b r₁) (.refine b r₂)

  /-- SUB-FUN (explicit witness): contravariant input, covariant output. -/
  | arrow {κ Γ s₁ t₁ s₂ t₂ x} :
      Subtyp κ Γ s₂ s₁ →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ s₁.fv ++ s₂.fv ++ t₁.fv ++ t₂.fv →
      Subtyp κ ((x, s₂) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) →
      Subtyp κ Γ (.arrow s₁ t₁) (.arrow s₂ t₂)

/-! ## Bidirectional typing -/

mutual
  -- κ; Γ ⊢ e ⇒ t : "e synthesizes type t under κ"
  inductive Synth : KEnv → TEnv → Exp → Ty → Prop where
    | var {κ Γ x t} :
        Γ.lookup x = some t →
        Synth κ Γ (.fvar x) (self x t)

    | int_const {κ Γ n} :
        Synth κ Γ (.iconst n) (prim n)

    | bool_const {κ Γ b} :
        Synth κ Γ (.bconst b) (primBool b)

    | ann {κ Γ e t} :
        Check κ Γ e t →
        Synth κ Γ (.ann e t) t

    | app {κ Γ e₁ y s t} :
        Synth κ Γ e₁ (.arrow s t) →
        Check κ Γ (.fvar y) s        →
        y ∉ t.fv →
        Synth κ Γ (.app e₁ (.fvar y)) (t.openVar 0 y)

    | leq_var {κ Γ x y r₁ r₂} :
        Γ.lookup x = some (.refine .int r₁) →
        Γ.lookup y = some (.refine .int r₂) →
        Synth κ Γ (.leq (.fvar x) (.fvar y))
           <ty|Bool{ν : (ν = true → x ≤ y) ∧ (x ≤ y → ν = true)}|>

    | add_var {κ Γ x y r₁ r₂} :
        Γ.lookup x = some (.refine .int r₁) →
        Γ.lookup y = some (.refine .int r₂) →
        Synth κ Γ (.add (.fvar x) (.fvar y)) <ty| Int{ν : ν = x + y}|>

    | not_var {κ Γ x r} :
        Γ.lookup x = some (.refine .bool r) →
        Synth κ Γ (.not (.fvar x)) <ty|Bool{ν : ν = ¬x}|>

    | and_var {κ Γ x y rx ry} :
        Γ.lookup x = some (.refine .bool rx) →
        Γ.lookup y = some (.refine .bool ry) →
        Synth κ Γ (.and (.fvar x) (.fvar y)) <ty|Bool{ν : ν = x ∧ y} |>

  inductive Check : KEnv → TEnv → Exp → Ty → Prop where
    | sub {κ Γ e s t} :
        Synth κ Γ e s  →
        Subtyp κ Γ s t →
        Check κ Γ e t

    /-- UNREACH: `unreachable` typechecks at any type, provided the ambient
        context is provably contradictory (no model of `Γ` exists). It is not
        a value and has no `BigStep` rule — it can only appear in dead code. -/
    | unreach {κ Γ t} :
        Entail κ Γ (fun _ => False) →
        Check κ Γ .unreach t

    | lam {κ Γ e s₁ s₂ x} :
        x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s₁.fv ++ s₂.fv →
        Check κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) →
        Check κ Γ (.lam e) (.arrow s₁ s₂)

    | letin {κ Γ e₁ e₂ s t x} :
        Synth κ Γ e₁ s →
        x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₂.fv ++ s.fv ++ t.fv →
        Check κ ((x, s) :: Γ) (e₂.openVar 0 x) t →
        Check κ Γ (.letin e₁ e₂) t

    | ite {κ Γ x y e₁ e₂ r t} :
        Γ.lookup x = some (.refine .bool r) →
        y ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₁.fv ++ e₂.fv ++ t.fv ++ [x] →
        Check κ ((y, <ty|Bool{ν : x = true }|>) :: Γ) e₁ t →
        Check κ ((y, <ty|Bool{ν : x = false}|>) :: Γ) e₂ t →
        Check κ Γ (.ite (.fvar x) e₁ e₂) t
end
