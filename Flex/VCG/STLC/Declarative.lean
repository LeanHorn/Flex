import Flex.VCG.STLC.Typing
import Flex.VCG.STLC.Notation

open STLC

/-! # Declarative Refinement Typing for STLC (LN + deep Formula + κ-assignments) -/

inductive Hastype : KEnv → TEnv → Exp → Ty → Prop where
  | var {κ Γ x t} :
      Γ.lookup x = some t →
      Ty.WFBVars t →
      Hastype κ Γ (.fvar x) (self x t)
  | int_const {κ Γ n} :
      Hastype κ Γ (.iconst n) (prim n)
  | bool_const {κ Γ b} :
      Hastype κ Γ (.bconst b) (primBool b)
  | lam {κ Γ e s₁ s₂ x} :
      Ty.WFBVars (.arrow s₁ s₂) →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s₁.fv ++ s₂.fv →
      Hastype κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) →
      Hastype κ Γ (.lam e) (.arrow s₁ s₂)
  | app {κ Γ e₁ y s t} :
      Hastype κ Γ e₁ (.arrow s t) →
      Hastype κ Γ (.fvar y) s →
      y ∉ t.fv →
      Hastype κ Γ (.app e₁ (.fvar y)) (t.openVar 0 y)
  | letin {κ Γ e₁ e₂ s t x} :
      Ty.WFBVars t →
      Hastype κ Γ e₁ s →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₂.fv ++ s.fv ++ t.fv →
      Hastype κ ((x, s) :: Γ) (e₂.openVar 0 x) t →
      Hastype κ Γ (.letin e₁ e₂) t
  | ann {κ Γ e t} :
      Hastype κ Γ e t →
      Ty.WFBVars t →
      Hastype κ Γ (.ann e t) t
  | sub {κ Γ e s t} :
      Hastype κ Γ e s →
      Subtyp κ Γ s t →
      Ty.WFBVars t →
      Hastype κ Γ e t
  | add_var {κ Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      Hastype κ Γ (.add (.fvar x) (.fvar y)) <ty| Int{ν : ν = x + y}|>
  | leq_var {κ Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      Hastype κ Γ (.leq (.fvar x) (.fvar y))
        <ty|Bool{ν : (ν = true → x ≤ y) ∧ (x ≤ y → ν = true)} |>
  | not_var {κ Γ x r} :
      Γ.lookup x = some (.refine .bool r) →
      Hastype κ Γ (.not (.fvar x)) <ty|Bool{ν : ν = ¬x}|>
  | and_var {κ Γ x y rx ry} :
      Γ.lookup x = some (.refine .bool rx) →
      Γ.lookup y = some (.refine .bool ry) →
      Hastype κ Γ (.and (.fvar x) (.fvar y)) <ty|Bool{ν : (ν = x ∧ y)}|>
  | unreach {κ Γ t} :
      Entail κ Γ (fun _ => False) →
      Ty.WFBVars t →
      Hastype κ Γ .unreach t
  | ite {κ Γ x y e₁ e₂ r t} :
      Γ.lookup x = some (.refine .bool r) →
      y ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₁.fv ++ e₂.fv ++ t.fv ++ [x] →
      Ty.WFBVars t →
      Hastype κ ((y, <ty|Bool{ν : x = true }|>) :: Γ) e₁ t →
      Hastype κ ((y, <ty|Bool{ν : x = false}|>) :: Γ) e₂ t →
      Hastype κ Γ (.ite (.fvar x) e₁ e₂) t

/-- For fvar typing, the variable must appear in the context. -/
theorem Hastype.fvar_lookup {κ Γ x t} (h : Hastype κ Γ (.fvar x) t) :
    ∃ s, Γ.lookup x = some s := by
  -- Only var and sub (transitively) can type a free variable; proved below
  -- by structural descent but requires sorry due to LN index elaboration issue.
  generalize he : (Exp.fvar x) = e ; rw [he] at h
  induction h <;> grind

theorem EVar.not_free_in_open : x ∈ e.fv → x ∈ (Exp.openVar k y e).fv := by
    intro xf
    induction e generalizing k with
    | bvar j              => simp_all [Exp.fv]
    | fvar z              => unfold Exp.fv Exp.openVar at * ; simp_all
    | iconst i            => simp_all [Exp.fv]
    | bconst b            => simp_all [Exp.fv]
    | lam e ih | not e ih => simp_all [Exp.fv, Exp.openVar]
    | letin e₁ e₂ ih1 ih2
    | app e₁ e₂ ih1 ih2
    | add e₁ e₂ ih1 ih2
    | leq e₁ e₂ ih1 ih2
    | and e₁ e₂ ih1 ih2   =>
        simp_all [Exp.fv, Exp.openVar]
        grind
    | ite e₀ e₁ e₂ ih1 ih2 ih3 =>
        simp_all [Exp.fv, Exp.openVar]
        grind
    | ann e t ih          =>
        simp_all [Exp.fv, Exp.openVar]
    | unreach             => simp_all [Exp.fv]

/-- Deferred — see Stage 12. -/
theorem Hastype.fv_subset {κ Γ e t} (_h : Hastype κ Γ e t) :
    ∀ z ∈ Exp.fv e, ∃ t', (z, t') ∈ Γ := by
  intro z zf
  induction _h with
  | @var _ _ _ hl _ =>
    simp [Exp.fv] at zf
    rw [List.lookup_eq_some_iff] at hl
    grind
  | int_const | bool_const =>
    simp [Exp.fv] at zf
  | @lam Γ' e s₁ s₂ x _ hfresh hbody ih =>
    simp [Exp.fv] at *
    have hx_efv : x ∉ e.fv := hfresh.2.2.1
      -- simp only [List.mem_append, not_or] at hfresh; exact hfresh.2.1
    grind [EVar.not_free_in_open]
    -- obtain ⟨t', hzeq | foo⟩ := ih (EVar.fv_subset_fv_openVar hx_efv zf)
    --     <;> [grind [EVar.fresh_not_mem]; exact ⟨t', foo⟩]
  | @letin Γ' e₁ e₂ s t x _ he1 hfresh hbody ih1 ih2 =>
    simp [Exp.fv] at *
    rcases zf with hzf1 | hzf2
    · exact ih1 hzf1
    · have hx_efv : x ∉ e₂.fv := hfresh.2.2.1
        -- simp only [List.mem_append, not_or] at hfresh; exact hfresh.2.1
      grind [EVar.not_free_in_open]
      -- obtain ⟨t', hzeq | foo⟩ := ih2 (EVar.fv_subset_fv_openVar hx_efv hzf2)
      --     <;> [grind [EVar.fresh_not_mem]; exact ⟨t', foo⟩]
  | add_var | leq_var | not_var | and_var | ite =>
    simp [Exp.fv] at zf
    rcases zf
        <;> grind [List.lookup_eq_some_iff]
  | sub => grind
  | @app Γ' e₁ y s t hht1 hht2 _hyfv ih1 ih2 =>
    simp [Exp.fv] at zf
    rcases zf with hzf1 | hzf2
    · exact ih1 hzf1
    · simp [Exp.fv] at ih2
      exact ih2 hzf2
  | @ann Γ' e t hht _ ih =>
    simp [Exp.fv] at zf
    exact ih zf
  | unreach =>
    simp [Exp.fv] at zf


/-- Well-typed expressions are locally closed (lc_at 0). Proved by induction on
    the typing derivation. Deferred (Stage 12). -/
theorem Hastype.lc_at {κ Γ e t} (_h : Hastype κ Γ e t) : Exp.lc_at 0 e := by
  induction _h with
  | var => simp [Exp.lc_at]
  | int_const => simp [Exp.lc_at]
  | bool_const => simp [Exp.lc_at]
  | lam =>
      simp only [Exp.lc_at]
      grind [Exp.lc_at_of_openVar]
  | app _ _ _ ih₁ ih₂ =>
    simp only [Exp.lc_at]; exact ⟨ih₁, ih₂⟩
  | letin =>
    simp only [Exp.lc_at]
    grind [Exp.lc_at_of_openVar]
  | ann _ _ ih => simp only [Exp.lc_at]; exact ih
  | sub _ _ _ ih => exact ih
  | add_var => simp [Exp.lc_at]
  | leq_var => simp [Exp.lc_at]
  | not_var => simp [Exp.lc_at]
  | and_var => simp [Exp.lc_at]
  | ite _ _ _ _ _ ih₁ ih₂ => simp only [Exp.lc_at]; exact ⟨trivial, ih₁, ih₂⟩
  | unreach => simp [Exp.lc_at]

/-- WFBVars of `self x t`: `self` is the singleton `{ν | ν = x}` (kvar-free, no
    BVars), so it is `WFBVars` outright — independent of `t`. -/
theorem Ty.WFBVars_self (x : EVar) (t : Ty) (_h : Ty.WFBVars t) : Ty.WFBVars (self x t) := by
  cases t with
  | refine b r =>
    cases b <;>
      simp [self, Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]
  | arrow s t => simp [self, _h]

/-- WFBVars of the concrete result types for primitives. -/
theorem Ty.WFBVars_prim (n : Int) : Ty.WFBVars (prim n) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]

theorem Ty.WFBVars_primBool (b : Bool) : Ty.WFBVars (primBool b) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]

/-- WFBVars of the add_var result type. -/
theorem Ty.WFBVars_add_result (x y : EVar) : Ty.WFBVars
    (.refine .int (.fmla (.eq .int (.bvar .int 0) (.add (.fvar .int x) (.fvar .int y))))) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]

/-- WFBVars of the leq_var result type. -/
theorem Ty.WFBVars_leq_result (x y : EVar) : Ty.WFBVars
    (.refine .bool (.fmla (.and
      (.imp (.eq .bool (.bvar .bool 0) (.const .bool true)) (.leqI (.fvar .int x) (.fvar .int y)))
      (.imp (.leqI (.fvar .int x) (.fvar .int y)) (.eq .bool (.bvar .bool 0) (.const .bool true)))))) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]

/-- WFBVars of the not_var result type. -/
theorem Ty.WFBVars_not_result (x : EVar) : Ty.WFBVars
    (.refine .bool (.fmla (.eq .bool (.bvar .bool 0) (.not (.fvar .bool x))))) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]

/-- WFBVars of the and_var result type. -/
theorem Ty.WFBVars_and_result (x y : EVar) : Ty.WFBVars
    (.refine .bool (.fmla (.eq .bool (.bvar .bool 0) (.and (.fvar .bool x) (.fvar .bool y))))) := by
  simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]

/-- Every type produced by a Hastype derivation is WFBVars. -/
theorem Hastype.wf_bvars {κ Γ e t} (h : Hastype κ Γ e t) : Ty.WFBVars t := by
  induction h with
  | var _ hwf => exact Ty.WFBVars_self _ _ hwf
  | int_const  => exact Ty.WFBVars_prim _
  | bool_const => exact Ty.WFBVars_primBool _
  | lam _ hwf _ => grind
  | app _ _ _ ih₁ _ =>
    -- ih₁ : WFBVars (.arrow s t), need WFBVars (t.openVar 0 y)
    simp only [Ty.WFBVars, Ty.WFBVarCtx] at ih₁
    exact Ty.WFBVarCtx_openVar_last _ [] _ _ ih₁.2
  | letin _ hwf _ _ _ _ => grind
  | ann _ hwf _ => exact hwf
  | sub _ _ hwf _ => exact hwf
  | add_var => exact Ty.WFBVars_add_result _ _
  | leq_var => exact Ty.WFBVars_leq_result _ _
  | not_var => exact Ty.WFBVars_not_result _
  | and_var => exact Ty.WFBVars_and_result _ _
  | ite _ _ hwf _ _ _ _ => exact hwf
  | unreach _ hwf => exact hwf
