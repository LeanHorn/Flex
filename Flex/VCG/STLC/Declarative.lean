import Flex.VCG.STLC.Typing
import Flex.VCG.STLC.Notation

open STLC

/-! # Declarative Refinement Typing for STLC (LN + deep Formula + κ-assignments) -/

inductive Hastype : DEnv → KEnv → TEnv → Exp → Ty → Prop where
  | var {de κ Γ x t} :
      Γ.lookup x = some t →
      Ty.WFBVars t →
      Hastype de κ Γ (.fvar x) (self x t)
  | int_const {de κ Γ n} :
      Hastype de κ Γ (.iconst n) (prim n)
  | bool_const {de κ Γ b} :
      Hastype de κ Γ (.bconst b) (primBool b)
  | lam {de κ Γ e s₁ s₂ x} :
      Ty.WFBVars (.arrow s₁ s₂) →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s₁.fv ++ s₂.fv →
      Hastype de κ ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) →
      Hastype de κ Γ (.lam e) (.arrow s₁ s₂)
  | app {de κ Γ e₁ y s t} :
      Hastype de κ Γ e₁ (.arrow s t) →
      Hastype de κ Γ (.fvar y) s →
      y ∉ t.fv →
      Hastype de κ Γ (.app e₁ (.fvar y)) (t.openVar 0 y)
  | letin {de κ Γ e₁ e₂ s t x} :
      Ty.WFBVars t →
      Hastype de κ Γ e₁ s →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₂.fv ++ s.fv ++ t.fv →
      Hastype de κ ((x, s) :: Γ) (e₂.openVar 0 x) t →
      Hastype de κ Γ (.letin e₁ e₂) t
  | ann {de κ Γ e t} :
      Hastype de κ Γ e t →
      Ty.WFBVars t →
      Hastype de κ Γ (.ann e t) t
  | sub {de κ Γ e s t} :
      Hastype de κ Γ e s →
      Subtyp de κ Γ s t →
      Ty.WFBVars t →
      Hastype de κ Γ e t
  | add_var {de κ Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      Hastype de κ Γ (.add (.fvar x) (.fvar y)) <ty| Int{ν : ν = x + y}|>
  | leq_var {de κ Γ x y r₁ r₂} :
      Γ.lookup x = some (.refine .int r₁) →
      Γ.lookup y = some (.refine .int r₂) →
      Hastype de κ Γ (.leq (.fvar x) (.fvar y))
        <ty|Bool{ν : (ν = true → x ≤ y) ∧ (x ≤ y → ν = true)} |>
  | not_var {de κ Γ x r} :
      Γ.lookup x = some (.refine .bool r) →
      Hastype de κ Γ (.not (.fvar x)) <ty|Bool{ν : ν = ¬x}|>
  | and_var {de κ Γ x y rx ry} :
      Γ.lookup x = some (.refine .bool rx) →
      Γ.lookup y = some (.refine .bool ry) →
      Hastype de κ Γ (.and (.fvar x) (.fvar y)) <ty|Bool{ν : (ν = x ∧ y)}|>
  | unreach {de κ Γ t} :
      Entail κ Γ (fun _ => False) →
      Ty.WFBVars t →
      Hastype de κ Γ .unreach t
  | ite {de κ Γ x y e₁ e₂ r t} :
      Γ.lookup x = some (.refine .bool r) →
      y ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₁.fv ++ e₂.fv ++ t.fv ++ [x] →
      Ty.WFBVars t →
      Hastype de κ ((y, <ty|Bool{ν : x = true }|>) :: Γ) e₁ t →
      Hastype de κ ((y, <ty|Bool{ν : x = false}|>) :: Γ) e₂ t →
      Hastype de κ Γ (.ite (.fvar x) e₁ e₂) t
  | fix {de κ Γ e s t f x} (as : List TVar) :
      (∀ a ∈ as, a ∉ TEnv.ftv Γ) →
      Ty.WFBVars (.arrow s t) →
      f ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s.fv ++ t.fv →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s.fv ++ t.fv ++ [f] →
      Hastype de κ ((x, s) :: (f, Ty.gen as (.arrow s t)) :: Γ)
        ((e.openVar 1 f).openVar 0 x) (t.openVar 0 x) →
      Hastype de κ Γ (.fix e) (.arrow s t)
  | tabs {de κ Γ k e t a} :
      Ty.WFBVars (.forall k t) →
      a.2 = k →
      a ∉ TEnv.ftv Γ ++ e.ftv ++ t.ftv →
      Hastype de κ Γ (e.openTv 0 a) (t.openTv 0 a) →
      Hastype de κ Γ (.tabs k e) (.forall k t)
  | tapp {de κ Γ e k t s} :
      Hastype de κ Γ e (.forall k t) →
      Kind.le s.kindOf k →
      (Ty.forall k t).wfB [] [] = true →
      s.wfB [] [] = true →
      (Ty.instTy 0 s t).wfB [] [] = true →
      Hastype de κ Γ (.tapp e s) (Ty.instTy 0 s t)
  | pair {de κ Γ x e₂ s t} :
      Ty.WFBVars (.prod s t) →
      Hastype de κ Γ (.fvar x) s →
      x ∉ t.fv →
      Hastype de κ Γ e₂ (t.openVar 0 x) →
      Hastype de κ Γ (.pair (.fvar x) e₂) (.prod s t)
  | split {de κ Γ e body s t t' x y} :
      Ty.WFBVars t' →
      Hastype de κ Γ e (.prod s t) →
      x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t.fv ++ t'.fv →
      y ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t.fv ++ t'.fv ++ [x] →
      Hastype de κ ((y, t.openVar 0 x) :: (x, s) :: Γ) ((body.openVar 1 x).openVar 0 y) t' →
      Hastype de κ Γ (.split e body) t'
  | ctor {de κ Γ C j τs e P} :
      de.payload? C j = some P →
      de.instOK C τs = true →
      Hastype de κ Γ e (Ty.instTys τs P) →
      Hastype de κ Γ (.ctor C j τs e) (Ty.dataL C τs)
  | case {de κ Γ e C n args m alts t} (zs : Fin m → EVar) :
      Ty.WFBVars t →
      Hastype de κ Γ e (.data C n args) →
      de.nCtors C = some m →
      de.instOK C (List.ofFn args) = true →
      (∀ j, zs j ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ (alts j).fv ++ t.fv) →
      (∀ (j : Fin m) P, de.payload? C j.val = some P →
        zs j ∉ (Ty.instTys (List.ofFn args) P).fv) →
      (∀ (j : Fin m) P, de.payload? C j.val = some P →
        Hastype de κ ((zs j, Ty.instTys (List.ofFn args) P) :: Γ)
          ((alts j).openVar 0 (zs j)) t) →
      Hastype de κ Γ (.case e m alts) t

/-- For fvar typing, the variable must appear in the context. -/
theorem Hastype.fvar_lookup {de κ Γ x t} (h : Hastype de κ Γ (.fvar x) t) :
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
    | lam e ih | not e ih | fix e ih => simp_all [Exp.fv, Exp.openVar]
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
    | ann e t ih | tapp e t ih | tabs t e ih =>
        simp_all [Exp.fv, Exp.openVar]
    | unreach             => simp_all [Exp.fv]
    | pair e₁ e₂ ih1 ih2 | split e₁ e₂ ih1 ih2 =>
        simp_all [Exp.fv, Exp.openVar]
        grind
    | ctor _ _ _ e ih => simp_all [Exp.fv, Exp.openVar]
    | case e n alts ih ihs =>
        simp only [Exp.fv, Exp.openVar, List.mem_append, List.mem_flatMap, List.mem_finRange,
          true_and] at xf ⊢
        rcases xf with h | ⟨j, h⟩
        · exact Or.inl (ih h)
        · exact Or.inr ⟨j, ihs j h⟩

/-- Deferred — see Stage 12. -/
theorem Hastype.fv_subset {de κ Γ e t} (_h : Hastype de κ Γ e t) :
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
  | @fix Γ' e s t f x _ _ _ hf hx _ ih =>
    simp only [Exp.fv] at zf
    simp only [List.mem_append, List.mem_singleton, not_or] at hf hx
    obtain ⟨t', hz⟩ := ih (EVar.not_free_in_open (EVar.not_free_in_open zf))
    simp only [List.mem_cons, Prod.mk.injEq] at hz
    rcases hz with ⟨rfl, _⟩ | ⟨rfl, _⟩ | hz
    · exact absurd zf (by simp_all)
    · exact absurd zf (by simp_all)
    · exact ⟨t', hz⟩
  | tabs _ _ _ _ ih =>
    simp only [Exp.fv] at zf
    exact ih (by simpa using zf)
  | tapp _ _ _ _ _ ih =>
    simp only [Exp.fv] at zf
    exact ih zf
  | pair _ _ _ _ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append] at zf
    rcases zf with h | h
    · exact ih₁ h
    · exact ih₂ h
  | @split Γ' e body s t t' x y _ _ hx hy _ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append] at zf
    rcases zf with h | h
    · exact ih₁ h
    · simp only [List.mem_append, List.mem_singleton, not_or] at hx hy
      obtain ⟨t'', hz⟩ := ih₂ (EVar.not_free_in_open (EVar.not_free_in_open h))
      simp only [List.mem_cons, Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, _⟩ | ⟨rfl, _⟩ | hz
      · exact absurd h (by simp_all)
      · exact absurd h (by simp_all)
      · exact ⟨t'', hz⟩
  | ctor _ _ _ ih =>
    simp only [Exp.fv] at zf
    exact ih zf
  | @case Γ' e C n args m alts t zs _ _ hm _ hz _ _ ih ihs =>
    simp only [Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and] at zf
    rcases zf with h | ⟨j, h⟩
    · exact ih h
    · obtain ⟨P, hP⟩ := DEnv.payload?_of_lt hm j.isLt
      obtain ⟨t'', hz'⟩ := ihs j P hP (EVar.not_free_in_open h)
      simp only [List.mem_cons, Prod.mk.injEq] at hz'
      rcases hz' with ⟨rfl, _⟩ | hz'
      · have := hz j
        simp only [List.mem_append, not_or] at this
        exact absurd h this.1.2
      · exact ⟨t'', hz'⟩


/-- Well-typed expressions are locally closed (lc_at 0). Proved by induction on
    the typing derivation. Deferred (Stage 12). -/
theorem Hastype.lc_at {de κ Γ e t} (_h : Hastype de κ Γ e t) : Exp.lc_at 0 e := by
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
  | fix _ _ _ _ _ _ ih =>
    simp only [Exp.lc_at]
    exact Exp.lc_at_of_openVar _ 1 _ (Exp.lc_at_of_openVar _ 0 _ ih)
  | tabs _ _ _ _ ih => simpa [Exp.lc_at] using ih
  | tapp _ _ _ _ _ ih => simpa [Exp.lc_at] using ih
  | pair _ _ _ _ ih₁ ih₂ => simp only [Exp.lc_at]; exact ⟨ih₁, ih₂⟩
  | split _ _ _ _ _ ih₁ ih₂ =>
    simp only [Exp.lc_at]
    exact ⟨ih₁, Exp.lc_at_of_openVar _ 1 _ (Exp.lc_at_of_openVar _ 0 _ ih₂)⟩
  | ctor _ _ _ ih => simpa [Exp.lc_at] using ih
  | case _ _ _ hm _ _ _ _ ih ihs =>
    simp only [Exp.lc_at]
    refine ⟨ih, fun j => ?_⟩
    obtain ⟨P, hP⟩ := DEnv.payload?_of_lt hm j.isLt
    exact Exp.lc_at_of_openVar _ 0 _ (ihs j P hP)

/-- WFBVars of `self x t`: `self` is the singleton `{ν | ν = x}` (kvar-free, no
    BVars), so it is `WFBVars` outright — independent of `t`. -/
theorem Ty.WFBVars_self (x : EVar) (t : Ty) (_h : Ty.WFBVars t) : Ty.WFBVars (self x t) := by
  cases t with
  | refine b r =>
    cases b with
    | tfvar a =>
      rcases a with ⟨n, _ | _⟩
      · simp [self, Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]
      · simpa [self] using _h
    | _ =>
      simp [self, Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]
  | arrow s t => simp [self, _h]
  | «forall» k t => simpa [self] using _h
  | prod s t => simpa [self] using _h
  | data C n args => simpa [self] using _h

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
theorem Hastype.wf_bvars {de κ Γ e t} (h : Hastype de κ Γ e t) : Ty.WFBVars t := by
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
  | fix _ _ hwf _ _ _ => exact hwf
  | tabs hwf _ _ _ _ => exact hwf
  | tapp _ _ _ _ hres _ => exact Ty.wfB_WFBVars _ hres
  | pair hwf _ _ _ _ _ => exact hwf
  | split hwf _ _ _ _ _ _ => exact hwf
  | ctor _ hok _ _ => exact DEnv.instOK_WFBVars hok
  | case _ hwf _ _ _ _ _ _ _ _ => exact hwf
