import Flex.VCG.STLC.Checker.Typing

open STLC


/-! # Declarative Refinement Typing for STLC (LN + deep Formula + κ-assignments) -/

inductive Hastype : DEnv → KEnv → TEnv → Exp → Ty → Prop where
  | var {de κ Γ x t} :
      Γ.lookup x = some t →
      Ty.WFBVars t →
      Hastype de κ Γ (.fvar x) (self de x t)
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
      Hastype de κ Γ (.add (.fvar x) (.fvar y)) (.refine .int (.fmla (.eq .int (.bvar .int 0) (.add (.fvar .int x) (.fvar .int y)))))
  | leq_var {de κ Γ x y b r₁ r₂} :
      Γ.lookup x = some (.refine b r₁) →
      Γ.lookup y = some (.refine b r₂) →
      b.fvOK = true →
      Hastype de κ Γ (.leq (.fvar x) (.fvar y)) (leqTy b x y)
  | not_var {de κ Γ x r} :
      Γ.lookup x = some (.refine .bool r) →
      Hastype de κ Γ (.not (.fvar x)) (.refine .bool (.fmla (.eq .bool (.bvar .bool 0) (.not (.fvar .bool x)))))
  | and_var {de κ Γ x y rx ry} :
      Γ.lookup x = some (.refine .bool rx) →
      Γ.lookup y = some (.refine .bool ry) →
      Hastype de κ Γ (.and (.fvar x) (.fvar y)) (.refine .bool (.fmla (.eq .bool (.bvar .bool 0) (.and (.fvar .bool x) (.fvar .bool y)))))
  | unreach {de κ Γ t} :
      Entail κ Γ (fun _ => False) →
      Ty.WFBVars t →
      Hastype de κ Γ .unreach t
  | ite {de κ Γ x y e₁ e₂ r t} :
      Γ.lookup x = some (.refine .bool r) →
      y ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e₁.fv ++ e₂.fv ++ t.fv ++ [x] →
      Ty.WFBVars t →
      Hastype de κ ((y, (.refine .bool (.fmla (.eq .bool (.fvar .bool x) (.const .bool true))))) :: Γ) e₁ t →
      Hastype de κ ((y, (.refine .bool (.fmla (.eq .bool (.fvar .bool x) (.const .bool false))))) :: Γ) e₂ t →
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
      Hastype de κ Γ (.ctor C j τs e) (Ty.dataL C τs (de.ctorRefine C j e))
  | case {de κ Γ e C n args r m alts t} (zs : Fin m → EVar) :
      Ty.WFBVars t →
      Hastype de κ Γ e (.data C n args r) →
      de.nCtors C = some m →
      de.instOK C (List.ofFn args) = true →
      (∀ j, zs j ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ (alts j).fv ++ t.fv) →
      (∀ (j : Fin m) P, de.payload? C j.val = some P →
        zs j ∉ (de.altTy C j.val e.var? (Ty.instTys (List.ofFn args) P)).fv) →
      (∀ (j : Fin m) P, de.payload? C j.val = some P →
        Hastype de κ ((zs j, de.altTy C j.val e.var? (Ty.instTys (List.ofFn args) P)) :: Γ)
          ((alts j).openVar 0 (zs j)) t) →
      Hastype de κ Γ (.case e m alts) t
