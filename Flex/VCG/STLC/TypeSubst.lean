import Flex.VCG.STLC.Substitution

/-! # Semantics of type-variable substitution

  Type variables are sorts of the refinement logic, so the type-level operations
  `Ty.openTv` (opening a type binder) and `Ty.instTy` (type application) retype
  the deep-embedded refinements. This file shows that both are *semantically*
  what they should be:

  * renaming a type-variable sort to another type-variable sort never changes
    the meaning of a refinement (`Refinement.interp_substB_ren`);
  * opening a type binder with `a` is the same as interpreting the binder by
    `a`'s semantic type (`TyDenote.openTv_iff`);
  * rebinding a type variable that does not occur is invisible
    (`TyDenote.set_fresh_iff`).
-/

namespace STLC

/-! ## Recasting between compatible sorts -/

@[simp] theorem BVal.toBVal_toVal (c : BVal) : Val.toBVal (BVal.toVal c) = c := by
  cases c <;> rfl

/-- Two sorts are *compatible* when recasting between them is lossless: equal
    base sorts, or two type-variable sorts. -/
def Base.Compat (b b' : Base) : Prop :=
  (b = .int ∧ b' = .int) ∨ (b = .bool ∧ b' = .bool) ∨ (b.isTv = true ∧ b'.isTv = true)

theorem Base.recast_inj {b b' : Base} (h : Base.Compat b b') {c₁ c₂ : b.interp} :
    Base.recast b b' c₁ = Base.recast b b' c₂ ↔ c₁ = c₂ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h₁, h₂⟩
  · rfl
  · rfl
  · cases b <;> simp [Base.isTv] at h₁ <;> cases b' <;> simp [Base.isTv] at h₂ <;>
      simp [Base.recast, Val.proj, Val.inj]

/-- Comparison commutes with lossless recasting. -/
theorem Base.le_recast {b b' : Base} (h : Base.Compat b b') {c₁ c₂ : b.interp} :
    Base.le b' (Base.recast b b' c₁) (Base.recast b b' c₂) ↔ Base.le b c₁ c₂ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h₁, h₂⟩
  · rfl
  · rfl
  · cases b <;> simp [Base.isTv] at h₁ <;> cases b' <;> simp [Base.isTv] at h₂ <;>
      simp [Base.recast, Val.proj, Val.inj]

theorem Base.canonArg_recast {b b' : Base} (h : Base.Compat b b') (c : b.interp) :
    Base.canonArg b' (Base.recast b b' c) = Base.canonArg b c := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h₁, h₂⟩
  · rfl
  · rfl
  · cases b <;> simp [Base.isTv] at h₁ <;> cases b' <;> simp [Base.isTv] at h₂ <;>
      simp [Base.recast, Val.proj, Val.inj]

/-- A sort substitution is a *renaming* when it sends type-variable sorts to
    type-variable sorts (it always fixes `int`/`bool`). -/
def BSubst.IsRen (σ : BSubst) : Prop := ∀ b : Base, b.isTv = true → (b.substB σ).isTv = true

theorem BSubst.compat_of_ren {σ : BSubst} (hσ : σ.IsRen) (b : Base) : Base.Compat b (b.substB σ) := by
  cases b with
  | int => exact Or.inl ⟨rfl, rfl⟩
  | bool => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | tbvar j => exact Or.inr (Or.inr ⟨rfl, hσ _ rfl⟩)
  | tfvar a => exact Or.inr (Or.inr ⟨rfl, hσ _ rfl⟩)

theorem BSubst.openAt_ren (k : Nat) (a : TVar) : (BSubst.openAt k a).IsRen := by
  intro b hb
  cases b with
  | tbvar j =>
    simp only [Base.substB, BSubst.openAt, BSubst.instAt]
    split
    · rfl
    · split <;> rfl
  | tfvar a' => rfl
  | int | bool => simp [Base.isTv] at hb

/-! ## Renaming is semantically invisible -/

theorem Formula.interp_substB_ren {σ : BSubst} (hσ : σ.IsRen) (φ : Formula) :
    ∀ γ : REnv, Formula.interp γ (φ.substB σ) ↔ Formula.interp γ φ := by
  induction φ with
  | tt | ff => intro γ; rfl
  | eq b t₁ t₂ =>
    intro γ
    simp only [Formula.substB, Formula.interp, Term.interp_substB]
    exact Base.recast_inj (BSubst.compat_of_ren hσ b)
  | leq b t₁ t₂ =>
    intro γ
    simp only [Formula.substB, Formula.interp, Term.interp_substB]
    exact Base.le_recast (BSubst.compat_of_ren hσ b)
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro γ; simp only [Formula.substB, Formula.interp, ih₁, ih₂]
  | not _ ih => intro γ; simp only [Formula.substB, Formula.interp, ih]
  | ex b φ ih | all b φ ih =>
    intro γ
    simp only [Formula.substB, Formula.interp]
    cases b with
    | int | bool => simp only [Base.substB, ih]
    | tbvar j =>
      have h := hσ (.tbvar j) rfl
      revert h
      generalize hb' : (Base.tbvar j).substB σ = b'
      intro h
      cases b' <;> simp [Base.isTv] at h <;> simp [Val.inj, ih]
    | tfvar a =>
      have h := hσ (.tfvar a) rfl
      revert h
      generalize hb' : (Base.tfvar a).substB σ = b'
      intro h
      cases b' <;> simp [Base.isTv] at h <;> simp [Val.inj, ih]

theorem Refinement.interp_substB_ren {κ : KEnv} {σ : BSubst} (hσ : σ.IsRen) (r : Refinement)
    (γ : REnv) : Refinement.interp κ (r.substB σ) γ ↔ Refinement.interp κ r γ := by
  induction r with
  | fmla φ => exact Formula.interp_substB_ren hσ φ γ
  | kapp kn args =>
    simp only [Refinement.substB, Refinement.interp, List.map_map]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply, Term.interp_substB]
    exact Base.canonArg_recast (BSubst.compat_of_ren hσ a.1) _
  | conj _ _ ih₁ ih₂ => simp only [Refinement.substB, Refinement.interp, ih₁, ih₂]

/-! ## Congruence for datatype denotations -/

theorem SemTy.upto_congr {i : Nat} {R R' : Fin (i+1) → Val → Prop}
    (h : ∀ j w, R j w ↔ R' j w) : SemTy.upto i R = SemTy.upto i R' := by
  have : R = R' := funext fun j => funext fun w => propext (h j w)
  subst this; rfl

/-- A datatype's denotation at index `k` depends on its type arguments only
    through their denotations below `k`. -/
theorem TyDenote.data_congr {κ : KEnv} {δ δ' : TyEnvSem} {k : Nat} {C : String} {n : Nat}
    {args args' : Fin n → Ty} {γ γ' : REnv} {v : Val}
    (hden : δ.denv = δ'.denv)
    (hargs : ∀ l, ∀ j < k, ∀ w, TyDenote κ δ j (args l) γ w ↔ TyDenote κ δ' j (args' l) γ' w) :
    TyDenote κ δ k (.data C n args) γ v ↔ TyDenote κ δ' k (.data C n args') γ' v := by
  simp only [TyDenote, hden]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    exists_congr fun j => exists_congr fun w => exists_congr fun P => and_congr_right fun _ =>
      and_congr_right fun _ => forall_congr' fun i => forall_congr' fun hi => ?_
  have : (List.ofFn fun l => SemTy.upto i fun j' w' => TyDenote κ δ j'.val (args l) γ w') =
      List.ofFn fun l => SemTy.upto i fun j' w' => TyDenote κ δ' j'.val (args' l) γ' w' := by
    congr 1; funext l
    exact SemTy.upto_congr fun j' w' => hargs l j'.val (by have := j'.isLt; omega) w'
  rw [this]

/-- Pairs: componentwise congruence. -/
theorem TyDenote.prod_congr {κ : KEnv} {δ δ' : TyEnvSem} {k : Nat} {s t s' t' : Ty}
    {γ γ' : REnv} {v : Val}
    (hs : ∀ w, TyDenote κ δ k s γ w ↔ TyDenote κ δ' k s' γ' w)
    (ht : ∀ w₁ w, TyDenote κ δ k t (γ.push w₁) w ↔ TyDenote κ δ' k t' (γ'.push w₁) w) :
    TyDenote κ δ k (.prod s t) γ v ↔ TyDenote κ δ' k (.prod s' t') γ' v := by
  simp only [TyDenote]
  exact exists_congr fun v₁ => exists_congr fun v₂ => and_congr_right fun _ =>
    and_congr (hs v₁) (ht v₁ v₂)

/-! ## Rebinding an absent type variable -/

/-- Rebind the free type variable `a` to the semantic type `R`. -/
def TyEnvSem.set (δ : TyEnvSem) (a : TVar) (R : SemTy) : TyEnvSem :=
  { δ with fv := fun a' => if a' = a then R else δ.fv a' }

@[simp] theorem TyEnvSem.set_push (δ : TyEnvSem) (a : TVar) (R R' : SemTy) :
    (δ.set a R).push R' = (δ.push R').set a R := rfl

theorem TyEnvSem.set_WK {δ : TyEnvSem} (hδ : δ.WK) (a : TVar) (R : SemTy) (hR : R.Fits a.2) :
    (δ.set a R).WK := by
  intro a'
  simp only [TyEnvSem.set]
  split
  · rename_i h; subst h; exact hR
  · exact hδ a'

theorem BaseDen.set_fresh {δ : TyEnvSem} {a : TVar} {R : SemTy} {k : Nat} {b : Base} {v : Val}
    (ha : a ∉ b.ftv) : BaseDen (δ.set a R) k b v ↔ BaseDen δ k b v := by
  cases b with
  | tfvar a' =>
    have : a' ≠ a := fun h => ha (by simp [Base.ftv, h])
    simp [BaseDen, TyEnvSem.set, this]
  | _ => rfl

theorem TyDenote.set_fresh_iff {κ : KEnv} {a : TVar} {R : SemTy} (t : Ty) (ha : a ∉ t.ftv) :
    ∀ (δ : TyEnvSem) (k : Nat) (γ : REnv) (v : Val),
      TyDenote κ (δ.set a R) k t γ v ↔ TyDenote κ δ k t γ v := by
  induction t with
  | refine b r =>
    intro δ k γ v
    simp only [Ty.ftv, List.mem_append, not_or] at ha
    simp only [TyDenote, BaseDen.set_fresh ha.1]
  | arrow s t ihs iht =>
    intro δ k γ v
    simp only [Ty.ftv, List.mem_append, not_or] at ha
    simp only [TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    refine forall_congr' (fun j => forall_congr' (fun _ => forall_congr' (fun va => ?_)))
    rw [ihs ha.1]
    refine imp_congr_right (fun _ => exists_congr (fun body => exists_congr (fun o =>
      and_congr_right (fun _ => and_congr_right (fun _ => ?_)))))
    exact forall_congr' (fun vr => forall_congr' (fun m => imp_congr_right (fun _ =>
      imp_congr_right (fun _ => iht ha.2 δ m _ vr))))
  | «forall» kd t ih =>
    intro δ k γ v
    simp only [Ty.ftv] at ha
    simp only [TyDenote]
    exact forall_congr' (fun R' => forall_congr' (fun _ => by
      rw [TyEnvSem.set_push]; exact ih ha (δ.push R') k γ v))
  | prod s t ihs iht =>
    intro δ k γ v
    simp only [Ty.ftv, List.mem_append, not_or] at ha
    exact TyDenote.prod_congr (fun w => ihs ha.1 δ k γ w) (fun w₁ w => iht ha.2 δ k _ w)
  | data C n args ih =>
    intro δ k γ v
    simp only [Ty.ftv, List.mem_flatMap, List.mem_finRange, true_and, not_exists] at ha
    exact TyDenote.data_congr rfl (fun l j _ w => ih l (ha l) δ j γ w)

/-! ## Opening a type binder -/

/-- Base denotations under opening: the opened level reads `a`'s interpretation,
    deeper levels shift down. -/
theorem BaseDen.openAt (ρ ρ₀ : List SemTy) (η : TVar → SemTy) (D : DEnv) (a : TVar) (R : SemTy)
    {k : Nat} {b : Base} {v : Val} (ha : a ∉ b.ftv) :
    BaseDen ⟨ρ ++ R :: ρ₀, η, D⟩ k b v ↔
    BaseDen ((⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).set a R) k (b.substB (BSubst.openAt ρ.length a)) v := by
  cases b with
  | int | bool => rfl
  | tfvar a' =>
    have : a' ≠ a := fun h => ha (by simp [Base.ftv, h])
    simp [BaseDen, Base.substB, BSubst.openAt, BSubst.instAt, TyEnvSem.set, this]
  | tbvar j =>
    simp only [Base.substB, BSubst.openAt, BSubst.instAt]
    by_cases h₁ : j = ρ.length
    · subst h₁
      simp [BaseDen, TyEnvSem.set]
    · by_cases h₂ : ρ.length < j
      · simp only [h₁, h₂, if_false, if_true, BaseDen]
        have e₁ : (ρ ++ R :: ρ₀)[j]? = ρ₀[j - ρ.length - 1]? := by
          rw [List.getElem?_append_right (by omega)]
          rw [show j - ρ.length = (j - ρ.length - 1) + 1 by omega]
          simp
        have e₂ : (ρ ++ ρ₀)[j - 1]? = ρ₀[j - ρ.length - 1]? := by
          rw [List.getElem?_append_right (by omega)]
          congr 1; omega
        simp [TyEnvSem.set, e₁, e₂]
      · simp only [h₁, h₂, if_false, BaseDen]
        have hj : j < ρ.length := by omega
        simp [TyEnvSem.set, List.getElem?_append_left hj]

/-- Opening a type binder with a fresh `a` is the same as interpreting the
    binder by `a`'s semantic type. -/
theorem TyDenote.openTv_iff {κ : KEnv} (a : TVar) (R : SemTy) (t : Ty) (ha : a ∉ t.ftv) :
    ∀ (ρ ρ₀ : List SemTy) (η : TVar → SemTy) (D : DEnv) (k : Nat) (γ : REnv) (v : Val),
      TyDenote κ ⟨ρ ++ R :: ρ₀, η, D⟩ k t γ v ↔
      TyDenote κ ((⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).set a R) k (t.openTv ρ.length a) γ v := by
  induction t with
  | refine b r =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.ftv, List.mem_append, not_or] at ha
    simp only [Ty.openTv, TyDenote]
    rw [BaseDen.openAt ρ ρ₀ η D a R ha.1,
        Refinement.interp_substB_ren (BSubst.openAt_ren _ _)]
  | arrow s t ihs iht =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.ftv, List.mem_append, not_or] at ha
    simp only [Ty.openTv, TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    refine forall_congr' (fun j => forall_congr' (fun _ => forall_congr' (fun va => ?_)))
    rw [ihs ha.1]
    refine imp_congr_right (fun _ => exists_congr (fun body => exists_congr (fun o =>
      and_congr_right (fun _ => and_congr_right (fun _ => ?_)))))
    exact forall_congr' (fun vr => forall_congr' (fun m => imp_congr_right (fun _ =>
      imp_congr_right (fun _ => iht ha.2 ρ ρ₀ η D m _ vr))))
  | «forall» kd t ih =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.ftv] at ha
    simp only [Ty.openTv, TyDenote]
    refine forall_congr' (fun R' => forall_congr' (fun _ => ?_))
    have := ih ha (R' :: ρ) ρ₀ η D k γ v
    simpa [TyEnvSem.push, TyEnvSem.set] using this
  | prod s t ihs iht =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.ftv, List.mem_append, not_or] at ha
    simp only [Ty.openTv]
    exact TyDenote.prod_congr (fun w => ihs ha.1 ρ ρ₀ η D k γ w)
      (fun w₁ w => iht ha.2 ρ ρ₀ η D k _ w)
  | data C n args ih =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.ftv, List.mem_flatMap, List.mem_finRange, true_and, not_exists] at ha
    simp only [Ty.openTv]
    exact TyDenote.data_congr rfl (fun l j _ w => ih l (ha l) ρ ρ₀ η D j γ w)

/-- The `∀`-instance of `openTv_iff`: entering a type binder by `R` is opening it
    with a fresh `a` interpreted by `R`. -/
theorem TyDenote.push_openTv_iff {κ : KEnv} (δ : TyEnvSem) (a : TVar) (R : SemTy) (t : Ty)
    (ha : a ∉ t.ftv) (k : Nat) (γ : REnv) (v : Val) :
    TyDenote κ (δ.push R) k t γ v ↔ TyDenote κ (δ.set a R) k (t.openTv 0 a) γ v := by
  have := TyDenote.openTv_iff (κ := κ) a R t ha [] δ.bv δ.fv δ.denv k γ v
  simpa [TyEnvSem.push] using this

/-! ## Closing a type variable (generalization) -/

theorem BSubst.closeAt_ren (k : Nat) (a : TVar) : (BSubst.closeAt k a).IsRen := by
  intro b hb
  cases b with
  | tbvar j => simp only [Base.substB, BSubst.closeAt]; split <;> rfl
  | tfvar a' => simp only [Base.substB, BSubst.closeAt]; split <;> rfl
  | int | bool => simp [Base.isTv] at hb

theorem BaseDen.closeAt (ρ ρ₀ : List SemTy) (η : TVar → SemTy) (D : DEnv) (a : TVar) (R : SemTy)
    {k : Nat} {b : Base} {v : Val} :
    BaseDen ⟨ρ ++ R :: ρ₀, η, D⟩ k (b.substB (BSubst.closeAt ρ.length a)) v ↔
    BaseDen ((⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).set a R) k b v := by
  cases b with
  | int | bool => rfl
  | tfvar a' =>
    simp only [Base.substB, BSubst.closeAt]
    by_cases h : a' = a
    · subst h; simp [BaseDen, TyEnvSem.set]
    · simp [BaseDen, TyEnvSem.set, h]
  | tbvar j =>
    simp only [Base.substB, BSubst.closeAt]
    by_cases h : ρ.length ≤ j
    · simp only [h, if_true, BaseDen]
      have e₁ : (ρ ++ R :: ρ₀)[j + 1]? = ρ₀[j - ρ.length]? := by
        rw [List.getElem?_append_right (by omega)]
        rw [show j + 1 - ρ.length = (j - ρ.length) + 1 by omega]
        simp
      have e₂ : (ρ ++ ρ₀)[j]? = ρ₀[j - ρ.length]? := List.getElem?_append_right h
      simp [TyEnvSem.set, e₁, e₂]
    · simp only [h, if_false, BaseDen]
      have hj : j < ρ.length := by omega
      simp [TyEnvSem.set, List.getElem?_append_left hj]

/-- Closing `a` as a type binder interpreted by `R` is interpreting `a` by `R`. -/
theorem TyDenote.closeTv_iff {κ : KEnv} (a : TVar) (R : SemTy) (t : Ty) :
    ∀ (ρ ρ₀ : List SemTy) (η : TVar → SemTy) (D : DEnv) (k : Nat) (γ : REnv) (v : Val),
      TyDenote κ ⟨ρ ++ R :: ρ₀, η, D⟩ k (t.closeTv ρ.length a) γ v ↔
      TyDenote κ ((⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).set a R) k t γ v := by
  induction t with
  | refine b r =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.closeTv, TyDenote]
    rw [BaseDen.closeAt ρ ρ₀ η D a R,
        Refinement.interp_substB_ren (BSubst.closeAt_ren _ _)]
  | arrow s t ihs iht =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.closeTv, TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    refine forall_congr' (fun j => forall_congr' (fun _ => forall_congr' (fun va => ?_)))
    rw [ihs ρ ρ₀ η D]
    refine imp_congr_right (fun _ => exists_congr (fun body => exists_congr (fun o =>
      and_congr_right (fun _ => and_congr_right (fun _ => ?_)))))
    exact forall_congr' (fun vr => forall_congr' (fun m => imp_congr_right (fun _ =>
      imp_congr_right (fun _ => iht ρ ρ₀ η D m _ vr))))
  | «forall» kd t ih =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.closeTv, TyDenote]
    refine forall_congr' (fun R' => forall_congr' (fun _ => ?_))
    have := ih (R' :: ρ) ρ₀ η D k γ v
    simpa [TyEnvSem.push, TyEnvSem.set] using this
  | prod s t ihs iht =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.closeTv]
    exact TyDenote.prod_congr (fun w => ihs ρ ρ₀ η D k γ w)
      (fun w₁ w => iht ρ ρ₀ η D k _ w)
  | data C n args ih =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.closeTv]
    exact TyDenote.data_congr rfl (fun l j _ w => ih l ρ ρ₀ η D j γ w)

/-- `δ'` re-interprets (some of) the type variables `as` of `δ`, legally. -/
inductive TyEnvSem.Reinterp (as : List TVar) : TyEnvSem → TyEnvSem → Prop
  | refl (δ : TyEnvSem) : TyEnvSem.Reinterp as δ δ
  | set {δ δ' : TyEnvSem} (a : TVar) (R : SemTy) :
      a ∈ as → R.Fits a.2 → TyEnvSem.Reinterp as δ δ' → TyEnvSem.Reinterp as δ (δ'.set a R)

theorem TyEnvSem.Reinterp.trans {as : List TVar} {δ₁ δ₂ δ₃ : TyEnvSem}
    (h₁ : TyEnvSem.Reinterp as δ₁ δ₂) (h₂ : TyEnvSem.Reinterp as δ₂ δ₃) :
    TyEnvSem.Reinterp as δ₁ δ₃ := by
  induction h₂ with
  | refl => exact h₁
  | set a R ha hR _ ih => exact .set a R ha hR ih

theorem TyEnvSem.Reinterp.WK {as : List TVar} {δ δ' : TyEnvSem}
    (h : TyEnvSem.Reinterp as δ δ') (hδ : δ.WK) : δ'.WK := by
  induction h with
  | refl => exact hδ
  | set a R _ hR _ ih => exact TyEnvSem.set_WK ih a R hR

theorem TyEnvSem.Reinterp.denv {as : List TVar} {δ δ' : TyEnvSem}
    (h : TyEnvSem.Reinterp as δ δ') : δ'.denv = δ.denv := by
  induction h with
  | refl => rfl
  | set _ _ _ _ _ ih => exact ih

theorem TyEnvSem.Reinterp.cons {a : TVar} {as : List TVar} {δ δ' : TyEnvSem} {R : SemTy}
    (hR : R.Fits a.2) (h : TyEnvSem.Reinterp as (δ.set a R) δ') :
    TyEnvSem.Reinterp (a :: as) δ δ' := by
  induction h with
  | refl => exact .set a R List.mem_cons_self hR (.refl δ)
  | set a' R' ha' hR' _ ih => exact .set a' R' (List.mem_cons_of_mem _ ha') hR' ih

/-- Introducing a generalized type: a value that is in `t` under every legal
    re-interpretation of `as` is in `∀ as. t`. -/
theorem TyDenote.gen_intro {κ : KEnv} {k : Nat} {t : Ty} {γ : REnv} {v : Val} :
    ∀ (as : List TVar) (δ : TyEnvSem),
      (∀ δ', TyEnvSem.Reinterp as δ δ' → TyDenote κ δ' k t γ v) →
      TyDenote κ δ k (Ty.gen as t) γ v
  | [], δ, h => h δ (.refl δ)
  | a :: as, δ, h => by
    simp only [Ty.gen, TyDenote]
    intro R hR
    have := TyDenote.closeTv_iff (κ := κ) a R (Ty.gen as t) [] δ.bv δ.fv δ.denv k γ v
    simp only [List.nil_append, List.length_nil] at this
    refine this.mpr (TyDenote.gen_intro as _ (fun δ' h' => h δ' (TyEnvSem.Reinterp.cons hR h')))

/-! ## Congruence: a refinement reads only the slots it mentions -/

theorem Term.interp_congr {γ γ' : REnv} (hmap : γ.map = γ'.map) :
    ∀ {b : Base} (t : Term b), (∀ c k, Term.hasBVar c k t → γ.bv[k]? = γ'.bv[k]?) →
      Term.interp γ t = Term.interp γ' t := by
  intro b t
  induction t with
  | const _ _ => intro _; rfl
  | bvar b k =>
    intro h
    simp only [Term.interp, REnv.getBV, h b k ⟨rfl, rfl⟩]
  | fvar b x => intro _; simp only [Term.interp, REnv.get, REnv.lookup, hmap]
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ =>
    intro h
    simp only [Term.interp,
      ih₁ (fun c k hk => h c k (Or.inl hk)), ih₂ (fun c k hk => h c k (Or.inr hk))]
  | not _ ih => intro h; simp only [Term.interp, ih h]

theorem Formula.interp_congr (φ : Formula) : ∀ {γ γ' : REnv}, γ.map = γ'.map →
    (∀ c k, Formula.hasBVar c k φ → γ.bv[k]? = γ'.bv[k]?) →
    (Formula.interp γ φ ↔ Formula.interp γ' φ) := by
  induction φ with
  | tt | ff => intros; rfl
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro γ γ' hmap h
    simp only [Formula.interp,
      Term.interp_congr hmap t₁ (fun c k hk => h c k (Or.inl hk)),
      Term.interp_congr hmap t₂ (fun c k hk => h c k (Or.inr hk))]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro γ γ' hmap h
    simp only [Formula.interp,
      ih₁ hmap (fun c k hk => h c k (Or.inl hk)), ih₂ hmap (fun c k hk => h c k (Or.inr hk))]
  | not _ ih => intro γ γ' hmap h; simp only [Formula.interp, ih hmap h]
  | ex b φ ih | all b φ ih =>
    intro γ γ' hmap h
    simp only [Formula.interp]
    have key : ∀ w : Val, Formula.interp (γ.push w) φ ↔ Formula.interp (γ'.push w) φ := by
      intro w
      refine ih hmap (fun c k hk => ?_)
      cases k with
      | zero => rfl
      | succ k => exact h c k hk
    first
      | exact exists_congr (fun x => key _)
      | exact forall_congr' (fun x => key _)

theorem Refinement.interp_congr {κ : KEnv} (r : Refinement) {γ γ' : REnv} (hmap : γ.map = γ'.map)
    (h : ∀ c k, Refinement.hasBVar c k r → γ.bv[k]? = γ'.bv[k]?) :
    Refinement.interp κ r γ ↔ Refinement.interp κ r γ' := by
  induction r with
  | fmla φ => exact Formula.interp_congr φ hmap h
  | kapp kn args =>
    simp only [Refinement.interp]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a ha
    rw [Term.interp_congr hmap a.2 (fun c k hk => h c k ⟨a, ha, hk⟩)]
  | conj _ _ ih₁ ih₂ =>
    simp only [Refinement.interp,
      ih₁ (fun c k hk => h c k (Or.inl hk)), ih₂ (fun c k hk => h c k (Or.inr hk))]

/-- A well-formed type's denotation depends only on the type-variable
    interpretations and term-stack slots in scope. -/
theorem TyDenote.congr_wf {κ : KEnv} (t : Ty) :
    ∀ (kctx : List Kind) (ctx : List (Option Base)) (ρ₁ ρ ρ' : List SemTy) (η : TVar → SemTy)
      (D : DEnv) (k : Nat) (γ γ' : REnv) (v : Val),
      t.wfB kctx ctx = true → kctx.length = ρ₁.length → γ.map = γ'.map →
      (∀ i < ctx.length, γ.bv[i]? = γ'.bv[i]?) →
      (TyDenote κ ⟨ρ₁ ++ ρ, η, D⟩ k t γ v ↔ TyDenote κ ⟨ρ₁ ++ ρ', η, D⟩ k t γ' v) := by
  induction t with
  | refine b r =>
    intro kctx ctx ρ₁ ρ ρ' η D k γ γ' v hw hlen hmap hbv
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    obtain ⟨⟨hty, _⟩, hr⟩ := hw
    simp only [TyDenote]
    apply and_congr
    · cases b with
      | tbvar j =>
        simp only [Base.tyOK, decide_eq_true_eq] at hty
        have hj : j < ρ₁.length := hlen ▸ hty
        simp [BaseDen, List.getElem?_append_left hj]
      | _ => rfl
    · apply Refinement.interp_congr r (by simpa using hmap)
      intro c i hi
      have := Refinement.wfB_hasBVar r hr c i hi
      cases i with
      | zero => rfl
      | succ i =>
        rcases Nat.lt_or_ge i ctx.length with hi' | hi'
        · exact hbv i hi'
        · rw [List.getElem?_cons_succ, List.getElem?_eq_none_iff.mpr hi'] at this
          cases this
  | arrow s t ihs iht =>
    intro kctx ctx ρ₁ ρ ρ' η D k γ γ' v hw hlen hmap hbv
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    simp only [TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    refine forall_congr' (fun j => forall_congr' (fun _ => forall_congr' (fun va => ?_)))
    rw [ihs kctx ctx ρ₁ ρ ρ' η D j γ γ' va hw.1 hlen hmap hbv]
    refine imp_congr_right (fun _ => exists_congr (fun body => exists_congr (fun o =>
      and_congr_right (fun _ => and_congr_right (fun _ => ?_)))))
    refine forall_congr' (fun vr => forall_congr' (fun m => imp_congr_right (fun _ =>
      imp_congr_right (fun _ => ?_))))
    refine iht kctx (s.optBase :: ctx) ρ₁ ρ ρ' η D m (γ.push va) (γ'.push va) vr hw.2 hlen
      (by simpa using hmap) (fun i hi => ?_)
    cases i with
    | zero => rfl
    | succ i => exact hbv i (by simpa using hi)
  | «forall» kd t ih =>
    intro kctx ctx ρ₁ ρ ρ' η D k γ γ' v hw hlen hmap hbv
    simp only [Ty.wfB] at hw
    simp only [TyDenote]
    refine forall_congr' (fun R => forall_congr' (fun _ => ?_))
    exact ih (kd :: kctx) _ (R :: ρ₁) ρ ρ' η D k γ γ' v hw (by simp [hlen]) hmap
      (fun i hi => hbv i (by simpa using hi))
  | prod s t ihs iht =>
    intro kctx ctx ρ₁ ρ ρ' η D k γ γ' v hw hlen hmap hbv
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    refine TyDenote.prod_congr (fun w => ihs kctx ctx ρ₁ ρ ρ' η D k γ γ' w hw.1 hlen hmap hbv)
      (fun w₁ w => iht kctx (s.optBase :: ctx) ρ₁ ρ ρ' η D k (γ.push w₁) (γ'.push w₁) w hw.2 hlen
        (by simpa using hmap) (fun i hi => ?_))
    cases i with
    | zero => rfl
    | succ i => exact hbv i (by simpa using hi)
  | data C n args ih =>
    intro kctx ctx ρ₁ ρ ρ' η D k γ γ' v hw hlen hmap hbv
    simp only [Ty.wfB, List.all_eq_true, List.mem_finRange, true_implies] at hw
    exact TyDenote.data_congr rfl
      (fun l j _ w => ih l kctx ctx ρ₁ ρ ρ' η D j γ γ' w (hw l) hlen hmap hbv)

/-! ## Instantiating a type variable at a base sort

  Retyping along `α ↦ b'` (`b'` = `Int` or `Bool`) preserves meaning, provided
  every `α`-sorted slot a refinement reads holds a value of sort `b'`. Under
  `wfB`, `α`-sorted terms are bound variables only, so these slots are all the
  refinement can observe at sort `α`. -/

/-- The `α = tbvar n`-sorted slots of the stack hold values of sort `b'` (only
    required when `α` is `B`-kinded: ⋆-kinded variables are never read). -/
def SlotsOK (kctx : List Kind) (ctx : List (Option Base)) (n : Nat) (b' : Base) (γ : REnv) : Prop :=
  ∀ i : Nat, ctx[i]? = some (some (Base.tbvar n)) → kctx[n]? = some Kind.B →
    ∃ w : Val, γ.bv[i]? = some w ∧ w.optBase = some b'

theorem SlotsOK.push {kctx : List Kind} {ctx : List (Option Base)} {n : Nat} {b' : Base} {γ : REnv}
    (h : SlotsOK kctx ctx n b' γ) (c : Option Base) (w : Val)
    (hw : c = some (.tbvar n) → kctx[n]? = some .B → w.optBase = some b') :
    SlotsOK kctx (c :: ctx) n b' (γ.push w) := by
  unfold SlotsOK at h ⊢
  intro i hi hB
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    exact ⟨w, rfl, hw hi hB⟩
  | succ i => exact h i (by simpa using hi) hB

/-- Recasting from a type-variable sort to a base sort is injective on values
    of that base sort. -/
theorem Base.proj_inj_of_optBase {b' : Base} (hb' : b' = .int ∨ b' = .bool) {w₁ w₂ : Val}
    (h₁ : w₁.optBase = some b') (h₂ : w₂.optBase = some b') :
    Val.proj b' w₁ = Val.proj b' w₂ ↔ Val.toBVal w₁ = Val.toBVal w₂ := by
  rcases hb' with rfl | rfl <;> cases w₁ <;> simp [Val.optBase] at h₁ <;>
    cases w₂ <;> simp [Val.optBase] at h₂ <;> simp

/-- On values of one base sort, the order at that sort is the order on codes:
    the per-sort orders are restrictions of `BVal.le`. -/
theorem Base.le_proj_of_optBase {b' : Base} (hb' : b' = .int ∨ b' = .bool) {w₁ w₂ : Val}
    (h₁ : w₁.optBase = some b') (h₂ : w₂.optBase = some b') :
    Base.le b' (Val.proj b' w₁) (Val.proj b' w₂) ↔ BVal.le (Val.toBVal w₁) (Val.toBVal w₂) := by
  rcases hb' with rfl | rfl <;> cases w₁ <;> simp [Val.optBase] at h₁ <;>
    cases w₂ <;> simp [Val.optBase] at h₂ <;> simp [BVal.le]

theorem Base.recast_tbvar_proj (j : Nat) (b' : Base) (w : Val) :
    Base.recast (.tbvar j) b' (Val.proj (.tbvar j) w) = Val.proj b' w :=
  Val.proj_toVal_toBVal b' w

theorem BSubst.instAt_compat {n : Nat} {b' : Base} (b : Base) (hb : b ≠ .tbvar n) :
    Base.Compat b (b.substB (BSubst.instAt n b')) := by
  cases b with
  | int => exact Or.inl ⟨rfl, rfl⟩
  | bool => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | tfvar a => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | tbvar j =>
    have hj : j ≠ n := fun h => hb (by rw [h])
    refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    simp only [Base.substB, BSubst.instAt, hj, if_false]
    split <;> rfl

theorem Formula.interp_substB_inst {n : Nat} {b' : Base} (hb' : b' = .int ∨ b' = .bool)
    (φ : Formula) : ∀ {kctx : List Kind} {ctx : List (Option Base)} {γ : REnv},
      φ.wfB kctx ctx = true → SlotsOK kctx ctx n b' γ →
      (Formula.interp γ (φ.substB (BSubst.instAt n b')) ↔ Formula.interp γ φ) := by
  induction φ with
  | tt | ff => intros; rfl
  | eq c t₁ t₂ =>
    intro kctx ctx γ hw hs
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    by_cases hc : c = .tbvar n
    · subst hc
      cases t₁ with
      | const _ _ => simp [Term.wfB, Base.isTv] at hw
      | fvar _ _ => simp [Term.wfB, Base.fvOK] at hw
      | bvar _ i₁ =>
      cases t₂ with
      | const _ _ => simp [Term.wfB, Base.isTv] at hw
      | fvar _ _ => simp [Term.wfB, Base.fvOK] at hw
      | bvar _ i₂ =>
      simp only [Term.wfB, Bool.and_eq_true, beq_iff_eq, Base.sortOK] at hw
      obtain ⟨⟨hi₁, hB⟩, hi₂, -⟩ := hw
      unfold SlotsOK at hs
      obtain ⟨w₁, hw₁, ho₁⟩ := hs i₁ hi₁ hB
      obtain ⟨w₂, hw₂, ho₂⟩ := hs i₂ hi₂ hB
      have hsub : (Base.tbvar n).substB (BSubst.instAt n b') = b' := by
        simp [Base.substB, BSubst.instAt]
      simp only [Formula.substB, Formula.interp, Term.interp_substB, Term.interp,
        REnv.getBV, hw₁, hw₂, Option.getD_some]
      rw [hsub, Base.recast_tbvar_proj, Base.recast_tbvar_proj]
      exact Base.proj_inj_of_optBase hb' ho₁ ho₂
    · simp only [Formula.substB, Formula.interp, Term.interp_substB]
      exact Base.recast_inj (BSubst.instAt_compat c hc)
  | leq c t₁ t₂ =>
    intro kctx ctx γ hw hs
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    by_cases hc : c = .tbvar n
    · subst hc
      cases t₁ with
      | const _ _ => simp [Term.wfB, Base.isTv] at hw
      | fvar _ _ => simp [Term.wfB, Base.fvOK] at hw
      | bvar _ i₁ =>
      cases t₂ with
      | const _ _ => simp [Term.wfB, Base.isTv] at hw
      | fvar _ _ => simp [Term.wfB, Base.fvOK] at hw
      | bvar _ i₂ =>
      simp only [Term.wfB, Bool.and_eq_true, beq_iff_eq, Base.sortOK] at hw
      obtain ⟨⟨hi₁, hB⟩, hi₂, -⟩ := hw
      unfold SlotsOK at hs
      obtain ⟨w₁, hw₁, ho₁⟩ := hs i₁ hi₁ hB
      obtain ⟨w₂, hw₂, ho₂⟩ := hs i₂ hi₂ hB
      have hsub : (Base.tbvar n).substB (BSubst.instAt n b') = b' := by
        simp [Base.substB, BSubst.instAt]
      simp only [Formula.substB, Formula.interp, Term.interp_substB, Term.interp,
        REnv.getBV, hw₁, hw₂, Option.getD_some]
      rw [hsub, Base.recast_tbvar_proj, Base.recast_tbvar_proj]
      exact Base.le_proj_of_optBase hb' ho₁ ho₂
    · simp only [Formula.substB, Formula.interp, Term.interp_substB]
      exact Base.le_recast (BSubst.instAt_compat c hc)
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro kctx ctx γ hw hs
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.substB, Formula.interp, ih₁ hw.1 hs, ih₂ hw.2 hs]
  | not _ ih =>
    intro kctx ctx γ hw hs
    simp only [Formula.wfB] at hw
    simp only [Formula.substB, Formula.interp, ih hw hs]
  | ex c φ ih | all c φ ih =>
    intro kctx ctx γ hw hs
    simp only [Formula.wfB, Bool.and_eq_true, Bool.not_eq_true'] at hw
    obtain ⟨hc, hw⟩ := hw
    have key : ∀ w : Val, (Formula.interp (γ.push w) (φ.substB (BSubst.instAt n b')) ↔
        Formula.interp (γ.push w) φ) := fun w =>
      ih hw (hs.push _ w (fun h => by cases h; simp [Base.isTv] at hc))
    cases c with
    | int | bool =>
      simp only [Formula.substB, Formula.interp, Base.substB]
      first
        | exact exists_congr (fun x => key _)
        | exact forall_congr' (fun x => key _)
    | tbvar _ | tfvar _ => simp [Base.isTv] at hc

theorem Refinement.interp_substB_inst {κ : KEnv} {n : Nat} {b' : Base} (hb' : b' = .int ∨ b' = .bool)
    (r : Refinement) {kctx : List Kind} {ctx : List (Option Base)} {γ : REnv}
    (hw : r.wfB kctx ctx = true) (hs : SlotsOK kctx ctx n b' γ) :
    Refinement.interp κ (r.substB (BSubst.instAt n b')) γ ↔ Refinement.interp κ r γ := by
  induction r with
  | fmla φ => exact Formula.interp_substB_inst hb' φ hw hs
  | kapp kn args =>
    simp only [Refinement.wfB, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hw
    simp only [Refinement.substB, Refinement.interp, List.map_map]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a ha
    simp only [Function.comp_apply, Term.interp_substB]
    have hnt : a.1 ≠ .tbvar n := fun h => by have := (hw a ha).1; rw [h] at this; simp [Base.isTv] at this
    exact Base.canonArg_recast (BSubst.instAt_compat a.1 hnt) _
  | conj _ _ ih₁ ih₂ =>
    simp only [Refinement.wfB, Bool.and_eq_true] at hw
    simp only [Refinement.substB, Refinement.interp, ih₁ hw.1, ih₂ hw.2]

/-! ## The substitution lemma for type application -/

theorem Refinement.interp_of_isTT {κ : KEnv} {r : Refinement} (h : r.isTT = true) (γ : REnv) :
    Refinement.interp κ r γ := by
  induction r with
  | fmla φ => cases φ <;> simp_all [Refinement.isTT, Refinement.interp, Formula.interp]
  | conj r₁ r₂ ih₁ ih₂ =>
    simp only [Refinement.isTT, Bool.and_eq_true] at h
    exact ⟨ih₁ h.1, ih₂ h.2⟩
  | kapp => simp [Refinement.isTT] at h

/-- The shape of a `B`-kinded instance: a refined base type or `B`-kinded type
    variable. -/
theorem Ty.kindOf_B {s : Ty} (h : s.kindOf = .B) :
    ∃ b' r', s = .refine b' r' ∧ (b' = .int ∨ b' = .bool ∨ ∃ n, b' = .tfvar (n, .B)) := by
  match s, h with
  | .refine .int r, _ => exact ⟨_, r, rfl, Or.inl rfl⟩
  | .refine .bool r, _ => exact ⟨_, r, rfl, Or.inr (Or.inl rfl)⟩
  | .refine (.tfvar (n, .B)) r, _ => exact ⟨_, r, rfl, Or.inr (Or.inr ⟨n, rfl⟩)⟩
  | .refine (.tfvar (_, .star)) _, h => simp [Ty.kindOf] at h
  | .refine (.tbvar _) _, h => simp [Ty.kindOf] at h
  | .arrow _ _, h => simp [Ty.kindOf] at h
  | .forall _ _, h => simp [Ty.kindOf] at h

/-- Sort substitutions at a type-variable sort are renamings. -/
theorem BSubst.instAt_ren_of_tv {n : Nat} {b' : Base} (hb' : b'.isTv = true) :
    (BSubst.instAt n b').IsRen := by
  intro b hb
  cases b with
  | tbvar j =>
    simp only [Base.substB, BSubst.instAt]
    split
    · exact hb'
    · split <;> rfl
  | tfvar _ => rfl
  | int | bool => simp [Base.isTv] at hb

/-- Base denotations are unaffected by the bound-variable stack beyond the
    instantiated level, for sorts other than that level. -/
theorem BaseDen.instAt_ne (ρ ρ₀ : List SemTy) (η : TVar → SemTy) (D : DEnv) (R : SemTy)
    {kctx : List Kind}
    {k : Nat} {b : Base} {v : Val} (hb : b ≠ .tbvar ρ.length) (hty : b.tyOK kctx = true)
    (hlen : kctx.length = ρ.length + 1) (b' : Base) :
    BaseDen ⟨ρ ++ R :: ρ₀, η, D⟩ k b v ↔
    BaseDen ⟨ρ ++ ρ₀, η, D⟩ k (b.substB (BSubst.instAt ρ.length b')) v := by
  cases b with
  | int | bool => rfl
  | tfvar a => rfl
  | tbvar j =>
    simp only [Base.tyOK, decide_eq_true_eq] at hty
    have hj : j < ρ.length := by
      have : j ≠ ρ.length := fun h => hb (by rw [h])
      omega
    have hne : ¬ j = ρ.length := by omega
    have hlt : ¬ ρ.length < j := by omega
    simp only [Base.substB, BSubst.instAt, hne, hlt, if_false, BaseDen]
    simp [List.getElem?_append_left hj]

/-- **Substitution lemma.** Interpreting the type variable by the semantic type
    `R = ⟦s⟧` is the same as substituting `s` for it (with λ_RF's refinement
    strengthening). `kctx`/`ctx` track the enclosing binders; `SlotsOK` records
    that `α`-sorted stack slots hold values of `s`'s sort. `R` need only agree
    with `⟦s⟧` up to the index at which the types are compared. -/
theorem TyDenote.instTy_iff {κ : KEnv} (s : Ty) (kd : Kind) (hs : s.wfB [] [] = true)
    (hk : Kind.le s.kindOf kd) (δ₀ : TyEnvSem) (γ₀ : REnv) (R : SemTy) :
    ∀ (t : Ty) (ρ ρ₀ : List SemTy) (kctx : List Kind) (ctx : List (Option Base))
      (k : Nat) (γ : REnv) (v : Val),
      (∀ k' ≤ k, ∀ w, R.rel k' w ↔ TyDenote κ δ₀ k' s γ₀ w) →
      t.wfB kctx ctx = true → kctx.length = ρ.length + 1 → kctx[ρ.length]? = some kd →
      γ.map = γ₀.map →
      ((s.sortOf = .int ∨ s.sortOf = .bool) → SlotsOK kctx ctx ρ.length s.sortOf γ) →
      (TyDenote κ ⟨ρ ++ R :: ρ₀, δ₀.fv, δ₀.denv⟩ k t γ v ↔
       TyDenote κ ⟨ρ ++ ρ₀, δ₀.fv, δ₀.denv⟩ k (Ty.instTy ρ.length s t) γ v) := by
  -- Values of `R` at a `B`-kinded variable have `s`'s sort.
  have hRval : kd = .B → (s.sortOf = .int ∨ s.sortOf = .bool) →
      ∀ k w, (R.rel k w ↔ TyDenote κ δ₀ k s γ₀ w) → R.rel k w → w.optBase = some s.sortOf := by
    intro hkd hb' k w hRk hw
    subst hkd
    have hsB : s.kindOf = .B := by
      rcases hk with h | h
      · exact h
      · cases h
    obtain ⟨b', r', rfl, hb'₂⟩ := Ty.kindOf_B hsB
    have := hRk.mp hw
    simp only [TyDenote] at this
    simp only [Ty.sortOf] at hb'
    rcases hb' with rfl | rfl
    · obtain ⟨n, rfl⟩ := this.1; rfl
    · obtain ⟨c, rfl⟩ := this.1; rfl
  -- The refinement of a binding, retyped along the instantiation.
  have hrefn : ∀ (r : Refinement) (kctx : List Kind) (ctx : List (Option Base)) (b : Base)
      (n : Nat) (γ : REnv) (v : Val),
      r.wfB kctx (some b :: ctx) = true →
      ((s.sortOf = .int ∨ s.sortOf = .bool) → SlotsOK kctx ctx n s.sortOf γ) →
      ((s.sortOf = .int ∨ s.sortOf = .bool) → b = .tbvar n → kctx[n]? = some .B →
        v.optBase = some s.sortOf) →
      (Refinement.interp κ (r.substB (BSubst.instAt n s.sortOf)) (γ.push v) ↔
       Refinement.interp κ r (γ.push v)) := by
    intro r kctx ctx b n γ v hw hslots hv
    by_cases hb' : s.sortOf = .int ∨ s.sortOf = .bool
    · refine Refinement.interp_substB_inst hb' r hw ((hslots hb').push _ v ?_)
      intro hc hB
      exact hv hb' (Option.some.inj hc) hB
    · have htv : s.sortOf.isTv = true := by
        cases h : s.sortOf <;> simp_all [Base.isTv]
      exact Refinement.interp_substB_ren (BSubst.instAt_ren_of_tv htv) r _
  intro t
  induction t with
  | refine b r =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap hslots
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    obtain ⟨⟨hty, hstar⟩, hr⟩ := hw
    by_cases hbk : b = .tbvar ρ.length
    · subst hbk
      simp only [Ty.instTy, if_true]
      simp only [TyDenote, BaseDen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      rw [hR k (Nat.le_refl _) v]
      -- the binder's own refinement, retyped
      have hr' := hrefn r kctx ctx _ ρ.length γ v hr hslots
      match s, hs, hk, hr' with
      | .refine b' r', hs, hk, hr' =>
        simp only [Ty.wfB, Bool.and_eq_true] at hs
        obtain ⟨⟨hty', _⟩, hr's⟩ := hs
        simp only [Ty.strengthen, TyDenote, Refinement.interp]
        have hbase : BaseDen δ₀ k b' v ↔ BaseDen ⟨ρ ++ ρ₀, δ₀.fv, δ₀.denv⟩ k b' v := by
          cases b' with
          | tbvar j => simp [Base.tyOK] at hty'
          | _ => rfl
        have hown : Refinement.interp κ r' (γ₀.push v) ↔ Refinement.interp κ r' (γ.push v) := by
          apply Refinement.interp_congr r' (by simpa using hmap.symm)
          intro c i hi
          have := Refinement.wfB_hasBVar r' hr's c i hi
          cases i with
          | zero => rfl
          | succ i => simp at this
        rw [hbase, hown]
        constructor
        · rintro ⟨⟨hb, h₁⟩, h₂⟩
          refine ⟨hb, h₁, (hr' ?_).mpr h₂⟩
          intro hsort _ hB
          simp only [Ty.sortOf] at hsort ⊢
          rcases hsort with rfl | rfl
          · obtain ⟨n, rfl⟩ := hb; rfl
          · obtain ⟨c, rfl⟩ := hb; rfl
        · rintro ⟨hb, h₁, h₂⟩
          refine ⟨⟨hb, h₁⟩, (hr' ?_).mp h₂⟩
          intro hsort _ hB
          simp only [Ty.sortOf] at hsort ⊢
          rcases hsort with rfl | rfl
          · obtain ⟨n, rfl⟩ := hb; rfl
          · obtain ⟨c, rfl⟩ := hb; rfl
      | .arrow _ _, hs, hk, _ | .forall _ _, hs, hk, _ | .prod _ _, hs, hk, _
      | .data _ _ _, hs, hk, _ =>
        have hkd' : kd = .star := by rcases hk with h | h <;> simp_all [Ty.kindOf]
        subst hkd'
        have hstar' : (Base.tbvar ρ.length).isStarB kctx = true := by
          simp [Base.isStarB, hkd]
        simp only [hstar', Bool.not_true, Bool.false_or] at hstar
        simp only [Ty.strengthen, Refinement.interp_of_isTT hstar, and_true]
        exact TyDenote.congr_wf _ [] [] [] δ₀.bv (ρ ++ ρ₀) δ₀.fv δ₀.denv k γ₀ γ v hs rfl hmap.symm
          (fun i hi => by simp at hi)
    · simp only [Ty.instTy, hbk, if_false, TyDenote]
      rw [BaseDen.instAt_ne ρ ρ₀ δ₀.fv δ₀.denv R hbk hty hlen s.sortOf,
          hrefn r kctx ctx b ρ.length γ v hr hslots (fun _ h => absurd h hbk)]
  | arrow s₁ t₂ ihs iht =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap hslots
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    simp only [Ty.instTy, TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    refine forall_congr' (fun j => forall_congr' (fun hj => forall_congr' (fun va => ?_)))
    have hRj : ∀ k' ≤ j, ∀ w, R.rel k' w ↔ TyDenote κ δ₀ k' s γ₀ w :=
      fun k' hk' => hR k' (by omega)
    have hdom := ihs ρ ρ₀ kctx ctx j γ va hRj hw.1 hlen hkd hmap hslots
    -- the slot for the new binder holds an `s`-sorted value when it is `α`-sorted
    have hslot (hva : TyDenote κ ⟨ρ ++ R :: ρ₀, δ₀.fv, δ₀.denv⟩ j s₁ γ va) :
        (s.sortOf = .int ∨ s.sortOf = .bool) → SlotsOK kctx (s₁.optBase :: ctx) ρ.length s.sortOf
          (γ.push va) := by
      intro hb'
      refine (hslots hb').push _ va ?_
      intro hopt hB
      have hkdB : kd = .B := by rw [hkd] at hB; exact Option.some.inj hB
      cases s₁ with
      | refine b₁ r₁ =>
        simp only [Ty.optBase, Option.some.injEq] at hopt
        subst hopt
        simp only [TyDenote, BaseDen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some] at hva
        exact hRval hkdB hb' j va (hRj j (Nat.le_refl _) va) hva.1
      | arrow _ _ | «forall» _ _ | prod _ _ | data _ _ _ => simp [Ty.optBase] at hopt
    constructor
    · intro h hva'
      have hva := hdom.mpr hva'
      obtain ⟨body, o, hap, hev, hres⟩ := h hva
      refine ⟨body, o, hap, hev, fun vr m ho hm => ?_⟩
      exact (iht ρ ρ₀ kctx (s₁.optBase :: ctx) m (γ.push va) vr (fun k' hk' => hR k' (by omega))
        hw.2 hlen hkd (by simpa using hmap) (hslot hva)).mp (hres vr m ho hm)
    · intro h hva
      obtain ⟨body, o, hap, hev, hres⟩ := h (hdom.mp hva)
      refine ⟨body, o, hap, hev, fun vr m ho hm => ?_⟩
      exact (iht ρ ρ₀ kctx (s₁.optBase :: ctx) m (γ.push va) vr (fun k' hk' => hR k' (by omega))
        hw.2 hlen hkd (by simpa using hmap) (hslot hva)).mpr (hres vr m ho hm)
  | «forall» kd' t' ih =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap hslots
    simp only [Ty.wfB] at hw
    simp only [Ty.instTy, TyDenote]
    refine forall_congr' (fun R' => forall_congr' (fun _ => ?_))
    have := ih (R' :: ρ) ρ₀ (kd' :: kctx) (ctx.map (Option.map Base.shiftT)) k γ v hR hw
      (by simp [hlen]) (by simpa using hkd) hmap ?_
    · simpa [TyEnvSem.push] using this
    · intro hb' i hi hB
      unfold SlotsOK at hslots
      simp only [List.length_cons, List.getElem?_cons_succ] at hi hB
      simp only [List.getElem?_map] at hi
      cases hc : ctx[i]? with
      | none => simp [hc] at hi
      | some o =>
        rw [hc] at hi
        cases o with
        | none => simp at hi
        | some c =>
          simp only [Option.map_some, Option.some.injEq] at hi
          cases c with
          | tbvar j =>
            simp only [Base.shiftT, Base.tbvar.injEq] at hi
            have hj : j = ρ.length := by omega
            subst hj
            exact hslots hb' i hc hB
          | _ => simp [Base.shiftT] at hi
  | prod s₁ t₂ ihs iht =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap hslots
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    simp only [Ty.instTy, TyDenote]
    have hslot (va : Val) (hva : TyDenote κ ⟨ρ ++ R :: ρ₀, δ₀.fv, δ₀.denv⟩ k s₁ γ va) :
        (s.sortOf = .int ∨ s.sortOf = .bool) → SlotsOK kctx (s₁.optBase :: ctx) ρ.length s.sortOf
          (γ.push va) := by
      intro hb'
      refine (hslots hb').push _ va ?_
      intro hopt hB
      have hkdB : kd = .B := by rw [hkd] at hB; exact Option.some.inj hB
      cases s₁ with
      | refine b₁ r₁ =>
        simp only [Ty.optBase, Option.some.injEq] at hopt
        subst hopt
        simp only [TyDenote, BaseDen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some] at hva
        exact hRval hkdB hb' k va (hR k (Nat.le_refl _) va) hva.1
      | arrow _ _ | «forall» _ _ | prod _ _ | data _ _ _ => simp [Ty.optBase] at hopt
    refine exists_congr fun v₁ => exists_congr fun v₂ => and_congr_right fun _ => ?_
    have h₁ := ihs ρ ρ₀ kctx ctx k γ v₁ hR hw.1 hlen hkd hmap hslots
    constructor
    · rintro ⟨hv₁, hv₂⟩
      exact ⟨h₁.mp hv₁, (iht ρ ρ₀ kctx (s₁.optBase :: ctx) k (γ.push v₁) v₂ hR hw.2 hlen hkd
        (by simpa using hmap) (hslot v₁ hv₁)).mp hv₂⟩
    · rintro ⟨hv₁, hv₂⟩
      have hv₁' := h₁.mpr hv₁
      exact ⟨hv₁', (iht ρ ρ₀ kctx (s₁.optBase :: ctx) k (γ.push v₁) v₂ hR hw.2 hlen hkd
        (by simpa using hmap) (hslot v₁ hv₁')).mpr hv₂⟩
  | data C n args ih =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap hslots
    simp only [Ty.wfB, List.all_eq_true, List.mem_finRange, true_implies] at hw
    simp only [Ty.instTy]
    exact TyDenote.data_congr rfl (fun l j hj w =>
      ih l ρ ρ₀ kctx ctx j γ w (fun k' hk' => hR k' (by omega)) (hw l) hlen hkd hmap hslots)

end STLC
