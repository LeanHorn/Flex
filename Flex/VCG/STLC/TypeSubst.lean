import Flex.VCG.STLC.Substitution

/-! # Semantics of type-variable substitution

  Type variables are sorts of the refinement logic, so the type-level operations
  `Ty.openTv` (opening a type binder) and `Ty.instTy` (type application) retype
  the deep-embedded refinements. This file shows that both are *semantically*
  what they should be:

  * retyping a refinement along a sort substitution never changes its meaning,
    when the two sort assignments agree on the sorts it reads
    (`Refinement.interp_substB`);
  * opening a type binder with `a` is the same as interpreting the binder by
    `a`'s semantic type (`TyDenote.openTv_iff`);
  * rebinding a type variable that does not occur is invisible
    (`TyDenote.set_fresh_iff`).
-/

namespace STLC

/-! ## Reading a refinement under a sort substitution

  A term of sort `b` is read, under the sort assignment `γ.sorts`, at the base
  `b` resolves to. The single fact behind every type-variable lemma below:
  retyping a refinement along a sort substitution `θ` and reading it under
  another environment changes nothing, as long as the name maps agree, the
  stack slots the refinement reads agree, and each sort occurring in the
  refinement resolves (after `θ`) to the same base (`BSubst.Agrees`). Only the
  *leaves* and quantifier domains of a refinement are read at a sort; equality
  and comparison only look at the values read, so they need nothing more. -/

/-- The sorts at which a term reads its leaves. -/
def Term.sorts : {b : Base} → Term b → List Base
  | _, .const b _ => [b]
  | _, .bvar b _  => [b]
  | _, .fvar b _  => [b]
  | _, .add t₁ t₂ => Term.sorts t₁ ++ Term.sorts t₂
  | _, .mbvar _ _ => []
  | _, .mfvar _ _ => []
  | _, .ibvar _   => []
  | _, .bbvar _   => []
  | _, .not t     => Term.sorts t
  | _, .and t₁ t₂ => Term.sorts t₁ ++ Term.sorts t₂
  | _, .leqI t₁ t₂ => Term.sorts t₁ ++ Term.sorts t₂
  | _, .ite _ c t e => Term.sorts c ++ Term.sorts t ++ Term.sorts e

/-- The sorts a formula reads at (its terms' leaves and quantifier domains). -/
def Formula.sorts : Formula → List Base
  | .tt | .ff => []
  | .eq _ t₁ t₂ | .leq _ t₁ t₂ => t₁.sorts ++ t₂.sorts
  | .and φ₁ φ₂ | .or φ₁ φ₂ | .imp φ₁ φ₂ => φ₁.sorts ++ φ₂.sorts
  | .not φ => φ.sorts
  | .ex b φ | .all b φ => b :: φ.sorts

def Refinement.sorts : Refinement → List Base
  | .fmla φ => φ.sorts
  | .kapp _ args => args.flatMap (fun a => a.2.sorts)
  | .conj r₁ r₂ => r₁.sorts ++ r₂.sorts

/-- After retyping along `θ`, every sort in `S` is read under `σ'` at the base it
    was read at under `σ`. -/
def BSubst.Agrees (θ : BSubst) (σ σ' : SortEnv) (S : List Base) : Prop :=
  ∀ b ∈ S, (b.substB θ).resolve σ' = b.resolve σ

theorem BSubst.Agrees.left {θ : BSubst} {σ σ' : SortEnv} {S T : List Base}
    (h : θ.Agrees σ σ' (S ++ T)) : θ.Agrees σ σ' S := fun b hb => h b (List.mem_append_left _ hb)

theorem BSubst.Agrees.right {θ : BSubst} {σ σ' : SortEnv} {S T : List Base}
    (h : θ.Agrees σ σ' (S ++ T)) : θ.Agrees σ σ' T := fun b hb => h b (List.mem_append_right _ hb)

/-- A term's value, as a `Val` (independent of the base it is read at). -/
@[reducible] def Term.ival (γ : REnv) {b : Base} (t : Term b) : Val :=
  Val.inj (b.resolve γ.sorts) (Term.interp γ t)

theorem Val.inj_sort_eq {s s' : BSort} {x : s.ty} {x' : s'.ty}
    (h : Val.inj s' x' = Val.inj s x) : s' = s := by
  cases s <;> cases s' <;> simp_all

theorem BSort.le_congr {s s' : BSort} {x y : s.ty} {x' y' : s'.ty}
    (hx : Val.inj s' x' = Val.inj s x) (hy : Val.inj s' y' = Val.inj s y) :
    BSort.le s' x' y' ↔ BSort.le s x y := by
  cases s <;> cases s' <;> simp_all

theorem Val.tag_congr {s s' : BSort} {x : s.ty} {x' : s'.ty}
    (h : Val.inj s' x' = Val.inj s x) : Val.tag s' x' = Val.tag s x := by
  cases s <;> cases s' <;> simp_all

theorem BSort.exists_iff (s : BSort) (P : Val → Prop) :
    (∃ x : s.ty, P (Val.inj s x)) ↔ ∃ v, Val.HasSort s v ∧ P v := by
  cases s
  · exact ⟨fun ⟨x, h⟩ => ⟨_, ⟨x, rfl⟩, h⟩, fun ⟨_, ⟨x, hx⟩, h⟩ => ⟨x, by subst hx; exact h⟩⟩
  · exact ⟨fun ⟨x, h⟩ => ⟨_, ⟨x, rfl⟩, h⟩, fun ⟨_, ⟨x, hx⟩, h⟩ => ⟨x, by subst hx; exact h⟩⟩

theorem BSort.forall_iff (s : BSort) (P : Val → Prop) :
    (∀ x : s.ty, P (Val.inj s x)) ↔ ∀ v, Val.HasSort s v → P v := by
  cases s
  · exact ⟨fun h _ ⟨x, hx⟩ => by subst hx; exact h x, fun h x => h _ ⟨x, rfl⟩⟩
  · exact ⟨fun h _ ⟨x, hx⟩ => by subst hx; exact h x, fun h x => h _ ⟨x, rfl⟩⟩

theorem Term.ival_substB (θ : BSubst) {γ γ' : REnv} (hmap : γ'.map = γ.map)
    (hmeas : γ'.sorts.meas = γ.sorts.meas) :
    ∀ {b : Base} (t : Term b), (∀ c k, Term.hasBVar c k t → γ'.bv[k]? = γ.bv[k]?) →
      (∀ k, Term.hasMBVar k t → γ'.bv[k]? = γ.bv[k]?) →
      θ.Agrees γ.sorts γ'.sorts t.sorts → Term.ival γ' (t.substB θ) = Term.ival γ t := by
  intro b t
  induction t with
  | const b c =>
    intro _ _ _
    cases b with
    | int | bool => rfl
    | tbvar _ | tfvar _ => exact c.elim
  | bvar b k =>
    intro hbv _ hA
    have hs := hA b (by simp [Term.sorts])
    simp only [Term.ival, Term.substB, Term.interp, REnv.getBV, hbv b k ⟨rfl, rfl⟩]
    rw [hs]
  | fvar b x =>
    intro _ _ hA
    have hs := hA b (by simp [Term.sorts])
    simp only [Term.ival, Term.substB, Term.interp, REnv.get, REnv.lookup, hmap]
    rw [hs]
  | mbvar m k =>
    intro _ hmbv _
    simp [Term.ival, Term.substB, Term.interp, hmeas, hmbv k rfl, Base.substB]
  | mfvar m x =>
    intro _ _ _
    simp [Term.ival, Term.substB, Term.interp, hmeas, hmap, Base.substB]
  | ibvar k =>
    intro _ hmbv _
    simp [Term.ival, Term.substB, Term.interp, hmbv k rfl, Base.substB]
  | bbvar k =>
    intro _ hmbv _
    simp [Term.ival, Term.substB, Term.interp, hmbv k rfl, Base.substB]
  | add t₁ t₂ ih₁ ih₂ | and t₁ t₂ ih₁ ih₂ | leqI t₁ t₂ ih₁ ih₂ =>
    intro hbv hmbv hA
    have h₁ := ih₁ (fun c k hk => hbv c k (Or.inl hk)) (fun k hk => hmbv k (Or.inl hk)) hA.left
    have h₂ := ih₂ (fun c k hk => hbv c k (Or.inr hk)) (fun k hk => hmbv k (Or.inr hk)) hA.right
    simp only [Term.ival, Term.substB, Term.interp, Base.substB, Base.resolve, Val.inj,
      Val.iconst.injEq, Val.bconst.injEq] at h₁ h₂ ⊢
    rw [h₁, h₂]
  | ite b c t e ihc iht ihe =>
    intro hbv hmbv hA
    have hc := ihc (fun c' k hk => hbv c' k (Or.inl hk)) (fun k hk => hmbv k (Or.inl hk))
      hA.left.left
    have ht := iht (fun c' k hk => hbv c' k (Or.inr (Or.inl hk)))
      (fun k hk => hmbv k (Or.inr (Or.inl hk))) hA.left.right
    have he := ihe (fun c' k hk => hbv c' k (Or.inr (Or.inr hk)))
      (fun k hk => hmbv k (Or.inr (Or.inr hk))) hA.right
    simp only [Term.ival, Term.substB, Base.substB, Base.resolve, Val.inj, Val.bconst.injEq] at hc
    simp only [Term.ival, Term.substB, Term.interp] at ht he ⊢
    rw [hc]
    by_cases hcv : Term.interp γ c = true
    · simp only [hcv, if_true]; exact ht
    · simp only [hcv, if_false, Bool.false_eq_true]; exact he
  | not t ih =>
    intro hbv hmbv hA
    have h₁ := ih hbv hmbv hA
    simp only [Term.ival, Term.substB, Term.interp, Base.substB, Base.resolve, Val.inj,
      Val.bconst.injEq] at h₁ ⊢
    rw [h₁]

/-- **Master lemma** (formulas). -/
theorem Formula.interp_substB (θ : BSubst) (φ : Formula) :
    ∀ {γ γ' : REnv}, γ'.map = γ.map → γ'.sorts.meas = γ.sorts.meas →
      (∀ c k, Formula.hasBVar c k φ → γ'.bv[k]? = γ.bv[k]?) →
      (∀ k, Formula.hasMBVar k φ → γ'.bv[k]? = γ.bv[k]?) →
      θ.Agrees γ.sorts γ'.sorts φ.sorts →
      (Formula.interp γ' (φ.substB θ) ↔ Formula.interp γ φ) := by
  induction φ with
  | tt | ff => intros; rfl
  | eq b t₁ t₂ =>
    intro γ γ' hmap hmeas hbv hmbv hA
    have h₁ := Term.ival_substB θ hmap hmeas t₁ (fun c k hk => hbv c k (Or.inl hk))
      (fun k hk => hmbv k (Or.inl hk)) hA.left
    have h₂ := Term.ival_substB θ hmap hmeas t₂ (fun c k hk => hbv c k (Or.inr hk))
      (fun k hk => hmbv k (Or.inr hk)) hA.right
    simp only [Formula.substB, Formula.interp]
    rw [← Val.inj_injective, ← Val.inj_injective (b.resolve γ.sorts)]
    exact Iff.of_eq (by simp only [Term.ival] at h₁ h₂; rw [h₁, h₂])
  | leq b t₁ t₂ =>
    intro γ γ' hmap hmeas hbv hmbv hA
    have h₁ := Term.ival_substB θ hmap hmeas t₁ (fun c k hk => hbv c k (Or.inl hk))
      (fun k hk => hmbv k (Or.inl hk)) hA.left
    have h₂ := Term.ival_substB θ hmap hmeas t₂ (fun c k hk => hbv c k (Or.inr hk))
      (fun k hk => hmbv k (Or.inr hk)) hA.right
    simp only [Formula.substB, Formula.interp]
    exact BSort.le_congr h₁ h₂
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro γ γ' hmap hmeas hbv hmbv hA
    simp only [Formula.substB, Formula.interp,
      ih₁ hmap hmeas (fun c k hk => hbv c k (Or.inl hk)) (fun k hk => hmbv k (Or.inl hk)) hA.left,
      ih₂ hmap hmeas (fun c k hk => hbv c k (Or.inr hk)) (fun k hk => hmbv k (Or.inr hk)) hA.right]
  | not _ ih =>
    intro γ γ' hmap hmeas hbv hmbv hA
    simp only [Formula.substB, Formula.interp, ih hmap hmeas hbv hmbv hA]
  | ex b φ ih | all b φ ih =>
    intro γ γ' hmap hmeas hbv hmbv hA
    have hb := hA b List.mem_cons_self
    have hA' : θ.Agrees γ.sorts γ'.sorts φ.sorts := fun b' hb' => hA b' (List.mem_cons_of_mem _ hb')
    have key : ∀ w : Val, Formula.interp (γ'.push w) (φ.substB θ) ↔ Formula.interp (γ.push w) φ := by
      intro w
      refine ih (by simpa using hmap) hmeas (fun c k hk => ?_) (fun k hk => ?_) hA'
      · cases k with
        | zero => rfl
        | succ k => exact hbv c k hk
      · cases k with
        | zero => rfl
        | succ k => exact hmbv k hk
    simp only [Formula.substB, Formula.interp]
    first
      | (rw [BSort.exists_iff _ (fun w => Formula.interp (γ'.push w) (φ.substB θ)),
            BSort.exists_iff _ (fun w => Formula.interp (γ.push w) φ), hb]
         exact exists_congr fun w => and_congr_right fun _ => key w)
      | (rw [BSort.forall_iff _ (fun w => Formula.interp (γ'.push w) (φ.substB θ)),
            BSort.forall_iff _ (fun w => Formula.interp (γ.push w) φ), hb]
         exact forall_congr' fun w => imp_congr_right fun _ => key w)

/-- **Master lemma** (refinements). -/
theorem Refinement.interp_substB {κ : KEnv} (θ : BSubst) (r : Refinement) :
    ∀ {γ γ' : REnv}, γ'.map = γ.map → γ'.sorts.meas = γ.sorts.meas →
      (∀ c k, Refinement.hasBVar c k r → γ'.bv[k]? = γ.bv[k]?) →
      (∀ k, Refinement.hasMBVar k r → γ'.bv[k]? = γ.bv[k]?) →
      θ.Agrees γ.sorts γ'.sorts r.sorts →
      (Refinement.interp κ (r.substB θ) γ' ↔ Refinement.interp κ r γ) := by
  induction r with
  | fmla φ =>
    intro γ γ' hmap hmeas hbv hmbv hA; exact Formula.interp_substB θ φ hmap hmeas hbv hmbv hA
  | kapp kn args =>
    intro γ γ' hmap hmeas hbv hmbv hA
    simp only [Refinement.substB, Refinement.interp, List.map_map]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a ha
    have h := Term.ival_substB θ hmap hmeas a.2 (fun c k hk => hbv c k ⟨a, ha, hk⟩)
      (fun k hk => hmbv k ⟨a, ha, hk⟩)
      (fun b hb => hA b (List.mem_flatMap.mpr ⟨a, ha, hb⟩))
    exact Val.tag_congr h
  | conj _ _ ih₁ ih₂ =>
    intro γ γ' hmap hmeas hbv hmbv hA
    simp only [Refinement.substB, Refinement.interp,
      ih₁ hmap hmeas (fun c k hk => hbv c k (Or.inl hk)) (fun k hk => hmbv k (Or.inl hk)) hA.left,
      ih₂ hmap hmeas (fun c k hk => hbv c k (Or.inr hk)) (fun k hk => hmbv k (Or.inr hk)) hA.right]

/-! ### The identity substitution: congruence -/

def BSubst.id : BSubst := ⟨.tbvar, .tfvar⟩

@[simp] theorem Base.substB_id (b : Base) : b.substB BSubst.id = b := by
  cases b <;> rfl

theorem Term.substB_id : ∀ {b : Base} (t : Term b),
    (⟨b.substB BSubst.id, t.substB BSubst.id⟩ : Σ b, Term b) = ⟨b, t⟩ := by
  intro b t
  induction t with
  | const b c => cases b <;> first | rfl | exact c.elim
  | bvar b k => cases b <;> rfl
  | fvar b x => cases b <;> rfl
  | mbvar _ _ | mfvar _ _ | ibvar _ | bbvar _ => rfl
  | add t₁ t₂ ih₁ ih₂ | and t₁ t₂ ih₁ ih₂ | leqI t₁ t₂ ih₁ ih₂ =>
    simp only [Base.substB, Sigma.mk.injEq, heq_eq_eq, true_and] at ih₁ ih₂
    simp only [Term.substB, Base.substB, ih₁, ih₂]
  | ite b c t e ihc iht ihe =>
    simp only [Base.substB, Sigma.mk.injEq, heq_eq_eq, true_and] at ihc
    simp only [Term.substB, ihc]
    generalize t.substB BSubst.id = u₁ at iht
    generalize e.substB BSubst.id = u₂ at ihe
    revert u₁ u₂
    rw [Base.substB_id]
    intro u₁ h₁ u₂ h₂
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h₁ h₂
    rw [h₁, h₂]
  | not t ih =>
    simp only [Base.substB, Sigma.mk.injEq, heq_eq_eq, true_and] at ih
    simp only [Term.substB, Base.substB, ih]

theorem Formula.substB_id (φ : Formula) : φ.substB BSubst.id = φ := by
  induction φ with
  | tt | ff => rfl
  | eq b t₁ t₂ | leq b t₁ t₂ =>
    have h₁ := Term.substB_id t₁
    have h₂ := Term.substB_id t₂
    simp only [Formula.substB]
    generalize t₁.substB BSubst.id = u₁ at h₁
    generalize t₂.substB BSubst.id = u₂ at h₂
    revert u₁ u₂
    rw [Base.substB_id]
    intro u₁ h₁ u₂ h₂
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h₁ h₂
    rw [h₁, h₂]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ => simp only [Formula.substB, ih₁, ih₂]
  | not _ ih => simp only [Formula.substB, ih]
  | ex b _ ih | all b _ ih => simp only [Formula.substB, ih, Base.substB_id]

theorem Refinement.substB_id (r : Refinement) : r.substB BSubst.id = r := by
  induction r with
  | fmla φ => simp only [Refinement.substB, Formula.substB_id]
  | kapp kn args =>
    simp only [Refinement.substB]
    congr 1
    conv => rhs; rw [← List.map_id args]
    apply List.map_congr_left
    intro a _
    exact Term.substB_id a.2
  | conj _ _ ih₁ ih₂ => simp only [Refinement.substB, ih₁, ih₂]

/-- A refinement reads only the slots and sorts it mentions. -/
theorem Formula.interp_congr (φ : Formula) {γ γ' : REnv} (hmap : γ.map = γ'.map)
    (hmeas : γ.sorts.meas = γ'.sorts.meas)
    (h : ∀ c k, Formula.hasBVar c k φ → γ.bv[k]? = γ'.bv[k]?)
    (hm : ∀ k, Formula.hasMBVar k φ → γ.bv[k]? = γ'.bv[k]?)
    (hs : ∀ b ∈ φ.sorts, b.resolve γ.sorts = b.resolve γ'.sorts) :
    Formula.interp γ φ ↔ Formula.interp γ' φ := by
  have := Formula.interp_substB BSubst.id φ (γ := γ') (γ' := γ) hmap hmeas
    (fun c k hk => h c k hk) hm (fun b hb => by rw [Base.substB_id]; exact hs b hb)
  rwa [Formula.substB_id] at this

theorem Refinement.interp_congr {κ : KEnv} (r : Refinement) {γ γ' : REnv} (hmap : γ.map = γ'.map)
    (hmeas : γ.sorts.meas = γ'.sorts.meas)
    (h : ∀ c k, Refinement.hasBVar c k r → γ.bv[k]? = γ'.bv[k]?)
    (hm : ∀ k, Refinement.hasMBVar k r → γ.bv[k]? = γ'.bv[k]?)
    (hs : ∀ b ∈ r.sorts, b.resolve γ.sorts = b.resolve γ'.sorts) :
    Refinement.interp κ r γ ↔ Refinement.interp κ r γ' := by
  have := Refinement.interp_substB (κ := κ) BSubst.id r (γ := γ') (γ' := γ) hmap hmeas
    (fun c k hk => h c k hk) hm (fun b hb => by rw [Base.substB_id]; exact hs b hb)
  rwa [Refinement.substB_id] at this

/-! ### Which sorts can occur -/

theorem Term.ftv_of_mem_sorts {a : TVar} : ∀ {b : Base} (t : Term b), .tfvar a ∈ t.sorts → a ∈ t.ftv := by
  intro b t
  induction t with
  | const b _ | bvar b _ | fvar b _ =>
    intro h; simp only [Term.sorts, List.mem_singleton] at h; subst h; simp [Term.ftv, Base.ftv]
  | mbvar _ _ | mfvar _ _ | ibvar _ | bbvar _ => intro h; simp [Term.sorts] at h
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | leqI _ _ ih₁ ih₂ =>
    intro h; simp only [Term.sorts, List.mem_append] at h
    simp only [Term.ftv, List.mem_append]; exact h.imp ih₁ ih₂
  | ite _ c t e ihc iht ihe =>
    intro h; simp only [Term.sorts, List.mem_append] at h
    simp only [Term.ftv, List.mem_append]
    rcases h with (h | h) | h
    · exact Or.inl (Or.inl (ihc h))
    · exact Or.inl (Or.inr (iht h))
    · exact Or.inr (ihe h)
  | not _ ih => intro h; exact ih h

theorem Formula.ftv_of_mem_sorts {a : TVar} (φ : Formula) : .tfvar a ∈ φ.sorts → a ∈ φ.ftv := by
  induction φ with
  | tt | ff => simp [Formula.sorts]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro h; simp only [Formula.sorts, List.mem_append] at h
    simp only [Formula.ftv, List.mem_append]
    rcases h with h | h
    · exact Or.inl (Or.inr (Term.ftv_of_mem_sorts t₁ h))
    · exact Or.inr (Term.ftv_of_mem_sorts t₂ h)
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro h; simp only [Formula.sorts, List.mem_append] at h
    simp only [Formula.ftv, List.mem_append]; exact h.imp ih₁ ih₂
  | not _ ih => intro h; exact ih h
  | ex b _ ih | all b _ ih =>
    intro h; simp only [Formula.sorts, List.mem_cons] at h
    simp only [Formula.ftv, List.mem_append]
    rcases h with rfl | h
    · exact Or.inl (by simp [Base.ftv])
    · exact Or.inr (ih h)

theorem Refinement.ftv_of_mem_sorts {a : TVar} (r : Refinement) : .tfvar a ∈ r.sorts → a ∈ r.ftv := by
  induction r with
  | fmla φ => exact Formula.ftv_of_mem_sorts φ
  | kapp kn args =>
    intro h
    simp only [Refinement.sorts, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    simp only [Refinement.ftv, List.mem_flatMap, List.mem_append]
    exact ⟨x, hx, Or.inr (Term.ftv_of_mem_sorts x.2 h)⟩
  | conj _ _ ih₁ ih₂ =>
    intro h; simp only [Refinement.sorts, List.mem_append] at h
    simp only [Refinement.ftv, List.mem_append]; exact h.imp ih₁ ih₂

theorem Term.sortOK_of_mem_sorts {kctx : List Kind} {ctx : List (Option Base)} :
    ∀ {b' : Base} (t : Term b'), t.wfB kctx ctx = true → ∀ b ∈ t.sorts, b.sortOK kctx = true := by
  intro b' t
  induction t with
  | const b _ =>
    intro hw c hc; simp only [Term.sorts, List.mem_singleton] at hc; subst hc
    cases c <;> simp_all [Term.wfB, Base.isTv, Base.sortOK]
  | mbvar _ _ | mfvar _ _ | ibvar _ | bbvar _ => intro _ c hc; simp [Term.sorts] at hc
  | bvar b _ =>
    intro hw c hc; simp only [Term.sorts, List.mem_singleton] at hc; subst hc
    simp only [Term.wfB, Bool.and_eq_true] at hw; exact hw.2
  | fvar b _ =>
    intro hw c hc; simp only [Term.sorts, List.mem_singleton] at hc; subst hc
    cases c with
    | tfvar a => obtain ⟨_, k⟩ := a; simpa [Term.wfB, Base.fvOK, Base.sortOK] using hw
    | _ => simp_all [Term.wfB, Base.fvOK, Base.sortOK]
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | leqI _ _ ih₁ ih₂ =>
    intro hw c hc
    simp only [Term.wfB, Bool.and_eq_true] at hw
    simp only [Term.sorts, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ih₁ hw.1 c hc
    · exact ih₂ hw.2 c hc
  | ite _ c t e ihc iht ihe =>
    intro hw c' hc
    simp only [Term.wfB, Bool.and_eq_true] at hw
    simp only [Term.sorts, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · exact ihc hw.1.1 c' hc
    · exact iht hw.1.2 c' hc
    · exact ihe hw.2 c' hc
  | not _ ih => intro hw c hc; exact ih hw c hc

theorem Formula.sortOK_of_mem_sorts (φ : Formula) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    φ.wfB kctx ctx = true → ∀ b ∈ φ.sorts, b.sortOK kctx = true := by
  induction φ with
  | tt | ff => simp [Formula.sorts]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro kctx ctx hw c hc
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.sorts, List.mem_append] at hc
    rcases hc with hc | hc
    · exact Term.sortOK_of_mem_sorts t₁ hw.1 c hc
    · exact Term.sortOK_of_mem_sorts t₂ hw.2 c hc
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro kctx ctx hw c hc
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.sorts, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ih₁ hw.1 c hc
    · exact ih₂ hw.2 c hc
  | not _ ih => intro kctx ctx hw c hc; exact ih hw c hc
  | ex b _ ih | all b _ ih =>
    intro kctx ctx hw c hc
    simp only [Formula.wfB, Bool.and_eq_true, Bool.not_eq_true'] at hw
    simp only [Formula.sorts, List.mem_cons] at hc
    rcases hc with rfl | hc
    · cases c <;> simp_all [Base.isTv, Base.sortOK]
    · exact ih hw.2 c hc

theorem Refinement.sortOK_of_mem_sorts (r : Refinement) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    r.wfB kctx ctx = true → ∀ b ∈ r.sorts, b.sortOK kctx = true := by
  induction r with
  | fmla φ => intro kctx ctx hw; exact Formula.sortOK_of_mem_sorts φ hw
  | kapp kn args =>
    intro kctx ctx hw c hc
    simp only [Refinement.wfB, List.all_eq_true] at hw
    simp only [Refinement.sorts, List.mem_flatMap] at hc
    obtain ⟨x, hx, hc⟩ := hc
    have hx' := hw x hx
    simp only [Bool.and_eq_true] at hx'
    exact Term.sortOK_of_mem_sorts x.2 hx'.2 c hc
  | conj _ _ ih₁ ih₂ =>
    intro kctx ctx hw c hc
    simp only [Refinement.wfB, Bool.and_eq_true] at hw
    simp only [Refinement.sorts, List.mem_append] at hc
    rcases hc with hc | hc
    · exact ih₁ hw.1 c hc
    · exact ih₂ hw.2 c hc

/-! ## Congruence for datatype denotations -/

theorem SemTy.upto_congr {i : Nat} {R R' : Fin (i+1) → Val → Prop} {srt : BSort}
    (h : ∀ j w, R j w ↔ R' j w) : SemTy.upto i R srt = SemTy.upto i R' srt := by
  have : R = R' := funext fun j => funext fun w => propext (h j w)
  subst this; rfl

/-- A datatype's denotation at index `k` depends on its type arguments only
    through their denotations below `k`. -/
theorem TyDenote.data_congr {κ : KEnv} {δ δ' : TyEnvSem} {k : Nat} {C : String} {n : Nat}
    {args args' : Fin n → Ty} {r r' : Refinement} {γ γ' : REnv} {v : Val}
    (hden : δ.denv = δ'.denv)
    (hargs : ∀ l, ∀ j < k, ∀ w, TyDenote κ δ j (args l) γ w ↔ TyDenote κ δ' j (args' l) γ' w)
    (hsort : ∀ l, (args l).semSort δ = (args' l).semSort δ')
    (hr : ∀ v, Refinement.interp κ r ((γ.withSorts δ.sorts).push v) ↔
      Refinement.interp κ r' ((γ'.withSorts δ'.sorts).push v)) :
    TyDenote κ δ k (.data C n args r) γ v ↔ TyDenote κ δ' k (.data C n args' r') γ' v := by
  simp only [TyDenote, hden]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr (hr v) <| exists_congr fun j => exists_congr fun w => exists_congr fun P => and_congr_right fun _ =>
      and_congr_right fun _ => forall_congr' fun i => forall_congr' fun hi => ?_
  have : (List.ofFn fun l => SemTy.upto i (fun j' w' => TyDenote κ δ j'.val (args l) γ w')
        ((args l).semSort δ)) =
      List.ofFn fun l => SemTy.upto i (fun j' w' => TyDenote κ δ' j'.val (args' l) γ' w')
        ((args' l).semSort δ') := by
    congr 1; funext l
    rw [hsort l]
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

/-! ### Which semantic type a sort stands for

  Every type-variable-level operation (rebinding, opening, closing,
  instantiating) maps sorts to sorts, and preserves *which semantic type* each
  sort stands for (`TyEnvSem.lookupB`). That gives both the base denotation and
  the base a refinement is read at (`Base.resolve_of_lookupB`). -/

/-- The semantic type a type-variable sort stands for under `δ`. -/
def TyEnvSem.lookupB (δ : TyEnvSem) : Base → SemTy
  | .tbvar j => δ.bv[j]?.getD SemTy.top
  | .tfvar a => δ.fv a
  | _        => SemTy.top

theorem TyEnvSem.resolve_eq (δ : TyEnvSem) {b : Base} (hb : b.isTv = true) :
    b.resolve δ.sorts = (δ.lookupB b).sort := by
  cases b with
  | int | bool => simp [Base.isTv] at hb
  | tfvar a => rfl
  | tbvar j =>
    simp only [Base.resolve, TyEnvSem.sorts, TyEnvSem.lookupB, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    cases δ.bv[j]? <;> rfl

/-- A sort operation that keeps type-variable sorts type-variable sorts and
    preserves what they stand for preserves the base they are read at. -/
theorem Base.resolve_of_lookupB {θ : BSubst} {δ δ' : TyEnvSem} {b : Base}
    (hθ : b.isTv = true → (b.substB θ).isTv = true)
    (h : b.isTv = true → δ'.lookupB (b.substB θ) = δ.lookupB b) :
    (b.substB θ).resolve δ'.sorts = b.resolve δ.sorts := by
  cases b with
  | int | bool => rfl
  | tbvar _ | tfvar _ =>
    rw [TyEnvSem.resolve_eq δ' (hθ rfl), TyEnvSem.resolve_eq δ rfl, h rfl]

theorem Ty.semSort_eq (δ : TyEnvSem) (t : Ty) : t.semSort δ = t.sortOf.resolve δ.sorts := by
  cases t <;> rfl

theorem TyEnvSem.lookupB_set_ne {δ : TyEnvSem} {a : TVar} {R : SemTy} {b : Base}
    (hb : b ≠ .tfvar a) : (δ.set a R).lookupB b = δ.lookupB b := by
  cases b with
  | tfvar a' =>
    have : a' ≠ a := fun h => hb (by rw [h])
    simp [TyEnvSem.lookupB, TyEnvSem.set, this]
  | _ => rfl

theorem TyEnvSem.lookupB_openAt (ρ ρ₀ : List SemTy) (η : TVar → SemTy) (D : DEnv) (a : TVar)
    (R : SemTy) {b : Base} (hb : b ≠ .tfvar a) :
    ((⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).set a R).lookupB (b.substB (BSubst.openAt ρ.length a)) =
      (⟨ρ ++ R :: ρ₀, η, D⟩ : TyEnvSem).lookupB b := by
  cases b with
  | int | bool => rfl
  | tfvar a' =>
    have : a' ≠ a := fun h => hb (by rw [h])
    simp [TyEnvSem.lookupB, Base.substB, BSubst.openAt, BSubst.instAt, TyEnvSem.set, this]
  | tbvar j =>
    simp only [Base.substB, BSubst.openAt, BSubst.instAt]
    by_cases h₁ : j = ρ.length
    · subst h₁; simp [TyEnvSem.lookupB, TyEnvSem.set]
    · by_cases h₂ : ρ.length < j
      · simp only [h₁, h₂, if_false, if_true, TyEnvSem.lookupB]
        have e₁ : (ρ ++ R :: ρ₀)[j]? = ρ₀[j - ρ.length - 1]? := by
          rw [List.getElem?_append_right (by omega)]
          rw [show j - ρ.length = (j - ρ.length - 1) + 1 by omega]
          simp
        have e₂ : (ρ ++ ρ₀)[j - 1]? = ρ₀[j - ρ.length - 1]? := by
          rw [List.getElem?_append_right (by omega)]
          congr 1; omega
        simp [TyEnvSem.set, e₁, e₂]
      · simp only [h₁, h₂, if_false, TyEnvSem.lookupB]
        have hj : j < ρ.length := by omega
        simp [TyEnvSem.set, List.getElem?_append_left hj]

theorem TyEnvSem.lookupB_closeAt (ρ ρ₀ : List SemTy) (η : TVar → SemTy) (D : DEnv) (a : TVar)
    (R : SemTy) (b : Base) :
    (⟨ρ ++ R :: ρ₀, η, D⟩ : TyEnvSem).lookupB (b.substB (BSubst.closeAt ρ.length a)) =
      ((⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).set a R).lookupB b := by
  cases b with
  | int | bool => rfl
  | tfvar a' =>
    simp only [Base.substB, BSubst.closeAt]
    by_cases h : a' = a
    · subst h; simp [TyEnvSem.lookupB, TyEnvSem.set]
    · simp [TyEnvSem.lookupB, TyEnvSem.set, h]
  | tbvar j =>
    simp only [Base.substB, BSubst.closeAt]
    by_cases h : ρ.length ≤ j
    · simp only [h, if_true, TyEnvSem.lookupB]
      have e₁ : (ρ ++ R :: ρ₀)[j + 1]? = ρ₀[j - ρ.length]? := by
        rw [List.getElem?_append_right (by omega)]
        rw [show j + 1 - ρ.length = (j - ρ.length) + 1 by omega]
        simp
      have e₂ : (ρ ++ ρ₀)[j]? = ρ₀[j - ρ.length]? := List.getElem?_append_right h
      simp [TyEnvSem.set, e₁, e₂]
    · simp only [h, if_false, TyEnvSem.lookupB]
      have hj : j < ρ.length := by omega
      simp [TyEnvSem.set, List.getElem?_append_left hj]

theorem BSubst.openAt_isTv {k : Nat} {a : TVar} {b : Base} (hb : b.isTv = true) :
    (b.substB (BSubst.openAt k a)).isTv = true := by
  cases b with
  | tbvar j =>
    simp only [Base.substB, BSubst.openAt, BSubst.instAt]
    split
    · rfl
    · split <;> rfl
  | tfvar _ => rfl
  | int | bool => simp [Base.isTv] at hb

theorem BSubst.closeAt_isTv {k : Nat} {a : TVar} {b : Base} (hb : b.isTv = true) :
    (b.substB (BSubst.closeAt k a)).isTv = true := by
  cases b with
  | tbvar j => simp only [Base.substB, BSubst.closeAt]; split <;> rfl
  | tfvar a' => simp only [Base.substB, BSubst.closeAt]; split <;> rfl
  | int | bool => simp [Base.isTv] at hb

theorem Ty.sortOf_openTv (k : Nat) (a : TVar) (t : Ty) :
    (t.openTv k a).sortOf = t.sortOf.substB (BSubst.openAt k a) := by
  cases t <;> rfl

theorem Ty.sortOf_closeTv (k : Nat) (a : TVar) (t : Ty) :
    (t.closeTv k a).sortOf = t.sortOf.substB (BSubst.closeAt k a) := by
  cases t <;> rfl

theorem Ty.ftv_sortOf {a : TVar} {t : Ty} (ha : a ∉ t.ftv) : t.sortOf ≠ .tfvar a := by
  cases t with
  | refine b r => intro h; simp only [Ty.sortOf] at h; subst h; simp [Ty.ftv, Base.ftv] at ha
  | _ => simp [Ty.sortOf]

/-- Reading a sort is unchanged when what it stands for is unchanged. -/
theorem Base.resolve_congr {δ δ' : TyEnvSem} {b : Base}
    (h : b.isTv = true → δ'.lookupB b = δ.lookupB b) : b.resolve δ'.sorts = b.resolve δ.sorts := by
  have := Base.resolve_of_lookupB (θ := BSubst.id) (δ := δ) (δ' := δ') (b := b)
    (by simp) (by simpa using h)
  simpa using this

theorem Refinement.ne_of_fresh {a : TVar} {r : Refinement} (ha : a ∉ r.ftv) :
    ∀ b ∈ r.sorts, b ≠ .tfvar a :=
  fun _ hb h => ha (Refinement.ftv_of_mem_sorts r (h ▸ hb))

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
    refine and_congr_right fun _ => Refinement.interp_congr r rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) ?_
    intro c hc
    exact Base.resolve_congr (fun _ => TyEnvSem.lookupB_set_ne (Refinement.ne_of_fresh ha.2 c hc))
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
  | data C n args r ih =>
    intro δ k γ v
    simp only [Ty.ftv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, not_or,
      not_exists] at ha
    refine TyDenote.data_congr rfl (fun l j _ w => ih l (ha.1 l) δ j γ w) (fun l => ?_)
      (fun v => Refinement.interp_congr r rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) fun c hc =>
        Base.resolve_congr (fun _ => TyEnvSem.lookupB_set_ne (Refinement.ne_of_fresh ha.2 c hc)))
    rw [Ty.semSort_eq, Ty.semSort_eq]
    exact Base.resolve_congr (fun _ => TyEnvSem.lookupB_set_ne (Ty.ftv_sortOf (ha.1 l)))

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
    rw [BaseDen.openAt ρ ρ₀ η D a R ha.1]
    refine and_congr_right fun _ => Iff.symm ?_
    refine Refinement.interp_substB _ r rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) (fun c hc => ?_)
    exact Base.resolve_of_lookupB (fun h => BSubst.openAt_isTv h)
      (fun _ => TyEnvSem.lookupB_openAt ρ ρ₀ η D a R (Refinement.ne_of_fresh ha.2 c hc))
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
  | data C n args r ih =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.ftv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and, not_or,
      not_exists] at ha
    simp only [Ty.openTv]
    refine TyDenote.data_congr rfl (fun l j _ w => ih l (ha.1 l) ρ ρ₀ η D j γ w) (fun l => ?_)
      (fun v => Iff.symm (Refinement.interp_substB _ r rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) fun c hc =>
        Base.resolve_of_lookupB (fun h => BSubst.openAt_isTv h)
          (fun _ => TyEnvSem.lookupB_openAt ρ ρ₀ η D a R (Refinement.ne_of_fresh ha.2 c hc))))
    rw [Ty.semSort_eq, Ty.semSort_eq, Ty.sortOf_openTv]
    exact (Base.resolve_of_lookupB (fun h => BSubst.openAt_isTv h)
      (fun _ => TyEnvSem.lookupB_openAt ρ ρ₀ η D a R (Ty.ftv_sortOf (ha.1 l)))).symm

/-- The `∀`-instance of `openTv_iff`: entering a type binder by `R` is opening it
    with a fresh `a` interpreted by `R`. -/
theorem TyDenote.push_openTv_iff {κ : KEnv} (δ : TyEnvSem) (a : TVar) (R : SemTy) (t : Ty)
    (ha : a ∉ t.ftv) (k : Nat) (γ : REnv) (v : Val) :
    TyDenote κ (δ.push R) k t γ v ↔ TyDenote κ (δ.set a R) k (t.openTv 0 a) γ v := by
  have := TyDenote.openTv_iff (κ := κ) a R t ha [] δ.bv δ.fv δ.denv k γ v
  simpa [TyEnvSem.push] using this

/-! ## Closing a type variable (generalization) -/

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
    rw [BaseDen.closeAt ρ ρ₀ η D a R]
    refine and_congr_right fun _ =>
      Refinement.interp_substB _ r rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) (fun c _ => ?_)
    exact Base.resolve_of_lookupB (fun h => BSubst.closeAt_isTv h)
      (fun _ => TyEnvSem.lookupB_closeAt ρ ρ₀ η D a R c)
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
  | data C n args r ih =>
    intro ρ ρ₀ η D k γ v
    simp only [Ty.closeTv]
    refine TyDenote.data_congr rfl (fun l j _ w => ih l ρ ρ₀ η D j γ w) (fun l => ?_)
      (fun v => Refinement.interp_substB _ r rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) fun c _ =>
        Base.resolve_of_lookupB (fun h => BSubst.closeAt_isTv h)
          (fun _ => TyEnvSem.lookupB_closeAt ρ ρ₀ η D a R c))
    rw [Ty.semSort_eq, Ty.semSort_eq, Ty.sortOf_closeTv]
    exact Base.resolve_of_lookupB (fun h => BSubst.closeAt_isTv h)
      (fun _ => TyEnvSem.lookupB_closeAt ρ ρ₀ η D a R _)

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

/-! ## Congruence: a type reads only the slots and type variables in scope -/

/-- Sorts in scope are read alike when the stacks agree on the scope. -/
theorem Base.resolve_append {ρ₁ ρ ρ' : List SemTy} {η : TVar → SemTy} {D D' : DEnv}
    {kctx : List Kind} (hlen : kctx.length = ρ₁.length) {c : Base}
    (hc : c.sortOK kctx = true ∨ c.tyOK kctx = true) :
    c.resolve (⟨ρ₁ ++ ρ, η, D⟩ : TyEnvSem).sorts = c.resolve (⟨ρ₁ ++ ρ', η, D'⟩ : TyEnvSem).sorts := by
  cases c with
  | tbvar j =>
    have hj : j < ρ₁.length := by
      rw [← hlen]
      rcases hc with h | h
      · simp only [Base.sortOK, beq_iff_eq] at h; exact (List.getElem?_eq_some_iff.mp h).1
      · simpa [Base.tyOK] using h
    simp only [Base.resolve, TyEnvSem.sorts, List.getD_eq_getElem?_getD, List.map_append]
    rw [List.getElem?_append_left (by simpa using hj), List.getElem?_append_left (by simpa using hj)]
  | _ => rfl

theorem Ty.sortOf_tyOK {kctx : List Kind} {ctx : List (Option Base)} {t : Ty}
    (h : t.wfB kctx ctx = true) : t.sortOf.tyOK kctx = true := by
  cases t with
  | refine b r => simp only [Ty.wfB, Bool.and_eq_true] at h; exact h.1.1
  | _ => rfl

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
    · refine Refinement.interp_congr r (by simpa using hmap) rfl ?_ ?_ ?_
      · intro c i hi
        have := Refinement.wfB_hasBVar r hr c i hi
        cases i with
        | zero => rfl
        | succ i =>
          rcases Nat.lt_or_ge i ctx.length with hi' | hi'
          · exact hbv i hi'
          · rw [List.getElem?_cons_succ, List.getElem?_eq_none_iff.mpr hi'] at this
            cases this
      · intro i hi
        have := Refinement.wfB_hasMBVar r hr i hi
        cases i with
        | zero => rfl
        | succ i => exact hbv i (by simpa using this)
      · intro c hc
        exact Base.resolve_append hlen (Or.inl (Refinement.sortOK_of_mem_sorts r hr c hc))
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
  | data C n args r ih =>
    intro kctx ctx ρ₁ ρ ρ' η D k γ γ' v hw hlen hmap hbv
    simp only [Ty.wfB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hw
    refine TyDenote.data_congr rfl
      (fun l j _ w => ih l kctx ctx ρ₁ ρ ρ' η D j γ γ' w (hw.2 l) hlen hmap hbv) (fun l => ?_)
      (fun v => ?_)
    · rw [Ty.semSort_eq, Ty.semSort_eq]
      exact Base.resolve_append hlen (Or.inr (Ty.sortOf_tyOK (hw.2 l)))
    · refine Refinement.interp_congr r (by simpa using hmap) rfl ?_ ?_ ?_
      · intro c i hi
        have := Refinement.wfB_hasBVar r hw.1 c i hi
        cases i with
        | zero => rfl
        | succ i =>
          rcases Nat.lt_or_ge i ctx.length with hi' | hi'
          · exact hbv i hi'
          · rw [List.getElem?_cons_succ, List.getElem?_eq_none_iff.mpr hi'] at this
            cases this
      · intro i hi
        have := Refinement.wfB_hasMBVar r hw.1 i hi
        cases i with
        | zero => rfl
        | succ i => exact hbv i (by simpa using this)
      · intro c hc
        exact Base.resolve_append hlen (Or.inl (Refinement.sortOK_of_mem_sorts r hw.1 c hc))

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

/-- What a sort other than the instantiated level stands for is unchanged by
    instantiation. -/
theorem TyEnvSem.lookupB_instAt_ne (ρ ρ₀ : List SemTy) (η : TVar → SemTy) (D : DEnv) (R : SemTy)
    (b' : Base) {j : Nat} (hj : j ≠ ρ.length) :
    (⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).lookupB ((Base.tbvar j).substB (BSubst.instAt ρ.length b')) =
      (⟨ρ ++ R :: ρ₀, η, D⟩ : TyEnvSem).lookupB (.tbvar j) := by
  simp only [Base.substB, BSubst.instAt, hj, if_false]
  by_cases h₂ : ρ.length < j
  · simp only [h₂, if_true, TyEnvSem.lookupB]
    have e₁ : (ρ ++ R :: ρ₀)[j]? = ρ₀[j - ρ.length - 1]? := by
      rw [List.getElem?_append_right (by omega)]
      rw [show j - ρ.length = (j - ρ.length - 1) + 1 by omega]
      simp
    have e₂ : (ρ ++ ρ₀)[j - 1]? = ρ₀[j - ρ.length - 1]? := by
      rw [List.getElem?_append_right (by omega)]
      congr 1; omega
    simp [e₁, e₂]
  · simp only [h₂, if_false, TyEnvSem.lookupB]
    have hj' : j < ρ.length := by omega
    simp [List.getElem?_append_left hj']

/-- Instantiating level `ρ.length` at the closed sort `b'` reads every sort at the
    same base, provided the level's interpretation `R` is read at `b'`'s base. -/
theorem Base.resolve_instAt {ρ ρ₀ : List SemTy} {η : TVar → SemTy} {D : DEnv} {R : SemTy}
    {b' : Base} (hb' : ∀ j, b' ≠ .tbvar j)
    (hRs : R.sort = b'.resolve (⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).sorts) (c : Base) :
    (c.substB (BSubst.instAt ρ.length b')).resolve (⟨ρ ++ ρ₀, η, D⟩ : TyEnvSem).sorts =
      c.resolve (⟨ρ ++ R :: ρ₀, η, D⟩ : TyEnvSem).sorts := by
  cases c with
  | int | bool => rfl
  | tfvar a => rfl
  | tbvar j =>
    by_cases hj : j = ρ.length
    · subst hj
      simp only [Base.substB, BSubst.instAt, if_true]
      rw [← hRs, TyEnvSem.resolve_eq _ rfl]
      simp [TyEnvSem.lookupB]
    · have htv : ((Base.tbvar j).substB (BSubst.instAt ρ.length b')).isTv = true := by
        simp only [Base.substB, BSubst.instAt, hj, if_false]; split <;> rfl
      rw [TyEnvSem.resolve_eq _ htv, TyEnvSem.resolve_eq _ rfl,
        TyEnvSem.lookupB_instAt_ne ρ ρ₀ η D R b' hj]

/-- A closed sort is read alike under any bound-variable stack. -/
theorem Base.resolve_closed {b' : Base} (hb' : ∀ j, b' ≠ .tbvar j) (δ δ' : TyEnvSem)
    (hfv : δ.fv = δ'.fv) : b'.resolve δ.sorts = b'.resolve δ'.sorts := by
  cases b' with
  | tbvar j => exact absurd rfl (hb' j)
  | tfvar a => simp [Base.resolve, TyEnvSem.sorts, hfv]
  | _ => rfl

theorem Ty.sortOf_closed {s : Ty} (hs : s.wfB [] [] = true) : ∀ j, s.sortOf ≠ .tbvar j := by
  intro j h
  have := Ty.sortOf_tyOK hs
  rw [h] at this
  simp [Base.tyOK] at this

theorem Ty.sortOf_instTy (k : Nat) (s t : Ty) :
    (Ty.instTy k s t).sortOf =
      if t.sortOf = .tbvar k then s.sortOf else t.sortOf.substB (BSubst.instAt k s.sortOf) := by
  cases t with
  | refine b r =>
    by_cases h : b = .tbvar k
    · subst h; simp only [Ty.instTy, Ty.sortOf, if_true]; cases s <;> rfl
    · simp only [Ty.instTy, Ty.sortOf, h, if_false]
  | _ => simp [Ty.instTy, Ty.sortOf, Base.substB]

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
    strengthening). `kctx`/`ctx` track the enclosing binders. `R` is read at the
    base of `s` (`hRs`), and need only agree with `⟦s⟧` up to the index at which
    the types are compared. -/
theorem TyDenote.instTy_iff {κ : KEnv} (s : Ty) (kd : Kind) (hs : s.wfB [] [] = true)
    (hk : Kind.le s.kindOf kd) (δ₀ : TyEnvSem) (γ₀ : REnv) (R : SemTy)
    (hRs : R.sort = s.semSort δ₀) :
    ∀ (t : Ty) (ρ ρ₀ : List SemTy) (kctx : List Kind) (ctx : List (Option Base))
      (k : Nat) (γ : REnv) (v : Val),
      (∀ k' ≤ k, ∀ w, R.rel k' w ↔ TyDenote κ δ₀ k' s γ₀ w) →
      t.wfB kctx ctx = true → kctx.length = ρ.length + 1 → kctx[ρ.length]? = some kd →
      γ.map = γ₀.map →
      (TyDenote κ ⟨ρ ++ R :: ρ₀, δ₀.fv, δ₀.denv⟩ k t γ v ↔
       TyDenote κ ⟨ρ ++ ρ₀, δ₀.fv, δ₀.denv⟩ k (Ty.instTy ρ.length s t) γ v) := by
  have hcl := Ty.sortOf_closed hs
  -- after instantiating, every sort is read at the base it was read at
  have hres : ∀ (ρ ρ₀ : List SemTy) (c : Base),
      (c.substB (BSubst.instAt ρ.length s.sortOf)).resolve
          (⟨ρ ++ ρ₀, δ₀.fv, δ₀.denv⟩ : TyEnvSem).sorts =
        c.resolve (⟨ρ ++ R :: ρ₀, δ₀.fv, δ₀.denv⟩ : TyEnvSem).sorts := by
    intro ρ ρ₀ c
    refine Base.resolve_instAt hcl ?_ c
    rw [hRs, Ty.semSort_eq]
    exact Base.resolve_closed hcl _ _ rfl
  have hrefn : ∀ (r : Refinement) (ρ ρ₀ : List SemTy) (γ : REnv) (v : Val),
      Refinement.interp κ (r.substB (BSubst.instAt ρ.length s.sortOf))
          ((γ.withSorts (⟨ρ ++ ρ₀, δ₀.fv, δ₀.denv⟩ : TyEnvSem).sorts).push v) ↔
        Refinement.interp κ r ((γ.withSorts (⟨ρ ++ R :: ρ₀, δ₀.fv, δ₀.denv⟩ : TyEnvSem).sorts).push v) :=
    fun r ρ ρ₀ γ v =>
      Refinement.interp_substB _ r rfl rfl (fun _ _ _ => rfl) (fun _ _ => rfl) (fun c _ => hres ρ ρ₀ c)
  intro t
  induction t with
  | refine b r =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    obtain ⟨⟨hty, hstar⟩, hr⟩ := hw
    by_cases hbk : b = .tbvar ρ.length
    · subst hbk
      simp only [Ty.instTy, if_true]
      simp only [TyDenote, BaseDen, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      rw [hR k (Nat.le_refl _) v]
      match s, hs, hk, hcl, hrefn with
      | .refine b' r', hs, hk, hcl, hrefn =>
        rw [← hrefn r ρ ρ₀ γ v]
        simp only [Ty.wfB, Bool.and_eq_true] at hs
        obtain ⟨⟨hty', _⟩, hr's⟩ := hs
        simp only [Ty.strengthen, TyDenote, Refinement.interp]
        have hbase : BaseDen δ₀ k b' v ↔ BaseDen ⟨ρ ++ ρ₀, δ₀.fv, δ₀.denv⟩ k b' v := by
          cases b' with
          | tbvar j => simp [Base.tyOK] at hty'
          | _ => rfl
        have hown : Refinement.interp κ r' ((γ₀.withSorts δ₀.sorts).push v) ↔
            Refinement.interp κ r'
              ((γ.withSorts (⟨ρ ++ ρ₀, δ₀.fv, δ₀.denv⟩ : TyEnvSem).sorts).push v) := by
          refine Refinement.interp_congr r' (by simpa using hmap.symm) rfl ?_ ?_ ?_
          · intro c i hi
            have := Refinement.wfB_hasBVar r' hr's c i hi
            cases i with
            | zero => rfl
            | succ i => simp at this
          · intro i hi
            have := Refinement.wfB_hasMBVar r' hr's i hi
            cases i with
            | zero => rfl
            | succ i => simp at this
          · intro c hc
            have hok := Refinement.sortOK_of_mem_sorts r' hr's c hc
            exact Base.resolve_closed (fun j h => by subst h; simp [Base.sortOK] at hok) _ _ rfl
        rw [hbase, hown, and_assoc]
      | .arrow _ _, hs, hk, _, _ | .forall _ _, hs, hk, _, _ | .prod _ _, hs, hk, _, _
      | .data _ _ _ _, hs, hk, _, _ =>
        have hkd' : kd = .star := by rcases hk with h | h <;> simp_all [Ty.kindOf]
        subst hkd'
        have hstar' : (Base.tbvar ρ.length).isStarB kctx = true := by
          simp [Base.isStarB, hkd]
        simp only [hstar', Bool.not_true, Bool.false_or] at hstar
        simp only [Ty.strengthen, Refinement.interp_of_isTT hstar, and_true]
        exact TyDenote.congr_wf _ [] [] [] δ₀.bv (ρ ++ ρ₀) δ₀.fv δ₀.denv k γ₀ γ v hs rfl hmap.symm
          (fun i hi => by simp at hi)
    · simp only [Ty.instTy, hbk, if_false, TyDenote]
      rw [BaseDen.instAt_ne ρ ρ₀ δ₀.fv δ₀.denv R hbk hty hlen s.sortOf, hrefn r ρ ρ₀ γ v]
  | arrow s₁ t₂ ihs iht =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    simp only [Ty.instTy, TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    refine forall_congr' (fun j => forall_congr' (fun hj => forall_congr' (fun va => ?_)))
    have hRj : ∀ k' ≤ j, ∀ w, R.rel k' w ↔ TyDenote κ δ₀ k' s γ₀ w :=
      fun k' hk' => hR k' (by omega)
    rw [ihs ρ ρ₀ kctx ctx j γ va hRj hw.1 hlen hkd hmap]
    refine imp_congr_right (fun _ => exists_congr (fun body => exists_congr (fun o =>
      and_congr_right (fun _ => and_congr_right (fun _ => ?_)))))
    exact forall_congr' (fun vr => forall_congr' (fun m => imp_congr_right (fun _ =>
      imp_congr_right (fun hm => iht ρ ρ₀ kctx (s₁.optBase :: ctx) m (γ.push va) vr
        (fun k' hk' => hR k' (by omega)) hw.2 hlen hkd (by simpa using hmap)))))
  | «forall» kd' t' ih =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap
    simp only [Ty.wfB] at hw
    simp only [Ty.instTy, TyDenote]
    refine forall_congr' (fun R' => forall_congr' (fun _ => ?_))
    have := ih (R' :: ρ) ρ₀ (kd' :: kctx) (ctx.map (Option.map Base.shiftT)) k γ v hR hw
      (by simp [hlen]) (by simpa using hkd) hmap
    simpa [TyEnvSem.push] using this
  | prod s₁ t₂ ihs iht =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    simp only [Ty.instTy]
    exact TyDenote.prod_congr (fun w => ihs ρ ρ₀ kctx ctx k γ w hR hw.1 hlen hkd hmap)
      (fun w₁ w => iht ρ ρ₀ kctx (s₁.optBase :: ctx) k (γ.push w₁) w hR hw.2 hlen hkd
        (by simpa using hmap))
  | data C n args r ih =>
    intro ρ ρ₀ kctx ctx k γ v hR hw hlen hkd hmap
    simp only [Ty.wfB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hw
    simp only [Ty.instTy]
    refine TyDenote.data_congr rfl (fun l j hj w =>
      ih l ρ ρ₀ kctx ctx j γ w (fun k' hk' => hR k' (by omega)) (hw.2 l) hlen hkd hmap) (fun l => ?_)
      (fun v => (hrefn r ρ ρ₀ γ v).symm)
    rw [Ty.semSort_eq, Ty.semSort_eq, Ty.sortOf_instTy]
    split
    · rename_i h
      rw [h]
      have := hres ρ ρ₀ (.tbvar ρ.length)
      simp only [Base.substB, BSubst.instAt, if_true] at this
      exact this.symm
    · exact (hres ρ ρ₀ _).symm

end STLC
