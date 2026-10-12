import Flex.VCG.STLC.Semantics
import Flex.VCG.STLC.Declarative
import Flex.VCG.STLC.Soundness
import Flex.VCG.STLC.Model
import Flex.VCG.STLC.TypeSubst

open STLC

/-! # Refinement Type Safety for STLC (LN + deep refinements + κ + recursion + ∀)

  With general recursion (`Exp.fix`) programs may diverge, so safety is stated
  *partially* but *fuel-indexed*, against the semantics `Eval` of
  `Semantics.lean`: for every fuel budget, a well-typed closed program either
  times out or returns a value in its type's denotation — and it never gets
  stuck. The logical relation (`TyDenote`, `Model.lean`) is step-indexed by the
  remaining fuel and parameterized by an interpretation `δ` of type variables.

    (T1) `subtyp_sound`         — Subtyping is semantic inclusion of denotations.
    (T2) `hastype_fundamental`  — Well-typed terms are in the expression relation
                                   at every index, under a closing substitution
                                   and every well-kinded type interpretation.
    (T3) `type_safety`          — Closed-term safety (corollary of T2).
    (T4) `vcgen_safety`         — End-to-end VCGen safety:
                                   `topVC κ [] e t → ∀ n, ∃ o, Eval n e o ∧ …`.
-/

namespace STLC

private theorem mem_TEnv_dom {Γ : TEnv} {x : EVar} {t : Ty} (h : (x, t) ∈ Γ) :
    x ∈ TEnv.dom Γ := by
  induction Γ with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨y, ty⟩ := hd
    simp only [TEnv.dom, List.mem_cons]
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | h
    · left; rfl
    · right; exact ih h

/-- `HasBase` only depends on the cell itself. -/
theorem REnv.HasBase_congr {γ γ' : REnv} {y : EVar} {b : Base} (h : γ.map y = γ'.map y) :
    γ.HasBase y b ↔ γ'.HasBase y b := by
  cases b <;> simp [REnv.HasBase, h]

end STLC

/-! ## Value invariants -/

/-- Every value of a base denotation is locally closed and closed. -/
theorem BaseDen.wf {δ : TyEnvSem} {k : Nat} {b : Base} {v : Val}
    (h : BaseDen δ k b v) : Val.lc v ∧ Val.closed v ∧ Val.Erased v := by
  cases b with
  | int  => obtain ⟨n, rfl⟩ := h; exact ⟨trivial, rfl, trivial⟩
  | bool => obtain ⟨c, rfl⟩ := h; exact ⟨trivial, rfl, trivial⟩
  | tbvar _ => exact SemTy.wf _ h
  | tfvar _ => exact SemTy.wf _ h

/-- Every value in a denotation is locally closed and closed. -/
theorem TyDenote.wf {κ : KEnv} {δ : TyEnvSem} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ δ k t γ v) : Val.lc v ∧ Val.closed v ∧ Val.Erased v := by
  induction t generalizing δ γ v with
  | refine b r => simp only [TyDenote] at h; exact BaseDen.wf h.1
  | arrow s t => simp only [TyDenote] at h; exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩
  | «forall» kd t ih =>
    simp only [TyDenote] at h
    exact ih (h SemTy.ints (SemTy.ints_fits kd))
  | prod s t ihs iht =>
    simp only [TyDenote] at h
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    obtain ⟨l₁, c₁, e₁⟩ := ihs h₁
    obtain ⟨l₂, c₂, e₂⟩ := iht h₂
    simp only [Val.lc, Val.closed, Val.fv, Val.Erased, Val.toExp, Exp.lc_at, Exp.fv,
      Exp.TypeFree, List.append_eq_nil_iff] at *
    exact ⟨⟨l₁, l₂⟩, ⟨c₁, c₂⟩, ⟨e₁, e₂⟩⟩
  | data C n args => simp only [TyDenote] at h; exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem TyDenote.closed {κ : KEnv} {δ : TyEnvSem} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ δ k t γ v) : Val.closed v := (TyDenote.wf h).2.1

theorem TyDenote.erased {κ : KEnv} {δ : TyEnvSem} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ δ k t γ v) : Val.Erased v := (TyDenote.wf h).2.2

theorem TyDenote.lc {κ : KEnv} {δ : TyEnvSem} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ δ k t γ v) : Val.lc v := (TyDenote.wf h).1

/-- A value in a denotation is in the expression relation (it evaluates to
    itself without consuming fuel). -/
theorem ExpDenote.of_val {κ : KEnv} {δ : TyEnvSem} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ δ k t γ v) : ExpDenote κ δ k t γ v.toExp :=
  ⟨_, Eval.toExp k v, fun v' m ho => by
    injection ho with h₁ h₂; subst h₁ h₂; exact h⟩

/-- A value in the denotation of a binding type with hypothesis `r` at sort `b`
    satisfies `r` and (under a well-kinded `δ`) has sort `b`. -/
theorem TyDenote.toHyp {κ : KEnv} {δ : TyEnvSem} {k : Nat} {t : Ty} {γ γ' : REnv} {v : Val}
    {b : Base} {r : Refinement} {z : EVar}
    (hδ : δ.WK) (ht : t.hyp? = some (b, r)) (h : TyDenote κ δ k t γ v) (hz : γ'.map z = v) :
    γ'.HasBase z b ∧ Refinement.interp κ r (γ.push v) := by
  have htr := Ty.hyp?_eq_some ht
  subst htr
  simp only [TyDenote] at h
  obtain ⟨hbd, hr⟩ := h
  refine ⟨?_, hr⟩
  cases b with
  | int  => obtain ⟨n, hn⟩ := hbd; exact ⟨n, hz.trans hn⟩
  | bool => obtain ⟨c, hc⟩ := hbd; exact ⟨c, hz.trans hc⟩
  | tbvar _ => simp at ht
  | tfvar a =>
    rcases a with ⟨n, _ | _⟩
    · obtain ⟨b0, hb0, hall⟩ := hδ (n, .B)
      have hopt := hall k v hbd
      rcases hb0 with rfl | rfl
      · cases v <;> simp [Val.optBase] at hopt
        exact Or.inl ⟨_, hz⟩
      · cases v <;> simp [Val.optBase] at hopt
        exact Or.inr ⟨_, hz⟩
    · simp at ht

/-! ## Datatype payloads: syntactic instantiation vs. semantic parameters

  Typing instantiates a constructor's payload type syntactically (`instTys`);
  the logical relation interprets the datatype's parameters semantically. The
  bridge lemma equates the two (below the current step index). -/

theorem Term.interp_nofv {γ γ' : REnv} (hbv : γ.bv = γ'.bv) :
    ∀ {b : Base} (t : Term b), t.fv = [] → Term.interp γ t = Term.interp γ' t := by
  intro b t
  induction t with
  | const => intro _; rfl
  | bvar b k => intro _; simp [Term.interp, REnv.getBV, hbv]
  | fvar b x => intro h; simp [Term.fv] at h
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ =>
    intro h; simp only [Term.fv, List.append_eq_nil_iff] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]
  | not _ ih => intro h; simp only [Term.fv] at h; simp only [Term.interp, ih h]

theorem Formula.interp_nofv (φ : Formula) : ∀ {γ γ' : REnv}, γ.bv = γ'.bv → φ.fv = [] →
    (Formula.interp γ φ ↔ Formula.interp γ' φ) := by
  induction φ with
  | tt | ff => intros; rfl
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
    intro γ γ' hbv h
    simp only [Formula.fv, List.append_eq_nil_iff] at h
    simp only [Formula.interp, Term.interp_nofv hbv t₁ h.1, Term.interp_nofv hbv t₂ h.2]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro γ γ' hbv h
    simp only [Formula.fv, List.append_eq_nil_iff] at h
    simp only [Formula.interp, ih₁ hbv h.1, ih₂ hbv h.2]
  | not _ ih => intro γ γ' hbv h; simp only [Formula.fv] at h; simp only [Formula.interp, ih hbv h]
  | ex b _ ih | all b _ ih =>
    intro γ γ' hbv h
    simp only [Formula.fv] at h
    simp only [Formula.interp]
    first
      | exact exists_congr fun x => ih (by simp [hbv]) h
      | exact forall_congr' fun x => ih (by simp [hbv]) h

theorem Refinement.interp_nofv {κ : KEnv} (r : Refinement) {γ γ' : REnv} (hbv : γ.bv = γ'.bv)
    (h : r.fv = []) : Refinement.interp κ r γ ↔ Refinement.interp κ r γ' := by
  induction r with
  | fmla φ => exact Formula.interp_nofv φ hbv h
  | kapp kn args =>
    simp only [Refinement.fv, List.flatMap_eq_nil_iff] at h
    simp only [Refinement.interp]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a ha
    rw [Term.interp_nofv hbv a.2 (h a ha)]
  | conj _ _ ih₁ ih₂ =>
    simp only [Refinement.fv, List.append_eq_nil_iff] at h
    simp only [Refinement.interp, ih₁ h.1, ih₂ h.2]

/-- A type without free term variables does not read the name map. -/
theorem TyDenote.map_irrel {κ : KEnv} (t : Ty) : t.fv = [] →
    ∀ (δ : TyEnvSem) (k : Nat) (γ γ' : REnv) (v : Val), γ.bv = γ'.bv →
      (TyDenote κ δ k t γ v ↔ TyDenote κ δ k t γ' v) := by
  induction t with
  | refine b r =>
    intro h δ k γ γ' v hbv
    simp only [TyDenote]
    exact and_congr_right fun _ => Refinement.interp_nofv r (by simp [hbv]) (by simpa [Ty.fv] using h)
  | arrow s t ihs iht =>
    intro h δ k γ γ' v hbv
    simp only [Ty.fv, List.append_eq_nil_iff] at h
    simp only [TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    refine forall_congr' (fun j => forall_congr' (fun _ => forall_congr' (fun va => ?_)))
    rw [ihs h.1 δ j γ γ' va hbv]
    refine imp_congr_right (fun _ => exists_congr (fun body => exists_congr (fun o =>
      and_congr_right (fun _ => and_congr_right (fun _ => ?_)))))
    exact forall_congr' (fun vr => forall_congr' (fun m => imp_congr_right (fun _ =>
      imp_congr_right (fun _ => iht h.2 δ m _ _ vr (by simp [hbv])))))
  | «forall» kd t ih =>
    intro h δ k γ γ' v hbv
    simp only [Ty.fv] at h
    simp only [TyDenote]
    exact forall_congr' fun R => forall_congr' fun _ => ih h (δ.push R) k γ γ' v hbv
  | prod s t ihs iht =>
    intro h δ k γ γ' v hbv
    simp only [Ty.fv, List.append_eq_nil_iff] at h
    exact TyDenote.prod_congr (fun w => ihs h.1 δ k γ γ' w hbv)
      (fun w₁ w => iht h.2 δ k _ _ w (by simp [hbv]))
  | data C n args ih =>
    intro h δ k γ γ' v hbv
    simp only [Ty.fv, List.flatMap_eq_nil_iff, List.mem_finRange, true_implies] at h
    exact TyDenote.data_congr rfl (fun l j _ w => ih l (h l) δ j γ γ' w hbv)

/-- A type without free type variables does not read their interpretation. -/
theorem TyDenote.ftv_irrel {κ : KEnv} (t : Ty) : t.ftv = [] →
    ∀ (ρ : List SemTy) (η η' : TVar → SemTy) (D : DEnv) (k : Nat) (γ : REnv) (v : Val),
      (TyDenote κ ⟨ρ, η, D⟩ k t γ v ↔ TyDenote κ ⟨ρ, η', D⟩ k t γ v) := by
  induction t with
  | refine b r =>
    intro h ρ η η' D k γ v
    simp only [TyDenote]
    refine and_congr_left fun _ => ?_
    cases b with
    | tfvar a => simp [Ty.ftv, Base.ftv] at h
    | _ => rfl
  | arrow s t ihs iht =>
    intro h ρ η η' D k γ v
    simp only [Ty.ftv, List.append_eq_nil_iff] at h
    simp only [TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    refine forall_congr' (fun j => forall_congr' (fun _ => forall_congr' (fun va => ?_)))
    rw [ihs h.1 ρ η η' D j γ va]
    refine imp_congr_right (fun _ => exists_congr (fun body => exists_congr (fun o =>
      and_congr_right (fun _ => and_congr_right (fun _ => ?_)))))
    exact forall_congr' (fun vr => forall_congr' (fun m => imp_congr_right (fun _ =>
      imp_congr_right (fun _ => iht h.2 ρ η η' D m _ vr))))
  | «forall» kd t ih =>
    intro h ρ η η' D k γ v
    simp only [Ty.ftv] at h
    simp only [TyDenote]
    exact forall_congr' fun R => forall_congr' fun _ => ih h (R :: ρ) η η' D k γ v
  | prod s t ihs iht =>
    intro h ρ η η' D k γ v
    simp only [Ty.ftv, List.append_eq_nil_iff] at h
    exact TyDenote.prod_congr (fun w => ihs h.1 ρ η η' D k γ w)
      (fun w₁ w => iht h.2 ρ η η' D k _ w)
  | data C n args ih =>
    intro h ρ η η' D k γ v
    simp only [Ty.ftv, List.flatMap_eq_nil_iff, List.mem_finRange, true_implies] at h
    exact TyDenote.data_congr rfl (fun l j _ w => ih l (h l) ρ η η' D j γ w)

/-- Instantiating parameters `ρ.length, …` of `P` one at a time (outermost
    first) is interpreting them by the semantic types `Rs`. -/
theorem TyDenote.instTysFrom_iff {κ : KEnv} (δ : TyEnvSem) (γ : REnv) (ks : List Kind) (P : Ty)
    (k : Nat) :
    ∀ (τs : List Ty) (Rs ρ ρ₀ : List SemTy) (γ' : REnv) (v : Val),
      τs.length = Rs.length → ρ.length + τs.length = ks.length →
      (∀ l (hl : l < τs.length) (hl' : l < Rs.length), ∃ kd, ks[ρ.length + l]? = some kd ∧
        Kind.le τs[l].kindOf kd ∧ τs[l].wfB [] [] = true ∧
        ∀ k' ≤ k, ∀ w, Rs[l].rel k' w ↔ TyDenote κ δ k' τs[l] γ w) →
      Ty.instTysOK ks ρ.length τs P = true → γ'.map = γ.map →
      (TyDenote κ ⟨ρ ++ Rs ++ ρ₀, δ.fv, δ.denv⟩ k P γ' v ↔
       TyDenote κ ⟨ρ ++ ρ₀, δ.fv, δ.denv⟩ k (Ty.instTysFrom ρ.length τs P) γ' v) := by
  intro τs
  induction τs with
  | nil =>
    intro Rs ρ ρ₀ γ' v hlen _ _ _ _
    cases Rs with
    | nil => simp [Ty.instTysFrom]
    | cons => simp at hlen
  | cons τ τs ih =>
    intro Rs ρ ρ₀ γ' v hlen hks hargs hok hmap
    cases Rs with
    | nil => simp at hlen
    | cons R Rs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [Ty.instTysOK, Bool.and_eq_true] at hok
      obtain ⟨kd, hkd, hk, hw, hR⟩ := hargs 0 (by simp) (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at hkd hk hw hR
      have hX := Ty.instTysOK_wfB hok.2
      have hks' : ρ.length + 1 ≤ ks.length := by simp at hks; omega
      have key := TyDenote.instTy_iff (κ := κ) τ kd hw hk δ γ R
        (Ty.instTysFrom (ρ.length + 1) τs P) ρ ρ₀ (ks.take (ρ.length + 1)) [] k γ' v hR hX
        (by simp; omega) (by rw [List.getElem?_take]; simp [hkd]) hmap (fun _ i hi => by simp at hi)
      have ih' := ih Rs (ρ ++ [R]) ρ₀ γ' v hlen (by simp at hks ⊢; omega)
        (fun l hl hl' => by
          obtain ⟨kd', h1, h2, h3, h4⟩ := hargs (l+1) (by simp; omega) (by simp; omega)
          have e : ρ.length + (l + 1) = (ρ ++ [R]).length + l := by simp; omega
          rw [e] at h1
          exact ⟨kd', h1, h2, h3, h4⟩)
        (by simpa using hok.2) hmap
      simp only [Ty.instTysFrom]
      rw [← key]
      simpa [List.append_assoc] using ih'

/-- **Bridge lemma.** A constructor payload instantiated at type arguments is
    the payload with its parameters interpreted by the arguments' denotations
    (as in the logical relation's datatype case). -/
theorem TyDenote.instTys_bridge {κ : KEnv} (δ : TyEnvSem) (γ : REnv) (i : Nat) {n : Nat}
    (args : Fin n → Ty) (ks : List Kind) (P : Ty)
    (hlen : ks.length = n)
    (hargs : ∀ l : Fin n, ∃ kd, ks[l.val]? = some kd ∧
      Kind.le (args l).kindOf kd ∧ (args l).wfB [] [] = true)
    (hok : Ty.instTysOK ks 0 (List.ofFn args) P = true) (hPfv : P.fv = []) (hPftv : P.ftv = [])
    (w : Val) :
    TyDenote κ δ i (Ty.instTys (List.ofFn args) P) γ w ↔
    TyDenote κ ⟨List.ofFn (fun l => SemTy.upto i (fun j' w' => TyDenote κ δ j'.val (args l) γ w')),
      fun _ => SemTy.top, δ.denv⟩ i P REnv.empty w := by
  have hupto : ∀ (t : Ty) k' w, k' ≤ i →
      ((SemTy.upto i (fun j' w' => TyDenote κ δ j'.val t γ w')).rel k' w ↔ TyDenote κ δ k' t γ w) := by
    intro t k' w hk'
    simp only [SemTy.upto]
    constructor
    · rintro ⟨⟨j', hj', h⟩, _⟩; exact TyDenote.mono hj' h
    · intro h; exact ⟨⟨⟨k', by omega⟩, Nat.le_refl _, h⟩, TyDenote.wf h⟩
  let Rs := List.ofFn (fun l => SemTy.upto i (fun j' w' => TyDenote κ δ j'.val (args l) γ w'))
  have hfinal : (Ty.instTys (List.ofFn args) P).wfB [] [] = true := by
    simpa using Ty.instTysOK_wfB hok
  have hPw : P.wfB ks [] = true := by
    have := Ty.instTysOK_last hok
    simp only [Nat.zero_add, List.length_ofFn] at this
    rwa [show n = ks.length from hlen.symm, List.take_length] at this
  obtain ⟨ρδ, ηδ, Dδ⟩ := δ
  have e1 := TyDenote.congr_wf (κ := κ) (Ty.instTys (List.ofFn args) P) [] [] [] ρδ ρδ ηδ Dδ i γ
    ⟨γ.map, []⟩ w hfinal rfl rfl (fun _ h => by simp at h)
  have e2 := TyDenote.instTysFrom_iff (κ := κ) ⟨ρδ, ηδ, Dδ⟩ γ ks P i (List.ofFn args) Rs [] ρδ
    ⟨γ.map, []⟩ w (by simp [Rs]) (by simp [hlen])
    (fun l hl hl' => by
      obtain ⟨kd, h1, h2, h3⟩ := hargs ⟨l, by simpa using hl⟩
      refine ⟨kd, by simpa using h1, by simpa using h2, by simpa using h3, fun k' hk' w' => ?_⟩
      simp only [Rs, List.getElem_ofFn]
      exact hupto _ k' w' hk')
    hok rfl
  have e3 := TyDenote.congr_wf (κ := κ) P ks [] Rs ρδ [] ηδ Dδ i ⟨γ.map, []⟩ ⟨γ.map, []⟩ w hPw
    (by simp [Rs, hlen]) rfl (fun _ h => by simp at h)
  have e4 := TyDenote.ftv_irrel (κ := κ) P hPftv Rs ηδ (fun _ => SemTy.top) Dδ i ⟨γ.map, []⟩ w
  have e5 := TyDenote.map_irrel (κ := κ) P hPfv ⟨Rs, fun _ => SemTy.top, Dδ⟩ i ⟨γ.map, []⟩
    REnv.empty w rfl
  simp only [List.nil_append, List.append_nil, List.length_nil] at e1 e2 e3
  rw [e1, ← e2, e3, e4, e5]

/-! ## Closing environment

  `EnvCloses κ δ k Γ γ` says: `γ` assigns each Γ-binding a value in that
  binding's logical relation at index `k`. Duplicate keys are tolerated
  (head-shadowed entries from `ite`'s context). -/
def EnvCloses : KEnv → TyEnvSem → Nat → TEnv → REnv → Prop
  | _, _, _, [],          _ => True
  | κ, δ, k, (x, t) :: Γ, γ => TyDenote κ δ k t γ (γ.map x) ∧ EnvCloses κ δ k Γ γ

/-- Downward closure of `EnvCloses`. -/
theorem EnvCloses.mono {κ : KEnv} {δ : TyEnvSem} {j k : Nat} (hjk : j ≤ k) :
    ∀ {Γ γ}, EnvCloses κ δ k Γ γ → EnvCloses κ δ j Γ γ
  | [],          _, _ => trivial
  | (_, _) :: _, _, ⟨h, hΓ⟩ => ⟨TyDenote.mono hjk h, EnvCloses.mono hjk hΓ⟩

/-- `EnvCloses` projects to `ModelsEnv` (under a well-kinded `δ`). -/
theorem EnvCloses.toModelsEnv {κ : KEnv} {δ : TyEnvSem} {k : Nat} (hδ : δ.WK) :
    ∀ {Γ γ}, EnvCloses κ δ k Γ γ → ModelsEnv κ γ Γ
  | [],          _, _ => trivial
  | (x, t) :: Γ, γ, ⟨htd, hΓ⟩ => by
      have hrest := EnvCloses.toModelsEnv hδ hΓ
      cases ht : t.hyp? with
      | none => exact (ModelsEnv.cons_none ht).mpr hrest
      | some p =>
        obtain ⟨b, r⟩ := p
        exact (ModelsEnv.cons_some ht).mpr ⟨TyDenote.toHyp hδ ht htd rfl, hrest⟩

/-- Looking up `x` in Γ recovers its denotation at the γ-slot value `γ.map x`. -/
theorem EnvCloses.lookup {κ : KEnv} {δ : TyEnvSem} {k : Nat} :
    ∀ {Γ γ}, EnvCloses κ δ k Γ γ → ∀ {x t}, Γ.lookup x = some t →
      TyDenote κ δ k t γ (γ.map x)
  | [],          _, _, _, _, hl => by simp [List.lookup] at hl
  | (y, s) :: Γ, γ, h, x, t, hl => by
      obtain ⟨hv, hΓ⟩ := h
      by_cases heq : x = y
      · subst heq
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
        exact hl ▸ hv
      · have hne_beq : (x == y) = false := by rw [beq_eq_false_iff_ne]; exact heq
        simp only [List.lookup, hne_beq] at hl
        exact EnvCloses.lookup hΓ hl

/-- Every Γ-bound name maps to a locally-closed value under `EnvCloses`. -/
theorem EnvCloses.mem_lc {κ : KEnv} {δ : TyEnvSem} {k : Nat} :
    ∀ {Γ γ}, EnvCloses κ δ k Γ γ → ∀ {x}, x ∈ TEnv.dom Γ → Val.lc (γ.map x)
  | [],          _, _, _, hx => by simp [TEnv.dom] at hx
  | (y, t) :: Γ, γ, h, x, hx => by
      obtain ⟨hv, hΓ⟩ := h
      simp only [TEnv.dom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact TyDenote.lc hv
      · exact EnvCloses.mem_lc hΓ hx

/-- Every Γ-bound name maps to a closed value (no free names) under `EnvCloses`. -/
theorem EnvCloses.mem_closed {κ : KEnv} {δ : TyEnvSem} {k : Nat} :
    ∀ {Γ γ}, EnvCloses κ δ k Γ γ → ∀ {x}, x ∈ TEnv.dom Γ → Val.closed (γ.map x)
  | [],          _, _, _, hx => by simp [TEnv.dom] at hx
  | (y, t) :: Γ, γ, h, x, hx => by
      obtain ⟨hv, hΓ⟩ := h
      simp only [TEnv.dom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact TyDenote.closed hv
      · exact EnvCloses.mem_closed hΓ hx

/-- Every Γ-bound name maps to a type-erased value under `EnvCloses`. -/
theorem EnvCloses.mem_erased {κ : KEnv} {δ : TyEnvSem} {k : Nat} :
    ∀ {Γ γ}, EnvCloses κ δ k Γ γ → ∀ {x}, x ∈ TEnv.dom Γ → Val.Erased (γ.map x)
  | [],          _, _, _, hx => by simp [TEnv.dom] at hx
  | (y, t) :: Γ, γ, h, x, hx => by
      obtain ⟨hv, hΓ⟩ := h
      simp only [TEnv.dom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact TyDenote.erased hv
      · exact EnvCloses.mem_erased hΓ hx

/-- Rebinding a type variable absent from Γ preserves `EnvCloses`. -/
theorem EnvCloses.set_fresh {κ : KEnv} {δ : TyEnvSem} {k : Nat} {a : TVar} {R : SemTy} :
    ∀ {Γ γ}, a ∉ TEnv.ftv Γ → EnvCloses κ δ k Γ γ → EnvCloses κ (δ.set a R) k Γ γ
  | [],          _, _, _ => trivial
  | (_, t) :: _, _, ha, ⟨h, hΓ⟩ => by
      simp only [TEnv.ftv, List.mem_append, not_or] at ha
      exact ⟨(TyDenote.set_fresh_iff t ha.1 _ _ _ _).mpr h, EnvCloses.set_fresh ha.2 hΓ⟩

/-- Re-interpreting type variables the context does not mention preserves it. -/
theorem EnvCloses.reinterp {κ : KEnv} {δ δ' : TyEnvSem} {k : Nat} {as : List TVar} {Γ : TEnv}
    {γ : REnv} (has : ∀ a ∈ as, a ∉ TEnv.ftv Γ) (h : TyEnvSem.Reinterp as δ δ')
    (hE : EnvCloses κ δ k Γ γ) : EnvCloses κ δ' k Γ γ := by
  induction h with
  | refl => exact hE
  | set a R ha _ _ ih => exact EnvCloses.set_fresh (has a ha) ih

/-! ## extendBy commutativity and extendBy_fresh -/

/-- Writing a fresh `x` (`x ∉ r.fv`) does not change `Refinement.interp` under
    *any* `γ`. -/
private theorem Refinement.interp_write_fresh {κ : KEnv} (r : Refinement)
    (x : EVar) (va : Val) (γ : REnv)
    (hx : x ∉ Refinement.fv r) :
    Refinement.interp κ r γ ↔ Refinement.interp κ r (γ.write x va) := by
  induction r with
  | fmla φ =>
    simp only [Refinement.fv] at hx
    simp only [Refinement.interp]
    exact (Formula.interp_write_fresh φ x va γ hx).symm
  | kapp kn args =>
    have hargs : ∀ a ∈ args, x ∉ Term.fv a.2 := fun a ha hm =>
      hx (by simp only [Refinement.fv, List.mem_flatMap]; exact ⟨a, ha, hm⟩)
    simp only [Refinement.interp]
    apply Iff.of_eq; congr 1
    apply List.map_congr_left
    intro a ha
    congr 1
    exact (Term.interp_write_fresh a.2 x va γ (hargs a ha)).symm
  | conj r₁ r₂ ih₁ ih₂ =>
    simp only [Refinement.fv, List.mem_append, not_or] at hx
    simp only [Refinement.interp]
    exact and_congr (ih₁ hx.1) (ih₂ hx.2)

/-- `TyDenote` is invariant under writing a name `x` not free in `t`. -/
theorem TyDenote.extendBy_fresh_iff {κ : KEnv} (t : Ty) :
    ∀ (δ : TyEnvSem) (k : Nat) (γ : REnv) (v : Val) (x : EVar) (va : Val), x ∉ t.fv →
      (TyDenote κ δ k t γ v ↔ TyDenote κ δ k t (γ.write x va) v) := by
  induction t with
  | refine b r =>
    intro δ k γ v x va hx
    have hx' : x ∉ Refinement.fv r := by simpa [Ty.fv] using hx
    simp only [TyDenote]
    refine and_congr_right (fun _ => ?_)
    rw [REnv.push_write_comm]
    exact Refinement.interp_write_fresh r x va _ hx'
  | arrow s' t' ihs iht =>
    intro δ k γ v x va hx
    simp only [Ty.fv, List.mem_append, not_or] at hx
    simp only [TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    constructor
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ := hLR j hj va' ((ihs δ j γ va' x va hx.1).mpr htd)
      refine ⟨body, o, hap, hev, fun vr m ho hm => ?_⟩
      rw [REnv.push_write_comm]
      exact (iht δ m (γ.push va') vr x va hx.2).mp (hres vr m ho hm)
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ := hLR j hj va' ((ihs δ j γ va' x va hx.1).mp htd)
      refine ⟨body, o, hap, hev, fun vr m ho hm => ?_⟩
      have h := hres vr m ho hm
      rw [REnv.push_write_comm] at h
      exact (iht δ m (γ.push va') vr x va hx.2).mpr h
  | «forall» kd t ih =>
    intro δ k γ v x va hx
    simp only [Ty.fv] at hx
    simp only [TyDenote]
    exact forall_congr' (fun R => forall_congr' (fun _ => ih (δ.push R) k γ v x va hx))
  | prod s' t' ihs iht =>
    intro δ k γ v x va hx
    simp only [Ty.fv, List.mem_append, not_or] at hx
    refine TyDenote.prod_congr (fun w => ihs δ k γ w x va hx.1) (fun w₁ w => ?_)
    rw [REnv.push_write_comm]
    exact iht δ k (γ.push w₁) w x va hx.2
  | data C n args ih =>
    intro δ k γ v x va hx
    simp only [Ty.fv, List.mem_flatMap, List.mem_finRange, true_and, not_exists] at hx
    exact TyDenote.data_congr rfl (fun l j _ w => ih l δ j γ w x va (hx l))

/-- TyDenote is monotone under writing at a variable `x` not free in `t`. -/
theorem TyDenote.extendBy_fresh {κ : KEnv} {δ : TyEnvSem} {k : Nat} {t : Ty} {γ : REnv}
    {v : Val} (x : EVar) (va : Val) (hx : x ∉ t.fv) (h : TyDenote κ δ k t γ v) :
    TyDenote κ δ k t (γ.write x va) v :=
  (TyDenote.extendBy_fresh_iff t δ k γ v x va hx).mp h

/-- Reverse direction: TyDenote under a fresh write implies TyDenote at γ. -/
theorem TyDenote.of_extendBy_fresh {κ : KEnv} {δ : TyEnvSem} {k : Nat} {t : Ty} {γ : REnv}
    {v : Val} (x : EVar) (va : Val) (hx : x ∉ t.fv) (h : TyDenote κ δ k t (γ.write x va) v) :
    TyDenote κ δ k t γ v :=
  (TyDenote.extendBy_fresh_iff t δ k γ v x va hx).mpr h

/-! ## push ↔ openVar bridge

  `TyDenote` threads arrow-binder values through the de Bruijn stack (`γ.push
  va`). Relating that to `openVar` uses the premise-free model bridge
  `Refinement.interp_openBVar` (Substitution.lean). -/

/-- Master bridge (push ↔ openVar): interpreting `t` with `va` inserted at de
    Bruijn level `ρ.length` equals interpreting `t.openVar` with `x ↦ va` written
    into the name map. -/
private theorem TyDenote.insertBV_openVar_aux {κ : KEnv} (t : Ty) :
    ∀ (ρ : List (Option Base)) (δ : TyEnvSem) (k : Nat) (x : EVar) (γ : REnv) (va : Val) (v : Val),
      ρ.length ≤ γ.bv.length → x ∉ t.fv →
      (TyDenote κ δ k t (γ.insertBV ρ.length va) v ↔
       TyDenote κ δ k (t.openVar ρ.length x) (γ.write x va) v) := by
  induction t with
  | refine b r =>
    intro ρ δ k x γ va v hlen hxf
    simp only [Ty.fv] at hxf
    simp only [Ty.openVar, TyDenote]
    refine and_congr_right (fun _ => ?_)
    rw [REnv.push_insertBV_comm, REnv.write_push]
    exact (Refinement.interp_openBVar κ r (γ.push v) x va (ρ.length + 1)
      (by simpa using Nat.succ_le_succ hlen) hxf).symm
  | arrow s' t' ihs iht =>
    intro ρ δ k x γ va v hlen hxf
    simp only [Ty.fv, List.mem_append, not_or] at hxf
    simp only [Ty.openVar, TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ =>
      and_congr_right (fun _ => ?_))))
    constructor
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ :=
        hLR j hj va' ((ihs ρ δ j x γ va va' hlen hxf.1).mpr htd)
      refine ⟨body, o, hap, hev, fun vr m ho hm => ?_⟩
      have h := hres vr m ho hm
      rw [REnv.push_insertBV_comm] at h
      rw [REnv.push_write_comm]
      exact (iht (s'.optBase :: ρ) δ m x (γ.push va') va vr
        (Nat.succ_le_succ hlen) hxf.2).mp h
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ :=
        hLR j hj va' ((ihs ρ δ j x γ va va' hlen hxf.1).mp htd)
      refine ⟨body, o, hap, hev, fun vr m ho hm => ?_⟩
      have h := hres vr m ho hm
      rw [REnv.push_write_comm] at h
      rw [REnv.push_insertBV_comm]
      exact (iht (s'.optBase :: ρ) δ m x (γ.push va') va vr
        (Nat.succ_le_succ hlen) hxf.2).mpr h
  | «forall» kd t ih =>
    intro ρ δ k x γ va v hlen hxf
    simp only [Ty.fv] at hxf
    simp only [Ty.openVar, TyDenote]
    exact forall_congr' (fun R => forall_congr' (fun _ => ih ρ (δ.push R) k x γ va v hlen hxf))
  | prod s' t' ihs iht =>
    intro ρ δ k x γ va v hlen hxf
    simp only [Ty.fv, List.mem_append, not_or] at hxf
    simp only [Ty.openVar]
    refine TyDenote.prod_congr (fun w => ihs ρ δ k x γ va w hlen hxf.1) (fun w₁ w => ?_)
    rw [REnv.push_insertBV_comm, REnv.push_write_comm]
    exact iht (s'.optBase :: ρ) δ k x (γ.push w₁) va w (Nat.succ_le_succ hlen) hxf.2
  | data C n args ih =>
    intro ρ δ k x γ va v hlen hxf
    simp only [Ty.fv, List.mem_flatMap, List.mem_finRange, true_and, not_exists] at hxf
    simp only [Ty.openVar]
    exact TyDenote.data_congr rfl (fun l j _ w => ih l ρ δ j x γ va w hlen (hxf l))

/-- `push va` in TyDenote corresponds to `openVar 0 x` with `γ.write x va`, when
    `x` is fresh for `t`. -/
theorem TyDenote.push_iff (κ : KEnv) (δ : TyEnvSem) (k : Nat) (t : Ty) (x : EVar) (γ : REnv)
    (va : Val) (v : Val) (hx_fv : x ∉ t.fv) :
    TyDenote κ δ k t (γ.push va) v ↔
    TyDenote κ δ k (t.openVar 0 x) (γ.write x va) v := by
  have h := TyDenote.insertBV_openVar_aux (κ := κ) t [] δ k x γ va v (by simp) hx_fv
  simpa using h

/-- `EnvCloses` is preserved when extending `γ` at a name `x` fresh for Γ. -/
theorem EnvCloses.extendBy_fresh {κ δ k Γ γ} (hE : EnvCloses κ δ k Γ γ)
    (x : EVar) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ) :
    EnvCloses κ δ k Γ (γ.write x va) := by
  induction Γ with
  | nil => exact True.intro
  | cons hd tl ih =>
    obtain ⟨y, t⟩ := hd
    obtain ⟨htd, hΓ⟩ := hE
    simp only [TEnv.dom, List.mem_cons, not_or] at hx_dom
    simp only [TEnv.tyFv, List.mem_append, not_or] at hx_fv
    have hxy : x ≠ y := hx_dom.1
    refine ⟨?_, ih hΓ hx_dom.2 hx_fv.2⟩
    rw [REnv.write_other γ x va hxy]
    exact TyDenote.extendBy_fresh x va hx_fv.1 htd

/-- Extend `EnvCloses` by prepending a fresh `(x, s)` binding whose value `va`
    is the value written at `x`. -/
theorem EnvCloses.extend {κ δ k Γ γ} (hE : EnvCloses κ δ k Γ γ)
    (x : EVar) (s : Ty) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ)
    (htd : TyDenote κ δ k s (γ.write x va) va) :
    EnvCloses κ δ k ((x, s) :: Γ) (γ.write x va) := by
  refine ⟨?_, EnvCloses.extendBy_fresh hE x va hx_dom hx_fv⟩
  rw [show (γ.write x va).map x = va by exact REnv.write_self γ x va]
  exact htd

/-! ## Variance: datatype denotations are monotone in their parameters

  If the parameters' interpretations are related as their declared variances
  require, a type in which they occur only at allowed polarities is related
  accordingly. Proved by induction on the step index (datatype payloads are read
  one step later), then on the type. -/

def STLC.SemTy.Le (R R' : SemTy) : Prop := ∀ k w, R.rel k w → R'.rel k w

/-- How two interpretations of a parameter of this variance must relate. -/
def STLC.Variance.Rel : Variance → SemTy → SemTy → Prop
  | .co,     R, R' => SemTy.Le R R'
  | .contra, R, R' => SemTy.Le R' R
  | .inv,    R, R' => SemTy.Le R R' ∧ SemTy.Le R' R

/-- Parameter interpretations `ρ`, `ρ'` related as the variances `vs` require. -/
def STLC.RelVar (vs : List Variance) (ρ ρ' : List SemTy) : Prop :=
  ∀ i : Nat, ((vs[i]?).getD Variance.inv).Rel (ρ[i]?.getD SemTy.top) (ρ'[i]?.getD SemTy.top)

theorem STLC.Pol.comp_ne_neg {p : Pol} {v : Variance} (hp : p ≠ .neg) (hv : v ≠ .contra) :
    p.comp v ≠ .neg := by cases v <;> cases p <;> simp_all [Pol.comp, Pol.flip]
theorem STLC.Pol.comp_ne_pos {p : Pol} {v : Variance} (hp : p ≠ .neg) (hv : v ≠ .co) :
    p.comp v ≠ .pos := by cases v <;> cases p <;> simp_all [Pol.comp, Pol.flip]
theorem STLC.Pol.comp_ne_pos' {p : Pol} {v : Variance} (hp : p ≠ .pos) (hv : v ≠ .contra) :
    p.comp v ≠ .pos := by cases v <;> cases p <;> simp_all [Pol.comp, Pol.flip]
theorem STLC.Pol.comp_ne_neg' {p : Pol} {v : Variance} (hp : p ≠ .pos) (hv : v ≠ .co) :
    p.comp v ≠ .neg := by cases v <;> cases p <;> simp_all [Pol.comp, Pol.flip]

theorem STLC.Variance.Rel_upto {i : Nat} {A B : Fin (i+1) → Val → Prop} (v : Variance)
    (hf : v ≠ .contra → ∀ j w, A j w → B j w) (hb : v ≠ .co → ∀ j w, B j w → A j w) :
    v.Rel (SemTy.upto i A) (SemTy.upto i B) := by
  have le : ∀ {A B : Fin (i+1) → Val → Prop}, (∀ j w, A j w → B j w) →
      SemTy.Le (SemTy.upto i A) (SemTy.upto i B) := by
    intro A B h k w hw
    obtain ⟨⟨j, hj, hA⟩, hwf⟩ := hw
    exact ⟨⟨j, hj, h j w hA⟩, hwf⟩
  cases v with
  | co => exact le (hf (by simp))
  | contra => exact le (hb (by simp))
  | inv => exact ⟨le (hf (by simp)), le (hb (by simp))⟩

theorem STLC.RelVar.ofFn {n i : Nat} (vs : List Variance) (A B : Fin n → Fin (i+1) → Val → Prop)
    (h : ∀ l : Fin n, ((vs[l.val]?).getD .inv).Rel (SemTy.upto i (A l)) (SemTy.upto i (B l))) :
    RelVar vs (List.ofFn fun l => SemTy.upto i (A l)) (List.ofFn fun l => SemTy.upto i (B l)) := by
  intro j
  by_cases hj : j < n
  · simp only [List.getElem?_ofFn, hj, dif_pos, Option.getD_some]
    exact h ⟨j, hj⟩
  · simp only [List.getElem?_ofFn, hj, dif_neg, not_false_eq_true, Option.getD_none]
    cases (vs[j]?).getD .inv <;>
      simp [Variance.Rel, SemTy.Le]

theorem TyDenote.var_mono {κ : KEnv} {de : DEnv} (hde : de.wfB = true) :
    ∀ (k : Nat) (t : Ty) (vs : List Variance) (p : Pol) (inner ρ ρ' : List SemTy)
      (η : TVar → SemTy) (γ : REnv) (v : Val),
      t.varOK de vs inner.length p = true → RelVar vs ρ ρ' →
      (p ≠ .neg → TyDenote κ ⟨inner ++ ρ, η, de⟩ k t γ v → TyDenote κ ⟨inner ++ ρ', η, de⟩ k t γ v) ∧
      (p ≠ .pos → TyDenote κ ⟨inner ++ ρ', η, de⟩ k t γ v → TyDenote κ ⟨inner ++ ρ, η, de⟩ k t γ v) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k IHk =>
  intro t
  induction t with
  | refine b r =>
    intro vs p inner ρ ρ' η γ v hok hrel
    simp only [TyDenote]
    suffices hb : (p ≠ .neg → BaseDen ⟨inner ++ ρ, η, de⟩ k b v → BaseDen ⟨inner ++ ρ', η, de⟩ k b v) ∧
        (p ≠ .pos → BaseDen ⟨inner ++ ρ', η, de⟩ k b v → BaseDen ⟨inner ++ ρ, η, de⟩ k b v) by
      exact ⟨fun hp h => ⟨hb.1 hp h.1, h.2⟩, fun hp h => ⟨hb.2 hp h.1, h.2⟩⟩
    cases b with
    | tbvar j =>
      simp only [Ty.varOK] at hok
      by_cases hj : j < inner.length
      · simp only [BaseDen, List.getElem?_append_left hj]; exact ⟨fun _ h => h, fun _ h => h⟩
      · simp only [hj, if_false] at hok
        have e : ∀ ρ₀ : List SemTy, (inner ++ ρ₀)[j]? = ρ₀[j - inner.length]? :=
          fun ρ₀ => List.getElem?_append_right (by omega)
        simp only [BaseDen, e]
        have hr := hrel (j - inner.length)
        generalize ((vs[j - inner.length]?).getD .inv) = va at hok hr
        generalize (ρ[j - inner.length]?.getD SemTy.top) = R at hr ⊢
        generalize (ρ'[j - inner.length]?.getD SemTy.top) = R' at hr ⊢
        cases va <;> cases p <;> simp_all [Variance.allows, Variance.Rel, SemTy.Le]
    | _ => exact ⟨fun _ h => h, fun _ h => h⟩
  | arrow s t _ _ =>
    intro vs p inner ρ ρ' η γ v hok hrel
    simp only [Ty.varOK, Bool.and_eq_true] at hok
    simp only [TyDenote]
    constructor
    · rintro hp ⟨hf, hlc, hcl, her, hLR⟩
      refine ⟨hf, hlc, hcl, her, fun j hj va hva => ?_⟩
      have hp' : p.flip ≠ .pos := by cases p <;> simp_all [Pol.flip]
      obtain ⟨body, o, hap, hev, hres⟩ :=
        hLR j hj va ((IHk j hj s vs p.flip inner ρ ρ' η γ va hok.1 hrel).2 hp' hva)
      exact ⟨body, o, hap, hev, fun vr m ho hm =>
        (IHk m (by omega) t vs p inner ρ ρ' η _ vr hok.2 hrel).1 hp (hres vr m ho hm)⟩
    · rintro hp ⟨hf, hlc, hcl, her, hLR⟩
      refine ⟨hf, hlc, hcl, her, fun j hj va hva => ?_⟩
      have hp' : p.flip ≠ .neg := by cases p <;> simp_all [Pol.flip]
      obtain ⟨body, o, hap, hev, hres⟩ :=
        hLR j hj va ((IHk j hj s vs p.flip inner ρ ρ' η γ va hok.1 hrel).1 hp' hva)
      exact ⟨body, o, hap, hev, fun vr m ho hm =>
        (IHk m (by omega) t vs p inner ρ ρ' η _ vr hok.2 hrel).2 hp (hres vr m ho hm)⟩
  | «forall» kd t ih =>
    intro vs p inner ρ ρ' η γ v hok hrel
    simp only [Ty.varOK] at hok
    simp only [TyDenote]
    have h := fun R => ih vs p (R :: inner) ρ ρ' η γ v (by simpa using hok) hrel
    constructor
    · intro hp hv R hR
      have := (h R).1 hp (by simpa [TyEnvSem.push] using hv R hR)
      simpa [TyEnvSem.push] using this
    · intro hp hv R hR
      have := (h R).2 hp (by simpa [TyEnvSem.push] using hv R hR)
      simpa [TyEnvSem.push] using this
  | prod s t ihs iht =>
    intro vs p inner ρ ρ' η γ v hok hrel
    simp only [Ty.varOK, Bool.and_eq_true] at hok
    simp only [TyDenote]
    constructor
    · rintro hp ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, rfl, (ihs vs p inner ρ ρ' η γ v₁ hok.1 hrel).1 hp h₁,
        (iht vs p inner ρ ρ' η _ v₂ hok.2 hrel).1 hp h₂⟩
    · rintro hp ⟨v₁, v₂, rfl, h₁, h₂⟩
      exact ⟨v₁, v₂, rfl, (ihs vs p inner ρ ρ' η γ v₁ hok.1 hrel).2 hp h₁,
        (iht vs p inner ρ ρ' η _ v₂ hok.2 hrel).2 hp h₂⟩
  | data C n args _ =>
    intro vs p inner ρ ρ' η γ v hok hrel
    simp only [Ty.varOK, List.all_eq_true, List.mem_finRange, true_implies] at hok
    -- the arguments are related at every index below `k`, by their polarity
    have harg : ∀ l : Fin n, ∀ j < k, ∀ w,
        (p.comp (de.var C l) ≠ .neg → TyDenote κ ⟨inner ++ ρ, η, de⟩ j (args l) γ w →
          TyDenote κ ⟨inner ++ ρ', η, de⟩ j (args l) γ w) ∧
        (p.comp (de.var C l) ≠ .pos → TyDenote κ ⟨inner ++ ρ', η, de⟩ j (args l) γ w →
          TyDenote κ ⟨inner ++ ρ, η, de⟩ j (args l) γ w) :=
      fun l j hj w => IHk j hj (args l) vs _ inner ρ ρ' η γ w (hok l) hrel
    -- transfer a payload between related parameter interpretations
    have hpay : ∀ i < k, ∀ (A B : Fin n → Fin (i+1) → Val → Prop) (j : Nat) (P : Ty) (w : Val),
        de.payload? C j = some P →
        (∀ l : Fin n, (de.var C l.val).Rel (SemTy.upto i (A l)) (SemTy.upto i (B l))) →
        TyDenote κ ⟨List.ofFn (fun l => SemTy.upto i (A l)), fun _ => SemTy.top, de⟩ i P REnv.empty w →
        TyDenote κ ⟨List.ofFn (fun l => SemTy.upto i (B l)), fun _ => SemTy.top, de⟩ i P REnv.empty w := by
      intro i hi A B j P w hP hAB hw
      obtain ⟨d, hd, -, -, hvar⟩ := DEnv.wfB_payload_all hde hP
      have hvl : ∀ l, de.var C l = (d.variances[l]?).getD .inv := fun l => by simp [DEnv.var, hd]
      have hrel' := RelVar.ofFn d.variances A B (fun l => by rw [← hvl]; exact hAB l)
      have := (IHk i hi P d.variances .pos [] _ _ (fun _ => SemTy.top) REnv.empty w
        (by simpa using hvar) hrel').1 (by simp)
      simpa using this (by simpa using hw)
    simp only [TyDenote]
    constructor
    · rintro hp ⟨hlc, hcl, her, j, w, P, rfl, hP, hw⟩
      refine ⟨hlc, hcl, her, j, w, P, rfl, hP, fun i hi => ?_⟩
      refine hpay i hi _ _ j P w hP (fun l => ?_) (hw i hi)
      apply Variance.Rel_upto
      · intro hv j' w' h
        exact (harg l j'.val (by have := j'.isLt; omega) w').1 (Pol.comp_ne_neg hp hv) h
      · intro hv j' w' h
        exact (harg l j'.val (by have := j'.isLt; omega) w').2 (Pol.comp_ne_pos hp hv) h
    · rintro hp ⟨hlc, hcl, her, j, w, P, rfl, hP, hw⟩
      refine ⟨hlc, hcl, her, j, w, P, rfl, hP, fun i hi => ?_⟩
      refine hpay i hi _ _ j P w hP (fun l => ?_) (hw i hi)
      apply Variance.Rel_upto
      · intro hv j' w' h
        exact (harg l j'.val (by have := j'.isLt; omega) w').2 (Pol.comp_ne_pos' hp hv) h
      · intro hv j' w' h
        exact (harg l j'.val (by have := j'.isLt; omega) w').1 (Pol.comp_ne_neg' hp hv) h

/-! ## T1 — Subtyping is semantic inclusion of denotations -/

private theorem Subtyp.optBase_eq {de κ Γ s t} (h : Subtyp de κ Γ s t) : s.optBase = t.optBase := by
  cases h with
  | refine _ _ => rfl
  | arrow => simp [Ty.optBase]
  | «forall» | prod | data => rfl

/-- ModelsEnv is preserved when extending γ at z fresh from Γ. -/
private theorem ModelsEnv.extendBy_fresh_aux {κ : KEnv} {Γ : TEnv} {γ : REnv}
    (hm : ModelsEnv κ γ Γ) (z : EVar) (va : Val)
    (hz_dom : z ∉ TEnv.dom Γ)
    (hz_fv : z ∉ TEnv.tyFv Γ) :
    ModelsEnv κ (γ.write z va) Γ := by
  induction Γ with
  | nil => exact True.intro
  | cons hd tl ih =>
    obtain ⟨y, t⟩ := hd
    simp only [TEnv.dom, List.mem_cons, not_or] at hz_dom
    simp only [TEnv.tyFv, List.mem_append, not_or] at hz_fv
    have htail := ih hm.tail hz_dom.2 hz_fv.2
    cases ht : t.hyp? with
    | none => exact (ModelsEnv.cons_none ht).mpr htail
    | some p =>
      obtain ⟨b, r⟩ := p
      obtain ⟨⟨hHB, hhead⟩, _⟩ := (ModelsEnv.cons_some ht).mp hm
      have hzy : z ≠ y := hz_dom.1
      have hmap : (γ.write z va).map y = γ.map y := REnv.write_other γ z va hzy
      have htr := Ty.hyp?_eq_some ht
      subst htr
      have hz_rfv : z ∉ Refinement.fv r := by simpa [Ty.fv] using hz_fv.1
      refine (ModelsEnv.cons_some ht).mpr ⟨⟨(REnv.HasBase_congr hmap).mpr hHB, ?_⟩, htail⟩
      rw [show (γ.write z va).lookup y = γ.lookup y from hmap, REnv.push_write_comm]
      exact (Refinement.interp_write_fresh r z va _ hz_rfv).mp hhead

/-- Build ModelsEnv after prepending a fresh binding (z, s₂) whose value is in
    `s₂`'s denotation. -/
private theorem ModelsEnv.extendBy_cons {κ : KEnv} {δ : TyEnvSem} {Γ : TEnv} {γ : REnv} {k : Nat}
    (hδ : δ.WK) (hm : ModelsEnv κ γ Γ) (s₂ : Ty) (z : EVar) (va : Val)
    (hz_dom : z ∉ TEnv.dom Γ)
    (hz_fv : z ∉ TEnv.tyFv Γ)
    (hz_s2fv : z ∉ s₂.fv)
    (htd_va : TyDenote κ δ k s₂ γ va) :
    ModelsEnv κ (γ.write z va) ((z, s₂) :: Γ) := by
  have htail := ModelsEnv.extendBy_fresh_aux hm z va hz_dom hz_fv
  cases ht : s₂.hyp? with
  | none => exact (ModelsEnv.cons_none ht).mpr htail
  | some p =>
    obtain ⟨b, r⟩ := p
    obtain ⟨hHB, hr⟩ := TyDenote.toHyp hδ ht htd_va (REnv.write_self γ z va)
    have htr := Ty.hyp?_eq_some ht
    subst htr
    have hz_rfv : z ∉ Refinement.fv r := by simpa [Ty.fv] using hz_s2fv
    refine (ModelsEnv.cons_some ht).mpr ⟨⟨hHB, ?_⟩, htail⟩
    rw [show (γ.write z va).lookup z = va from REnv.write_self γ z va, REnv.push_write_comm]
    exact (Refinement.interp_write_fresh r z va _ hz_rfv).mp hr

theorem subtyp_sound {de κ Γ s t} (hde : de.wfB = true) (hsub : Subtyp de κ Γ s t)
    (hWF_s : Ty.WFBVars s) (hWF_t : Ty.WFBVars t) :
    ∀ {δ}, δ.WK → δ.denv = de → ∀ {k γ}, ModelsEnv κ γ Γ → ∀ {v},
      TyDenote κ δ k s γ v → TyDenote κ δ k t γ v := by
  induction hsub with
  | refine hfresh hent =>
      rename_i b r₁ r₂ x
      intro δ hδ hD k γ hΓ v hs
      simp only [List.mem_append, not_or] at hfresh
      obtain ⟨⟨⟨hx_dom, hx_tyfv⟩, hx_r₁⟩, hx_r₂⟩ := hfresh
      have hx_r₁' : x ∉ (Ty.refine b r₁).fv := by simpa [Ty.fv] using hx_r₁
      -- Feed the witness through the opened rule: extend the model at the fresh
      -- `x`, read off the opened `r₂`, then close ν back to push form.
      have h := hent _ (ModelsEnv.extendBy_cons hδ hΓ _ x _ hx_dom hx_tyfv hx_r₁' hs)
      simp only [TyDenote] at hs ⊢
      refine ⟨hs.1, ?_⟩
      have := (Refinement.interp_openBVar κ r₂ γ x v 0 (Nat.zero_le _) hx_r₂).mp h
      simpa using this
  | arrow hdom hfresh hcodom ih_hdom ih_hcodom =>
    rename_i Γ' s₁ t₁ s₂ t₂ x
    obtain ⟨hWF_s1, hWF_st1⟩ := hWF_s
    obtain ⟨hWF_s2, hWF_t2⟩ := hWF_t
    have hopt_eq : s₂.optBase = s₁.optBase := by grind [Subtyp.optBase_eq]
    have hWF_st1' : Ty.WFBVarCtx [s₂.optBase] t₁ := hopt_eq ▸ hWF_st1
    simp only [List.mem_append, not_or] at hfresh
    obtain ⟨⟨⟨⟨⟨hx_Γdom, hx_Γfv⟩, hx_s1fv⟩, hx_s2fv⟩, hx_t1fv⟩, hx_t2fv⟩ := hfresh
    intro δ hδ hD k γ hm v htd
    simp only [TyDenote] at htd ⊢
    obtain ⟨hfun, hlc, hcl, her, hLR⟩ := htd
    refine ⟨hfun, hlc, hcl, her, fun j hj va htd_va => ?_⟩
    -- Domain conversion (contravariant): s₂ <: s₁
    have htd_va_s1 : TyDenote κ δ j s₁ γ va := ih_hdom hWF_s2 hWF_s1 hδ hD hm htd_va
    obtain ⟨body, o, hap, hev, hres⟩ := hLR j hj va htd_va_s1
    refine ⟨body, o, hap, hev, fun vr m ho hm' => ?_⟩
    have hWF_t1x : Ty.WFBVars (t₁.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₁ [] s₂.optBase x hWF_st1'
    have hWF_t2x : Ty.WFBVars (t₂.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₂ [] s₂.optBase x hWF_t2
    have htd_vr_t1 := (TyDenote.push_iff κ δ m t₁ x γ va vr hx_t1fv).mp (hres vr m ho hm')
    have hm_ext : ModelsEnv κ (γ.write x va) ((x, s₂) :: Γ') :=
      ModelsEnv.extendBy_cons hδ hm s₂ x va hx_Γdom hx_Γfv hx_s2fv htd_va
    exact (TyDenote.push_iff κ δ m t₂ x γ va vr hx_t2fv).mpr
      (ih_hcodom hWF_t1x hWF_t2x hδ hD hm_ext htd_vr_t1)
  | «forall» hka hfresh hbody ih =>
    rename_i Γ' kd t₁ t₂ a
    simp only [List.mem_append, not_or] at hfresh
    have hWF₁ : Ty.WFBVars (t₁.openTv 0 a) :=
      Ty.WFBVars_openTv t₁ 0 a (by simpa [Ty.WFBVars, Ty.WFBVarCtx] using hWF_s)
    have hWF₂ : Ty.WFBVars (t₂.openTv 0 a) :=
      Ty.WFBVars_openTv t₂ 0 a (by simpa [Ty.WFBVars, Ty.WFBVarCtx] using hWF_t)
    intro δ hδ hD k γ hm v htd
    simp only [TyDenote] at htd ⊢
    intro R hR
    -- Interpret the binder by `R` on both sides, i.e. open with `a ↦ R`.
    have hδ' : (δ.set a R).WK := TyEnvSem.set_WK hδ a R (hka ▸ hR)
    have h₁ := (TyDenote.push_openTv_iff δ a R t₁ hfresh.1 k γ v).mp (htd R hR)
    exact (TyDenote.push_openTv_iff δ a R t₂ hfresh.2 k γ v).mpr (ih hWF₁ hWF₂ hδ' hD hm h₁)
  | prod hfst hfresh hsnd ih_fst ih_snd =>
    rename_i Γ' s₁ t₁ s₂ t₂ x
    obtain ⟨hWF_s1, hWF_st1⟩ := hWF_s
    obtain ⟨hWF_s2, hWF_t2⟩ := hWF_t
    have hopt_eq : s₁.optBase = s₂.optBase := Subtyp.optBase_eq hfst
    have hWF_t2' : Ty.WFBVarCtx [s₁.optBase] t₂ := hopt_eq ▸ hWF_t2
    simp only [List.mem_append, not_or] at hfresh
    obtain ⟨⟨⟨⟨⟨hx_Γdom, hx_Γfv⟩, hx_s1fv⟩, hx_s2fv⟩, hx_t1fv⟩, hx_t2fv⟩ := hfresh
    intro δ hδ hD k γ hm v htd
    simp only [TyDenote] at htd ⊢
    obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := htd
    refine ⟨v₁, v₂, rfl, ih_fst hWF_s1 hWF_s2 hδ hD hm hv₁, ?_⟩
    have hWF_t1x : Ty.WFBVars (t₁.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₁ [] s₁.optBase x hWF_st1
    have hWF_t2x : Ty.WFBVars (t₂.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₂ [] s₁.optBase x hWF_t2'
    have hm_ext : ModelsEnv κ (γ.write x v₁) ((x, s₁) :: Γ') :=
      ModelsEnv.extendBy_cons hδ hm s₁ x v₁ hx_Γdom hx_Γfv hx_s1fv hv₁
    exact (TyDenote.push_iff κ δ k t₂ x γ v₁ v₂ hx_t2fv).mpr
      (ih_snd hWF_t1x hWF_t2x hδ hD hm_ext ((TyDenote.push_iff κ δ k t₁ x γ v₁ v₂ hx_t1fv).mp hv₂))
  | data h₁ h₂ ih₁ ih₂ =>
    rename_i Γ' C n args₁ args₂
    intro δ hδ hD k γ hm v htd
    simp only [TyDenote] at htd ⊢
    obtain ⟨hlc, hcl, her, j, w, P, rfl, hP, hpay⟩ := htd
    refine ⟨hlc, hcl, her, j, w, P, rfl, hP, fun i hi => ?_⟩
    rw [hD] at hP ⊢
    have hw := hpay i hi
    rw [hD] at hw
    obtain ⟨d, hd, -, -, hvar⟩ := DEnv.wfB_payload_all hde hP
    have hvl : ∀ l, de.var C l = (d.variances[l]?).getD .inv := fun l => by simp [DEnv.var, hd]
    have hrel := RelVar.ofFn d.variances
      (fun l (j' : Fin (i+1)) w' => TyDenote κ δ j'.val (args₁ l) γ w')
      (fun l (j' : Fin (i+1)) w' => TyDenote κ δ j'.val (args₂ l) γ w')
      (fun l => by
        rw [← hvl]
        apply Variance.Rel_upto
        · intro hv j' w' h
          exact ih₁ l hv (hWF_s l) (hWF_t l) hδ hD hm h
        · intro hv j' w' h
          exact ih₂ l hv (hWF_t l) (hWF_s l) hδ hD hm h)
    have := (TyDenote.var_mono (κ := κ) hde i P d.variances .pos [] _ _ (fun _ => SemTy.top)
      REnv.empty w (by simpa using hvar) hrel).1 (by simp)
    simpa using this (by simpa using hw)

/-! ## T2 — Fundamental Lemma -/

/-- Any function value applies to any argument. -/
private theorem Val.apply_isSome {f : Val} (hf : ∃ body, f = .clos body ∨ f = .fclos body)
    (va : Val) : ∃ body, Val.apply f va = some body := by
  obtain ⟨b, rfl | rfl⟩ := hf <;> exact ⟨_, rfl⟩

/-- Selfification is sound: a variable's value is in its selfified type. -/
private theorem TyDenote.self {κ : KEnv} {δ : TyEnvSem} {k : Nat} {γ : REnv} {x : EVar} {t : Ty}
    (hv : TyDenote κ δ k t γ (γ.map x)) : TyDenote κ δ k (self x t) γ (γ.map x) := by
  cases t with
  | refine b r =>
    have hsing : ∀ b' : Base, Refinement.interp κ
        (.fmla (.eq b' (.bvar b' 0) (.fvar b' x))) (γ.push (γ.map x)) := by
      intro b'
      simp [Refinement.interp, Formula.interp, Term.interp, REnv.getBV, REnv.get, REnv.lookup]
    simp only [TyDenote] at hv
    cases b with
    | tfvar a =>
      rcases a with ⟨n, _ | _⟩
      · change TyDenote κ δ k (.refine _ (.fmla (.eq _ (.bvar _ 0) (.fvar _ x)))) γ (γ.map x)
        simp only [TyDenote]; exact ⟨hv.1, hsing _⟩
      · change TyDenote κ δ k (.refine _ r) γ (γ.map x)
        simp only [TyDenote]; exact hv
    | _ =>
      change TyDenote κ δ k (.refine _ (.fmla (.eq _ (.bvar _ 0) (.fvar _ x)))) γ (γ.map x)
      simp only [TyDenote]; exact ⟨hv.1, hsing _⟩
  | arrow _ _ | «forall» _ _ | prod _ _ | data _ _ _ => simpa only [self] using hv

theorem hastype_fundamental {de κ Γ e t} (hde : de.wfB = true) (h : Hastype de κ Γ e t) :
    ∀ {δ}, δ.WK → δ.denv = de → ∀ {k γ}, EnvCloses κ δ k Γ γ →
      ExpDenote κ δ k t γ (Exp.substEnv γ e).erase := by
  induction h with
  | unreach hent _ =>
      intro δ hδ hD k γ hE
      exact (hent γ (hE.toModelsEnv hδ)).elim
  | var hlk _ =>
      rename_i Γ x t hwf
      intro δ hδ hD k γ hE
      have hv := EnvCloses.lookup hE hlk
      rw [Exp.substEnv_fvar, Exp.erase_of_typeFree _ (TyDenote.erased hv)]
      exact ExpDenote.of_val (TyDenote.self hv)
  | int_const =>
      rename_i n
      intro δ hδ hD k γ _
      show ExpDenote _ _ _ _ _ (Val.iconst n).toExp
      apply ExpDenote.of_val
      simp only [prim, TyDenote, BaseDen]
      exact ⟨⟨n, rfl⟩, by simp [Refinement.interp, Formula.interp, Term.interp]⟩
  | bool_const =>
      rename_i b
      intro δ hδ hD k γ _
      show ExpDenote _ _ _ _ _ (Val.bconst b).toExp
      apply ExpDenote.of_val
      simp only [primBool, TyDenote, BaseDen]
      exact ⟨⟨b, rfl⟩, by simp [Refinement.interp, Formula.interp, Term.interp]⟩
  | ann _ _ ih =>
      intro δ hδ hD k γ hE
      rw [Exp.substEnv_ann]
      exact ih hδ hD hE
  | sub hhs hsub hwf_t ih =>
      intro δ hδ hD k γ hE
      obtain ⟨o, hev, hres⟩ := ih hδ hD hE
      exact ⟨o, hev, fun v m ho =>
        subtyp_sound hde hsub hhs.wf_bvars hwf_t hδ hD (EnvCloses.toModelsEnv hδ hE) (hres v m ho)⟩
  | add_var hlk₁ hlk₂ =>
      rename_i x y r₁ r₂
      intro δ hδ hD k γ hE
      have hv₁ := EnvCloses.lookup hE hlk₁
      simp only [TyDenote, BaseDen] at hv₁; obtain ⟨⟨n₁, hγx⟩, _⟩ := hv₁
      have hv₂ := EnvCloses.lookup hE hlk₂
      simp only [TyDenote, BaseDen] at hv₂; obtain ⟨⟨n₂, hγy⟩, _⟩ := hv₂
      have hx : Exp.substEnv γ (.fvar x) = .iconst n₁ := by simp [Exp.substEnv_fvar, hγx]
      have hy : Exp.substEnv γ (.fvar y) = .iconst n₂ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.val (.iconst (n₁ + n₂)) k, ?_, fun v m ho => ?_⟩
      · rw [Exp.substEnv_add, hx, hy]; simp only [Exp.erase]; exact Eval.add Eval.iconst Eval.iconst
      · injection ho with h₁ h₂; subst h₁ h₂
        simp only [TyDenote, BaseDen]
        refine ⟨⟨n₁ + n₂, rfl⟩, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx, hγy]
  | leq_var hlk₁ hlk₂ =>
      rename_i x y r₁ r₂
      intro δ hδ hD k γ hE
      have hv₁ := EnvCloses.lookup hE hlk₁
      simp only [TyDenote, BaseDen] at hv₁; obtain ⟨⟨n₁, hγx⟩, _⟩ := hv₁
      have hv₂ := EnvCloses.lookup hE hlk₂
      simp only [TyDenote, BaseDen] at hv₂; obtain ⟨⟨n₂, hγy⟩, _⟩ := hv₂
      have hx : Exp.substEnv γ (.fvar x) = .iconst n₁ := by simp [Exp.substEnv_fvar, hγx]
      have hy : Exp.substEnv γ (.fvar y) = .iconst n₂ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.val (.bconst (decide (n₁ ≤ n₂))) k, ?_, fun v m ho => ?_⟩
      · rw [Exp.substEnv_leq, hx, hy]; simp only [Exp.erase]; exact Eval.leq Eval.iconst Eval.iconst
      · injection ho with h₁ h₂; subst h₁ h₂
        simp only [TyDenote, BaseDen]
        refine ⟨⟨_, rfl⟩, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp,
                   REnv.getBV, REnv.get, REnv.lookup, REnv.push, Val.proj,
                   hγx, hγy, List.getElem?_cons_zero, Option.getD_some]
        constructor
        · intro h; exact decide_eq_true_iff.mp h
        · intro h; exact decide_eq_true_iff.mpr h
  | not_var hlk =>
      rename_i x r
      intro δ hδ hD k γ hE
      have hv₁ := EnvCloses.lookup hE hlk
      simp only [TyDenote, BaseDen] at hv₁; obtain ⟨⟨b, hγx⟩, _⟩ := hv₁
      have hx : Exp.substEnv γ (.fvar x) = .bconst b := by simp [Exp.substEnv_fvar, hγx]
      refine ⟨.val (.bconst (!b)) k, ?_, fun v m ho => ?_⟩
      · rw [Exp.substEnv_not, hx]; simp only [Exp.erase]; exact Eval.not_ Eval.bconst
      · injection ho with h₁ h₂; subst h₁ h₂
        simp only [TyDenote, BaseDen]
        refine ⟨⟨_, rfl⟩, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx]
  | and_var hlkx hlky =>
      rename_i x y rx ry
      intro δ hδ hD k γ hE
      have hvx := EnvCloses.lookup hE hlkx
      simp only [TyDenote, BaseDen] at hvx; obtain ⟨⟨bx, hγx⟩, _⟩ := hvx
      have hvy := EnvCloses.lookup hE hlky
      simp only [TyDenote, BaseDen] at hvy; obtain ⟨⟨by_, hγy⟩, _⟩ := hvy
      have hxx : Exp.substEnv γ (.fvar x) = .bconst bx := by simp [Exp.substEnv_fvar, hγx]
      have hyy : Exp.substEnv γ (.fvar y) = .bconst by_ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.val (.bconst (bx && by_)) k, ?_, fun v m ho => ?_⟩
      · rw [Exp.substEnv_and, hxx, hyy]; simp only [Exp.erase]; exact Eval.and_ Eval.bconst Eval.bconst
      · injection ho with h₁ h₂; subst h₁ h₂
        simp only [TyDenote, BaseDen]
        refine ⟨⟨_, rfl⟩, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx, hγy]
  | lam hwf_arr hfresh ih =>
      rename_i Γ' body s₁ s₂ x ih_fund
      intro δ hδ hD k γ hE
      rw [Exp.substEnv_lam]
      have hbody_dom : ∀ z ∈ body.fv, z ∈ TEnv.dom Γ' := by
        intro z hz
        obtain ⟨t', hzΓ⟩ := (Hastype.lam hwf_arr hfresh ih).fv_subset z (by simpa [Exp.fv] using hz)
        exact mem_TEnv_dom hzΓ
      show ExpDenote _ _ _ _ _ (Val.clos (Exp.substEnv γ body).erase).toExp
      apply ExpDenote.of_val
      simp only [TyDenote]
      refine ⟨⟨_, Or.inl rfl⟩, ?_, ?_, ?_, ?_⟩
      · simp only [Val.lc]
        exact Exp.lc_at_erase _ 1 (Exp.substEnv_lc_at γ body 1
          (fun z hz => EnvCloses.mem_lc hE (hbody_dom z hz))
          (Hastype.lam hwf_arr hfresh ih).lc_at)
      · simp only [Val.closed, Val.fv]
        have h := Exp.substEnv_fv_nil γ body
          (fun z hz => EnvCloses.mem_closed hE (hbody_dom z hz))
        exact List.eq_nil_iff_forall_not_mem.mpr fun z hz =>
          by simpa [h] using Exp.fv_erase_subset _ z hz
      · exact Exp.typeFree_erase _
      · intro j hj va htd_va
        simp [List.mem_append, not_or] at hfresh
        obtain ⟨hxΓ, hxΓfv, hxbody, hxs₁, hxs₂⟩ := hfresh
        have hEx : EnvCloses κ δ j ((x, s₁) :: Γ') (γ.write x va) :=
          EnvCloses.extend (hE.mono (Nat.le_of_lt hj)) x s₁ va hxΓ hxΓfv
            (TyDenote.extendBy_fresh x va hxs₁ htd_va)
        obtain ⟨o, hev, hres⟩ := ih_fund hδ hD hEx
        rw [Exp.substEnv_write_openVar body γ va x 0 hxbody
              (fun w hw => EnvCloses.mem_lc hE (hbody_dom w hw)),
            Exp.erase_openExp, Exp.erase_of_typeFree _ (TyDenote.erased htd_va)] at hev
        exact ⟨_, o, rfl, hev, fun vr m ho _ =>
          (TyDenote.push_iff κ δ m s₂ x γ va vr hxs₂).mpr (hres vr m ho)⟩
  | app h_fn h_arg hyfv ih_fn ih_arg =>
      rename_i e₁ y s t
      intro δ hδ hD k γ hE
      rw [Exp.substEnv_app]
      simp only [Exp.erase]
      obtain ⟨o₁, hev₁, hres₁⟩ := ih_fn hδ hD hE
      cases o₁ with
      | timeout => exact ⟨.timeout, Eval.app_to₁ hev₁, fun _ _ ho => by cases ho⟩
      | val f n₁ =>
        have htd_f := hres₁ f n₁ rfl
        have hn₁ := Eval.fuel_le hev₁
        -- The argument is the variable `y`: it evaluates to `γ.map y` for free.
        have hy_er : Val.Erased (γ.map y) := by
          obtain ⟨t', hyΓ⟩ := h_arg.fv_subset y (by simp [Exp.fv])
          exact EnvCloses.mem_erased hE (mem_TEnv_dom hyΓ)
        obtain ⟨o₂, hev₂, hres₂⟩ := ih_arg hδ hD (hE.mono hn₁)
        rw [Exp.substEnv_fvar, Exp.erase_of_typeFree _ hy_er] at hev₂
        rw [Exp.substEnv_fvar, Exp.erase_of_typeFree _ hy_er]
        have ho₂ := Eval.toExp_inv hev₂
        subst ho₂
        have htd_va := hres₂ _ _ rfl
        simp only [TyDenote] at htd_f
        obtain ⟨hfun, _, _, _, hLR⟩ := htd_f
        cases n₁ with
        | zero =>
          obtain ⟨body, hap⟩ := Val.apply_isSome hfun (γ.map y)
          exact ⟨.timeout, Eval.app_tick hev₁ (Eval.toExp 0 _) hap, fun _ _ ho => by cases ho⟩
        | succ m₁ =>
          obtain ⟨body, o, hap, hev, hres⟩ :=
            hLR m₁ (Nat.lt_succ_self _) (γ.map y) (TyDenote.mono (Nat.le_succ _) htd_va)
          refine ⟨o, Eval.app hev₁ (Eval.toExp _ _) hap hev, fun vr m ho => ?_⟩
          have h := (TyDenote.push_iff κ δ m t y γ (γ.map y) vr hyfv).mp
            (hres vr m ho (by have := Eval.fuel_le (ho ▸ hev); omega))
          rwa [REnv.write_idem] at h
  | @letin Γ' e₁ e₂ s' t' x hwfbv hht xf hhto ih₁ ih₂ =>
      intro δ hδ hD k γ hE
      rw [Exp.substEnv_letin]
      simp only [Exp.erase]
      obtain ⟨o₁, hev₁, hres₁⟩ := ih₁ hδ hD hE
      cases o₁ with
      | timeout => exact ⟨.timeout, Eval.letin_to hev₁, fun _ _ ho => by cases ho⟩
      | val v₁ n₁ =>
        have htd₁ := hres₁ v₁ n₁ rfl
        have he₂_dom : ∀ w ∈ e₂.fv, w ∈ TEnv.dom Γ' := by
          intro w hw
          obtain ⟨t'', hwΓ⟩ := (Hastype.letin hwfbv hht xf hhto).fv_subset w
            (by simp only [Exp.fv]; exact List.mem_append_right _ hw)
          exact mem_TEnv_dom hwΓ
        simp [List.mem_append, not_or] at xf
        obtain ⟨hxΓ, hxΓfv, hxbody, hxs, hxt⟩ := xf
        have hEx : EnvCloses κ δ n₁ ((x, s') :: Γ') (γ.write x v₁) :=
          EnvCloses.extend (hE.mono (Eval.fuel_le hev₁)) x s' v₁ hxΓ hxΓfv
            (TyDenote.extendBy_fresh x v₁ hxs htd₁)
        obtain ⟨o, hev, hres⟩ := ih₂ hδ hD hEx
        rw [Exp.substEnv_write_openVar e₂ γ v₁ x 0 hxbody
              (fun w hw => EnvCloses.mem_lc hE (he₂_dom w hw)),
            Exp.erase_openExp, Exp.erase_of_typeFree _ (TyDenote.erased htd₁)] at hev
        exact ⟨o, Eval.letin hev₁ hev, fun vr m ho =>
          TyDenote.of_extendBy_fresh x v₁ hxt (hres vr m ho)⟩
  | ite hlk hfresh _ h₁ h₂ ih_e₁ ih_e₂ =>
      rename_i Γ x y e₁ e₂ r t _
      intro δ hδ hD k γ hE
      have htd_x := EnvCloses.lookup hE hlk
      simp only [TyDenote, BaseDen] at htd_x
      obtain ⟨⟨bx, hγx⟩, _⟩ := htd_x
      have hxfv : Exp.substEnv γ (.fvar x) = .bconst bx := by simp [Exp.substEnv_fvar, hγx]
      have hy_e₁ : y ∉ e₁.fv := fun hm => hfresh (by simp [hm])
      have hy_e₂ : y ∉ e₂.fv := fun hm => hfresh (by simp [hm])
      let r_true : Refinement :=
        .fmla (.eq .bool (.fvar .bool x) (.const .bool true))
      let r_false : Refinement :=
        .fmla (.eq .bool (.fvar .bool x) (.const .bool false))
      have hy_dom : y ∉ TEnv.dom Γ := fun hm => hfresh (by simp [hm])
      have hy_tyfv : y ∉ TEnv.tyFv Γ := fun hm => hfresh (by simp [hm])
      have hy_tfv : y ∉ t.fv := fun hm => hfresh (by simp [hm])
      have hyx : y ≠ x := fun he => hfresh (by simp [he])
      rw [Exp.substEnv_ite, hxfv]
      simp only [Exp.erase]
      cases bx with
      | true =>
        have htd_guard : TyDenote κ δ k (.refine .bool r_true)
            (γ.write y (.bconst (γ.bools y)))
            (.bconst (γ.bools y)) := by
          simp only [TyDenote, BaseDen, r_true]
          refine ⟨⟨_, rfl⟩, ?_⟩
          simp [Refinement.interp, Formula.interp, Term.interp,
                REnv.get, REnv.lookup, hyx, hγx]
        have hE₁ : EnvCloses κ δ k ((y, .refine .bool r_true) :: Γ)
            (γ.write y (.bconst (γ.bools y))) :=
          EnvCloses.extend hE y (.refine .bool r_true) (.bconst (γ.bools y))
            hy_dom hy_tyfv htd_guard
        obtain ⟨o, hev, hres⟩ := ih_e₁ hδ hD hE₁
        rw [Exp.substEnv_write_fresh e₁ γ y (.bconst (γ.bools y)) hy_e₁] at hev
        exact ⟨o, Eval.ite_t Eval.bconst hev, fun vr m ho =>
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y)) hy_tfv (hres vr m ho)⟩
      | false =>
        have htd_guard : TyDenote κ δ k (.refine .bool r_false)
            (γ.write y (.bconst (γ.bools y)))
            (.bconst (γ.bools y)) := by
          simp only [TyDenote, BaseDen, r_false]
          refine ⟨⟨_, rfl⟩, ?_⟩
          simp [Refinement.interp, Formula.interp, Term.interp,
                REnv.get, REnv.lookup, hyx, hγx]
        have hE₂ : EnvCloses κ δ k ((y, .refine .bool r_false) :: Γ)
            (γ.write y (.bconst (γ.bools y))) :=
          EnvCloses.extend hE y (.refine .bool r_false) (.bconst (γ.bools y))
            hy_dom hy_tyfv htd_guard
        obtain ⟨o, hev, hres⟩ := ih_e₂ hδ hD hE₂
        rw [Exp.substEnv_write_fresh e₂ γ y (.bconst (γ.bools y)) hy_e₂] at hev
        exact ⟨o, Eval.ite_f Eval.bconst hev, fun vr m ho =>
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y)) hy_tfv (hres vr m ho)⟩
  | @fix Γ' e s t f x as has hwf hf hx hbody ih =>
      intro δ₀ hδ₀ hD₀ k γ hE₀
      rw [Exp.substEnv_fix]
      simp only [Exp.erase]
      have hfix := Hastype.fix as has hwf hf hx hbody
      have he_dom : ∀ w ∈ e.fv, w ∈ TEnv.dom Γ' := by
        intro w hw
        obtain ⟨t', hwΓ⟩ := hfix.fv_subset w (by simpa [Exp.fv] using hw)
        exact mem_TEnv_dom hwΓ
      have he_lc : e.lc_at 2 := by simpa [Exp.lc_at] using hfix.lc_at
      simp only [List.mem_append, List.mem_singleton, not_or] at hf hx
      obtain ⟨⟨⟨⟨hfΓ, hfΓfv⟩, hfe⟩, hfs⟩, hft⟩ := hf
      obtain ⟨⟨⟨⟨⟨hxΓ, hxΓfv⟩, hxe⟩, hxs⟩, hxt⟩, hxf⟩ := hx
      -- The recursive closure is in the relation at every index, and under every
      -- re-interpretation of the generalized type variables `as`, by induction
      -- on the index: a recursive call happens after a β-step, i.e. at `j < k`
      -- (and may use another interpretation of `as` — polymorphic recursion).
      have key : ∀ k, EnvCloses κ δ₀ k Γ' γ → ∀ δ, TyEnvSem.Reinterp as δ₀ δ →
          TyDenote κ δ k (.arrow s t) γ (.fclos (Exp.substEnv γ e).erase) := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k IH =>
        intro hE₀ δ hδδ
        have hE : EnvCloses κ δ k Γ' γ := EnvCloses.reinterp has hδδ hE₀
        have hδ : δ.WK := hδδ.WK hδ₀
        have hD : δ.denv = _ := hδδ.denv.trans hD₀
        simp only [TyDenote]
        refine ⟨⟨_, Or.inr rfl⟩, ?_, ?_, ?_, ?_⟩
        · simp only [Val.lc]
          exact Exp.lc_at_erase _ 2 (Exp.substEnv_lc_at γ e 2
            (fun z hz => EnvCloses.mem_lc hE (he_dom z hz)) he_lc)
        · simp only [Val.closed, Val.fv]
          have h := Exp.substEnv_fv_nil γ e
            (fun z hz => EnvCloses.mem_closed hE (he_dom z hz))
          exact List.eq_nil_iff_forall_not_mem.mpr fun z hz =>
            by simpa [h] using Exp.fv_erase_subset _ z hz
        · exact Exp.typeFree_erase _
        · intro j hj va htd_va
          have hEj := hE.mono (Nat.le_of_lt hj)
          have hE₀j := hE₀.mono (Nat.le_of_lt hj)
          let vf : Val := .fclos (Exp.substEnv γ e).erase
          have htd_f : TyDenote κ δ j (Ty.gen as (.arrow s t)) γ vf :=
            TyDenote.gen_intro as δ (fun δ' h' => IH j hj hE₀j δ' (hδδ.trans h'))
          have hf_st : f ∉ (Ty.gen as (.arrow s t)).fv := by simp [Ty.fv, hfs, hft]
          have hx_st : x ∉ (Ty.gen as (.arrow s t)).fv := by simp [Ty.fv, hxs, hxt]
          have hE₁ : EnvCloses κ δ j ((f, Ty.gen as (.arrow s t)) :: Γ') (γ.write f vf) :=
            EnvCloses.extend hEj f _ vf hfΓ hfΓfv (TyDenote.extendBy_fresh f vf hf_st htd_f)
          have hE₂ : EnvCloses κ δ j ((x, s) :: (f, Ty.gen as (.arrow s t)) :: Γ')
              ((γ.write f vf).write x va) :=
            EnvCloses.extend hE₁ x s va
              (by simp only [TEnv.dom, List.mem_cons, not_or]; exact ⟨hxf, hxΓ⟩)
              (by simp only [TEnv.tyFv, List.mem_append, not_or]; exact ⟨hx_st, hxΓfv⟩)
              (TyDenote.extendBy_fresh x va hxs (TyDenote.extendBy_fresh f vf hfs htd_va))
          obtain ⟨o, hev, hres⟩ := ih hδ hD hE₂
          -- Close the opened body: first the argument `x`, then the self-name `f`.
          have hγ₁ : ∀ w ∈ (e.openVar 1 f).fv, Val.lc ((γ.write f vf).map w) := by
            intro w hw
            rcases Exp.fv_openVar hw with hw | rfl
            · have hwf : f ≠ w := fun h => hfe (h ▸ hw)
              rw [REnv.write_other γ f vf hwf]
              exact EnvCloses.mem_lc hE (he_dom w hw)
            · rw [REnv.write_self]
              exact TyDenote.lc htd_f
          have hx_open : x ∉ (e.openVar 1 f).fv := fun hm => by
            rcases Exp.fv_openVar hm with h | h
            · exact hxe h
            · exact hxf h
          rw [Exp.substEnv_write_openVar _ _ va x 0 hx_open hγ₁,
              Exp.substEnv_write_openVar e γ vf f 1 hfe
                (fun w hw => EnvCloses.mem_lc hE (he_dom w hw)),
              Exp.erase_openExp, Exp.erase_openExp,
              Exp.erase_of_typeFree _ (TyDenote.erased htd_va),
              Exp.erase_of_typeFree _ (TyDenote.erased htd_f)] at hev
          refine ⟨_, o, rfl, hev, fun vr m ho _ => ?_⟩
          have h := (TyDenote.push_iff κ δ m t x (γ.write f vf) va vr hxt).mpr (hres vr m ho)
          rw [REnv.push_write_comm] at h
          exact TyDenote.of_extendBy_fresh f vf hft h
      exact ⟨_, Eval.fix, fun v m ho => by
        injection ho with h₁ h₂; subst h₁ h₂; exact key k hE₀ δ₀ (.refl δ₀)⟩

  | @tabs Γ' kd e t a hwf hka hfresh hbody ih =>
      intro δ hδ hD k γ hE
      rw [Exp.substEnv_tabs]
      simp only [Exp.erase]
      simp only [List.mem_append, not_or] at hfresh
      obtain ⟨⟨haΓ, hae⟩, hat⟩ := hfresh
      have hfix := Hastype.tabs hwf hka (by simp [haΓ, hae, hat]) hbody
      have he_er : ∀ z ∈ e.fv, Val.Erased (γ.map z) := by
        intro z hz
        obtain ⟨t', hzΓ⟩ := hfix.fv_subset z (by simpa [Exp.fv] using hz)
        exact EnvCloses.mem_erased hE (mem_TEnv_dom hzΓ)
      -- The body, opened with `a`, evaluates like the body itself (types erased).
      have hbody_eq : (Exp.substEnv γ (e.openTv 0 a)).erase = (Exp.substEnv γ e).erase := by
        rw [Exp.substEnv_openTv γ 0 a e he_er, Exp.erase_openTv]
      have hden : ∀ R : SemTy, R.Fits kd →
          ExpDenote κ (δ.set a R) k (t.openTv 0 a) γ (Exp.substEnv γ e).erase := by
        intro R hR
        have := ih (TyEnvSem.set_WK hδ a R (hka ▸ hR)) hD (EnvCloses.set_fresh haΓ hE)
        rwa [hbody_eq] at this
      -- One outcome for every interpretation of α (evaluation is deterministic).
      obtain ⟨o, hev, _⟩ := hden SemTy.ints (SemTy.ints_fits kd)
      refine ⟨o, hev, fun v m ho => ?_⟩
      simp only [TyDenote]
      intro R hR
      obtain ⟨o', hev', hres'⟩ := hden R hR
      cases Eval.det hev hev'
      exact (TyDenote.push_openTv_iff δ a R t hat m γ v).mpr (hres' v m ho)
  | @tapp Γ' e kd t s hhe hk hw₁ hw₂ hw₃ ih =>
      intro δ hδ hD k γ hE
      rw [Exp.substEnv_tapp]
      simp only [Exp.erase]
      obtain ⟨o, hev, hres⟩ := ih hδ hD hE
      refine ⟨o, hev, fun v m ho => ?_⟩
      have h := hres v m ho
      simp only [TyDenote] at h
      -- Instantiate the type variable by the instance's own denotation.
      let R : SemTy := ⟨fun j w => TyDenote κ δ j s γ w,
        fun hjk h => TyDenote.mono hjk h, fun h => TyDenote.wf h⟩
      have hRfits : R.Fits kd := by
        cases kd with
        | star => trivial
        | B =>
          have hsB : s.kindOf = .B := by rcases hk with h | h; exact h; cases h
          obtain ⟨b', r', rfl, hb'⟩ := Ty.kindOf_B hsB
          rcases hb' with rfl | rfl | ⟨n, rfl⟩
          · exact ⟨.int, Or.inl rfl, fun j w hw => by
              simp only [R, TyDenote, BaseDen] at hw; obtain ⟨⟨n, rfl⟩, _⟩ := hw; rfl⟩
          · exact ⟨.bool, Or.inr rfl, fun j w hw => by
              simp only [R, TyDenote, BaseDen] at hw; obtain ⟨⟨c, rfl⟩, _⟩ := hw; rfl⟩
          · obtain ⟨b0, hb0, hall⟩ := hδ (n, .B)
            exact ⟨b0, hb0, fun j w hw => by
              simp only [R, TyDenote, BaseDen] at hw; exact hall j w hw.1⟩
      have hwt : t.wfB [kd] [] = true := by simpa [Ty.wfB] using hw₁
      have key := TyDenote.instTy_iff (κ := κ) s kd hw₂ hk δ γ R
        t [] δ.bv [kd] [] m γ v (fun _ _ _ => Iff.rfl) hwt rfl rfl rfl (fun _ i hi => by simp at hi)
      simp only [List.nil_append, List.length_nil] at key
      exact key.mp (by simpa [TyEnvSem.push] using h R hRfits)
  | pair hwf hhx hxt hh₂ ih₁ ih₂ =>
      rename_i Γ' x e₂ s t
      intro δ hδ hD k γ hE
      have hx_er : Val.Erased (γ.map x) := by
        obtain ⟨t', hxΓ⟩ := hhx.fv_subset x (by simp [Exp.fv])
        exact EnvCloses.mem_erased hE (mem_TEnv_dom hxΓ)
      simp only [Exp.substEnv, Exp.erase]
      rw [Exp.erase_of_typeFree _ hx_er]
      obtain ⟨o₁, hev₁, hres₁⟩ := ih₁ hδ hD hE
      rw [Exp.substEnv_fvar, Exp.erase_of_typeFree _ hx_er] at hev₁
      have ho₁ := Eval.toExp_inv hev₁
      subst ho₁
      have hv₁ := hres₁ _ _ rfl
      obtain ⟨o₂, hev₂, hres₂⟩ := ih₂ hδ hD hE
      cases o₂ with
      | timeout => exact ⟨.timeout, Eval.pair_to₂ (Eval.toExp k _) hev₂, fun _ _ ho => by cases ho⟩
      | val v₂ m =>
        refine ⟨.val (.pair (γ.map x) v₂) m, Eval.pair (Eval.toExp k _) hev₂, fun v m' ho => ?_⟩
        injection ho with h₁ h₂; subst h₁ h₂
        have hm := Eval.fuel_le hev₂
        simp only [TyDenote]
        refine ⟨γ.map x, v₂, rfl, TyDenote.mono hm hv₁, ?_⟩
        exact (TyDenote.push_iff κ δ m t x γ (γ.map x) v₂ hxt).mpr
          (by rw [REnv.write_idem]; exact hres₂ v₂ m rfl)
  | @split Γ' e body s t t' x y hwf hhe hx hy hbody ih ihb =>
      intro δ hδ hD k γ hE
      simp only [Exp.substEnv, Exp.erase]
      have hspl := Hastype.split hwf hhe hx hy hbody
      have hb_dom : ∀ w ∈ body.fv, w ∈ TEnv.dom Γ' := by
        intro w hw
        obtain ⟨t'', hwΓ⟩ := hspl.fv_subset w
          (by simp only [Exp.fv]; exact List.mem_append_right _ hw)
        exact mem_TEnv_dom hwΓ
      simp only [List.mem_append, List.mem_singleton, not_or] at hx hy
      obtain ⟨⟨⟨⟨⟨hxΓ, hxΓfv⟩, hxb⟩, hxs⟩, hxt⟩, hxt'⟩ := hx
      obtain ⟨⟨⟨⟨⟨⟨hyΓ, hyΓfv⟩, hyb⟩, hys⟩, hyt⟩, hyt'⟩, hyx⟩ := hy
      obtain ⟨o₁, hev₁, hres₁⟩ := ih hδ hD hE
      cases o₁ with
      | timeout => exact ⟨.timeout, Eval.split_to hev₁, fun _ _ ho => by cases ho⟩
      | val v n₁ =>
        have hv := hres₁ v n₁ rfl
        simp only [TyDenote] at hv
        obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := hv
        have hn₁ := Eval.fuel_le hev₁
        have hE₁ : EnvCloses κ δ n₁ ((x, s) :: Γ') (γ.write x v₁) :=
          EnvCloses.extend (hE.mono hn₁) x s v₁ hxΓ hxΓfv (TyDenote.extendBy_fresh x v₁ hxs hv₁)
        have hv₂' : TyDenote κ δ n₁ (t.openVar 0 x) (γ.write x v₁) v₂ :=
          (TyDenote.push_iff κ δ n₁ t x γ v₁ v₂ hxt).mp hv₂
        have hy_open : y ∉ (t.openVar 0 x).fv := fun hm => by
          rcases Ty.fv_openVar t hm with h | h
          · exact hyt h
          · exact hyx h
        have hE₂ : EnvCloses κ δ n₁ ((y, t.openVar 0 x) :: (x, s) :: Γ')
            ((γ.write x v₁).write y v₂) :=
          EnvCloses.extend hE₁ y _ v₂
            (by simp only [TEnv.dom, List.mem_cons, not_or]; exact ⟨hyx, hyΓ⟩)
            (by simp only [TEnv.tyFv, List.mem_append, not_or]; exact ⟨hys, hyΓfv⟩)
            (TyDenote.extendBy_fresh y v₂ hy_open hv₂')
        obtain ⟨o, hev, hres⟩ := ihb hδ hD hE₂
        have hγ₁ : ∀ w ∈ (body.openVar 1 x).fv, Val.lc ((γ.write x v₁).map w) := by
          intro w hw
          rcases Exp.fv_openVar hw with hw | rfl
          · have hxw : x ≠ w := fun h => hxb (h ▸ hw)
            rw [REnv.write_other γ x v₁ hxw]
            exact EnvCloses.mem_lc hE (hb_dom w hw)
          · rw [REnv.write_self]; exact TyDenote.lc hv₁
        have hy_open_b : y ∉ (body.openVar 1 x).fv := fun hm => by
          rcases Exp.fv_openVar hm with h | h
          · exact hyb h
          · exact hyx h
        rw [Exp.substEnv_write_openVar _ _ v₂ y 0 hy_open_b hγ₁,
            Exp.substEnv_write_openVar body γ v₁ x 1 hxb
              (fun w hw => EnvCloses.mem_lc hE (hb_dom w hw)),
            Exp.erase_openExp, Exp.erase_openExp,
            Exp.erase_of_typeFree _ (TyDenote.erased hv₂),
            Exp.erase_of_typeFree _ (TyDenote.erased hv₁)] at hev
        refine ⟨o, Eval.split hev₁ hev, fun vr m ho => ?_⟩
        exact TyDenote.of_extendBy_fresh x v₁ hxt'
          (TyDenote.of_extendBy_fresh y v₂ hyt' (hres vr m ho))
  | @ctor Γ' C j τs e P hP hok hhe ih =>
      intro δ hδ hD k γ hE
      simp only [Exp.substEnv, Exp.erase]
      obtain ⟨o, hev, hres⟩ := ih hδ hD hE
      cases o with
      | timeout => exact ⟨.timeout, Eval.ctor_to hev, fun _ _ ho => by cases ho⟩
      | val w m =>
        refine ⟨.val (.ctor C j w) m, Eval.ctor hev, fun v m' ho => ?_⟩
        injection ho with h₁ h₂; subst h₁ h₂
        have hw := hres w m rfl
        obtain ⟨hlc, hcl, her⟩ := TyDenote.wf hw
        obtain ⟨ks, hks, hargs, hokP⟩ := DEnv.instOK_payload_ok hok hP
        obtain ⟨hPfv, hPftv⟩ := DEnv.wfB_payload hde hP
        have hτs : List.ofFn (fun l : Fin τs.length => τs[l]) = τs := List.ofFn_getElem
        simp only [Ty.dataL, TyDenote]
        refine ⟨by simpa [Val.lc, Val.toExp, Exp.lc_at] using hlc,
          by simpa [Val.closed, Val.fv, Val.toExp, Exp.fv] using hcl,
          by simpa [Val.Erased, Val.toExp, Exp.TypeFree] using her,
          j, w, P, rfl, hD ▸ hP, fun i hi => ?_⟩
        have hw' : TyDenote κ δ i (Ty.instTys (List.ofFn fun l : Fin τs.length => τs[l]) P) γ w := by
          rw [hτs]; exact TyDenote.mono (Nat.le_of_lt hi) hw
        exact (TyDenote.instTys_bridge δ γ i (fun l : Fin τs.length => τs[l]) ks P hks
          (fun l => hargs l.val l.isLt) (by rw [hτs]; exact hokP) hPfv hPftv w).mp hw'
  | @case Γ' e C n args m alts t zs hwf hhe hm hok hz hzP hcks ih ihs =>
      intro δ hδ hD k γ hE
      simp only [Exp.substEnv, Exp.erase]
      have hcs := Hastype.case zs hwf hhe hm hok hz hzP hcks
      obtain ⟨o₀, hev₀, hres₀⟩ := ih hδ hD hE
      cases o₀ with
      | timeout => exact ⟨.timeout, Eval.case_to hev₀, fun _ _ ho => by cases ho⟩
      | val v n₁ =>
        have hv := hres₀ v n₁ rfl
        simp only [TyDenote] at hv
        obtain ⟨_, _, _, j, w, P, rfl, hP, hpay⟩ := hv
        rw [hD] at hP
        have hj : j < m := DEnv.payload?_lt hm hP
        cases n₁ with
        | zero => exact ⟨.timeout, Eval.case_tick hj hev₀, fun _ _ ho => by cases ho⟩
        | succ i =>
          obtain ⟨ks, hks, hargs, hokP⟩ := DEnv.instOK_payload_ok hok hP
          obtain ⟨hPfv, hPftv⟩ := DEnv.wfB_payload hde hP
          have hw : TyDenote κ δ i (Ty.instTys (List.ofFn args) P) γ w :=
            (TyDenote.instTys_bridge δ γ i args ks P (by simpa using hks)
              (fun l => by
                obtain ⟨kd, h1, h2, h3⟩ := hargs l.val (by simp)
                exact ⟨kd, h1, by simpa using h2, by simpa using h3⟩)
              hokP hPfv hPftv w).mpr (hpay i (Nat.lt_succ_self i))
          have hzj := hz ⟨j, hj⟩
          simp only [List.mem_append, not_or] at hzj
          obtain ⟨⟨⟨hzΓ, hzΓfv⟩, hzalt⟩, hzt⟩ := hzj
          have hzP' := hzP ⟨j, hj⟩ P hP
          have hn := Eval.fuel_le hev₀
          have hE' : EnvCloses κ δ i ((zs ⟨j, hj⟩, Ty.instTys (List.ofFn args) P) :: Γ')
              (γ.write (zs ⟨j, hj⟩) w) :=
            EnvCloses.extend (hE.mono (by omega)) _ _ w hzΓ hzΓfv
              (TyDenote.extendBy_fresh _ w hzP' hw)
          obtain ⟨o, hev, hres⟩ := ihs ⟨j, hj⟩ P hP hδ hD hE'
          have halt_dom : ∀ w' ∈ (alts ⟨j, hj⟩).fv, w' ∈ TEnv.dom Γ' := by
            intro w' hw'
            obtain ⟨t'', hwΓ⟩ := hcs.fv_subset w' (by
              simp only [Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
              exact Or.inr ⟨⟨j, hj⟩, hw'⟩)
            exact mem_TEnv_dom hwΓ
          rw [Exp.substEnv_write_openVar _ γ w _ 0 hzalt
                (fun w' hw' => EnvCloses.mem_lc hE (halt_dom w' hw')),
              Exp.erase_openExp, Exp.erase_of_typeFree _ (TyDenote.erased hw)] at hev
          exact ⟨o, Eval.case hj hev₀ hev, fun vr m' ho =>
            TyDenote.of_extendBy_fresh _ w hzt (hres vr m' ho)⟩

/-! ## T3 — Closed-term type safety (corollary of T2) -/

namespace STLC

/-- The operational semantics of a program: run its type erasure. (Types never
    influence evaluation; erasing them first is what makes type abstraction and
    application, and the opening of type binders during checking, invisible at
    runtime.) -/
def Run (n : Nat) (e : Exp) (o : Outcome) : Prop := Eval n e.erase o

end STLC

/-- A well-typed closed program never gets stuck: for every fuel budget `n` it
    either times out or returns a value, and every returned value (with `m`
    fuel left) is in its type's denotation at index `m`. -/
theorem type_safety {de : DEnv} {κ : KEnv} {e : Exp} {t : Ty} (hde : de.wfB = true)
    (h : Hastype de κ [] e t) :
    ∀ n, ∃ o, Run n e o ∧
      ∀ v m, o = .val v m → TyDenote κ (TyEnvSem.empty de) m t REnv.empty v := by
  intro n
  have hfv : e.fv = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun z hz => by
      obtain ⟨t', ht'⟩ := h.fv_subset z hz; simp at ht'
  have hden := hastype_fundamental hde h (TyEnvSem.empty_WK de) rfl (k := n) (γ := REnv.empty)
    (by simp [EnvCloses])
  rw [Exp.substEnv_closed REnv.empty e hfv] at hden
  exact hden

/-! ## T4 — End-to-end VCGen safety

  VCGen soundness composes with the logical-relations fundamental lemma to give
  end-to-end (fuel-indexed, partial) refinement type safety for `topVC`. -/

theorem vcgen_safety {κ : KEnv} {e : Exp} {t : Ty} {de : DEnv} (hde : de.wfB = true)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t de) :
    ∀ n, ∃ o, Run n e o ∧
      ∀ v m, o = .val v m → TyDenote κ (TyEnvSem.empty de) m t REnv.empty v :=
  type_safety hde (topVC_decl_sound κ e t hE ht h)

/-- Progress: a program accepted by VCGen never gets stuck. -/
theorem vcgen_no_stuck {κ : KEnv} {e : Exp} {t : Ty} {de : DEnv} (hde : de.wfB = true)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t de) :
    ∀ n, ∃ o, Run n e o := fun n =>
  let ⟨o, hev, _⟩ := vcgen_safety hde hE ht h n
  ⟨o, hev⟩

/-- Partial correctness at base type: if a program accepted by VCGen terminates
    (under any fuel budget), its value has the result sort and satisfies the
    result refinement. -/
theorem vcgen_partial_correct {κ : KEnv} {e : Exp} {b : Base} {r : Refinement} {de : DEnv}
    (hde : de.wfB = true)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars (.refine b r)) (h : topVC κ [] e (.refine b r) de)
    {n m : Nat} {v : Val} (hev : Run n e (.val v m)) :
    BaseDen (TyEnvSem.empty de) m b v ∧ Refinement.interp κ r (REnv.empty.push v) := by
  obtain ⟨o, hev', hres⟩ := vcgen_safety hde hE ht h n
  cases Eval.det hev hev'
  simpa only [TyDenote] using hres v m rfl
