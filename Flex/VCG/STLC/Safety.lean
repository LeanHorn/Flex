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
      refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
      rw [REnv.push_write_comm]
      exact (iht δ m (γ.push va') vr x va hx.2).mp (hres vr m ho)
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ := hLR j hj va' ((ihs δ j γ va' x va hx.1).mp htd)
      refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
      have h := hres vr m ho
      rw [REnv.push_write_comm] at h
      exact (iht δ m (γ.push va') vr x va hx.2).mpr h
  | «forall» kd t ih =>
    intro δ k γ v x va hx
    simp only [Ty.fv] at hx
    simp only [TyDenote]
    exact forall_congr' (fun R => forall_congr' (fun _ => ih (δ.push R) k γ v x va hx))

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
      refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
      have h := hres vr m ho
      rw [REnv.push_insertBV_comm] at h
      rw [REnv.push_write_comm]
      exact (iht (s'.optBase :: ρ) δ m x (γ.push va') va vr
        (Nat.succ_le_succ hlen) hxf.2).mp h
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ :=
        hLR j hj va' ((ihs ρ δ j x γ va va' hlen hxf.1).mp htd)
      refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
      have h := hres vr m ho
      rw [REnv.push_write_comm] at h
      rw [REnv.push_insertBV_comm]
      exact (iht (s'.optBase :: ρ) δ m x (γ.push va') va vr
        (Nat.succ_le_succ hlen) hxf.2).mpr h
  | «forall» kd t ih =>
    intro ρ δ k x γ va v hlen hxf
    simp only [Ty.fv] at hxf
    simp only [Ty.openVar, TyDenote]
    exact forall_congr' (fun R => forall_congr' (fun _ => ih ρ (δ.push R) k x γ va v hlen hxf))

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

/-! ## T1 — Subtyping is semantic inclusion of denotations -/

private theorem Subtyp.optBase_eq {κ Γ s t} (h : Subtyp κ Γ s t) : s.optBase = t.optBase := by
  cases h with
  | refine _ _ => rfl
  | arrow => simp [Ty.optBase]
  | «forall» => rfl

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

theorem subtyp_sound {κ Γ s t} (hsub : Subtyp κ Γ s t)
    (hWF_s : Ty.WFBVars s) (hWF_t : Ty.WFBVars t) :
    ∀ {δ}, δ.WK → ∀ {k γ}, ModelsEnv κ γ Γ → ∀ {v},
      TyDenote κ δ k s γ v → TyDenote κ δ k t γ v := by
  induction hsub with
  | refine hfresh hent =>
      rename_i b r₁ r₂ x
      intro δ hδ k γ hΓ v hs
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
    intro δ hδ k γ hm v htd
    simp only [TyDenote] at htd ⊢
    obtain ⟨hfun, hlc, hcl, her, hLR⟩ := htd
    refine ⟨hfun, hlc, hcl, her, fun j hj va htd_va => ?_⟩
    -- Domain conversion (contravariant): s₂ <: s₁
    have htd_va_s1 : TyDenote κ δ j s₁ γ va := ih_hdom hWF_s2 hWF_s1 hδ hm htd_va
    obtain ⟨body, o, hap, hev, hres⟩ := hLR j hj va htd_va_s1
    refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
    have hWF_t1x : Ty.WFBVars (t₁.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₁ [] s₂.optBase x hWF_st1'
    have hWF_t2x : Ty.WFBVars (t₂.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₂ [] s₂.optBase x hWF_t2
    have htd_vr_t1 := (TyDenote.push_iff κ δ m t₁ x γ va vr hx_t1fv).mp (hres vr m ho)
    have hm_ext : ModelsEnv κ (γ.write x va) ((x, s₂) :: Γ') :=
      ModelsEnv.extendBy_cons hδ hm s₂ x va hx_Γdom hx_Γfv hx_s2fv htd_va
    exact (TyDenote.push_iff κ δ m t₂ x γ va vr hx_t2fv).mpr
      (ih_hcodom hWF_t1x hWF_t2x hδ hm_ext htd_vr_t1)
  | «forall» hka hfresh hbody ih =>
    rename_i Γ' kd t₁ t₂ a
    simp only [List.mem_append, not_or] at hfresh
    have hWF₁ : Ty.WFBVars (t₁.openTv 0 a) :=
      Ty.WFBVars_openTv t₁ 0 a (by simpa [Ty.WFBVars, Ty.WFBVarCtx] using hWF_s)
    have hWF₂ : Ty.WFBVars (t₂.openTv 0 a) :=
      Ty.WFBVars_openTv t₂ 0 a (by simpa [Ty.WFBVars, Ty.WFBVarCtx] using hWF_t)
    intro δ hδ k γ hm v htd
    simp only [TyDenote] at htd ⊢
    intro R hR
    -- Interpret the binder by `R` on both sides, i.e. open with `a ↦ R`.
    have hδ' : (δ.set a R).WK := TyEnvSem.set_WK hδ a R (hka ▸ hR)
    have h₁ := (TyDenote.push_openTv_iff δ a R t₁ hfresh.1 k γ v).mp (htd R hR)
    exact (TyDenote.push_openTv_iff δ a R t₂ hfresh.2 k γ v).mpr (ih hWF₁ hWF₂ hδ' hm h₁)

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
  | arrow _ _ => simpa only [self] using hv
  | «forall» _ _ => simpa only [self] using hv

theorem hastype_fundamental {κ Γ e t} (h : Hastype κ Γ e t) :
    ∀ {δ}, δ.WK → ∀ {k γ}, EnvCloses κ δ k Γ γ →
      ExpDenote κ δ k t γ (Exp.substEnv γ e).erase := by
  induction h with
  | unreach hent _ =>
      intro δ hδ k γ hE
      exact (hent γ (hE.toModelsEnv hδ)).elim
  | var hlk _ =>
      rename_i Γ x t hwf
      intro δ hδ k γ hE
      have hv := EnvCloses.lookup hE hlk
      rw [Exp.substEnv_fvar, Exp.erase_of_typeFree _ (TyDenote.erased hv)]
      exact ExpDenote.of_val (TyDenote.self hv)
  | int_const =>
      rename_i n
      intro δ hδ k γ _
      show ExpDenote _ _ _ _ _ (Val.iconst n).toExp
      apply ExpDenote.of_val
      simp only [prim, TyDenote, BaseDen]
      exact ⟨⟨n, rfl⟩, by simp [Refinement.interp, Formula.interp, Term.interp]⟩
  | bool_const =>
      rename_i b
      intro δ hδ k γ _
      show ExpDenote _ _ _ _ _ (Val.bconst b).toExp
      apply ExpDenote.of_val
      simp only [primBool, TyDenote, BaseDen]
      exact ⟨⟨b, rfl⟩, by simp [Refinement.interp, Formula.interp, Term.interp]⟩
  | ann _ _ ih =>
      intro δ hδ k γ hE
      rw [Exp.substEnv_ann]
      exact ih hδ hE
  | sub hhs hsub hwf_t ih =>
      intro δ hδ k γ hE
      obtain ⟨o, hev, hres⟩ := ih hδ hE
      exact ⟨o, hev, fun v m ho =>
        subtyp_sound hsub hhs.wf_bvars hwf_t hδ (EnvCloses.toModelsEnv hδ hE) (hres v m ho)⟩
  | add_var hlk₁ hlk₂ =>
      rename_i x y r₁ r₂
      intro δ hδ k γ hE
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
      intro δ hδ k γ hE
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
      intro δ hδ k γ hE
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
      intro δ hδ k γ hE
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
      intro δ hδ k γ hE
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
        obtain ⟨o, hev, hres⟩ := ih_fund hδ hEx
        rw [Exp.substEnv_write_openVar body γ va x 0 hxbody
              (fun w hw => EnvCloses.mem_lc hE (hbody_dom w hw)),
            Exp.erase_openExp, Exp.erase_of_typeFree _ (TyDenote.erased htd_va)] at hev
        exact ⟨_, o, rfl, hev, fun vr m ho =>
          (TyDenote.push_iff κ δ m s₂ x γ va vr hxs₂).mpr (hres vr m ho)⟩
  | app h_fn h_arg hyfv ih_fn ih_arg =>
      rename_i e₁ y s t
      intro δ hδ k γ hE
      rw [Exp.substEnv_app]
      simp only [Exp.erase]
      obtain ⟨o₁, hev₁, hres₁⟩ := ih_fn hδ hE
      cases o₁ with
      | timeout => exact ⟨.timeout, Eval.app_to₁ hev₁, fun _ _ ho => by cases ho⟩
      | val f n₁ =>
        have htd_f := hres₁ f n₁ rfl
        have hn₁ := Eval.fuel_le hev₁
        -- The argument is the variable `y`: it evaluates to `γ.map y` for free.
        have hy_er : Val.Erased (γ.map y) := by
          obtain ⟨t', hyΓ⟩ := h_arg.fv_subset y (by simp [Exp.fv])
          exact EnvCloses.mem_erased hE (mem_TEnv_dom hyΓ)
        obtain ⟨o₂, hev₂, hres₂⟩ := ih_arg hδ (hE.mono hn₁)
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
          have h := (TyDenote.push_iff κ δ m t y γ (γ.map y) vr hyfv).mp (hres vr m ho)
          rwa [REnv.write_idem] at h
  | @letin Γ' e₁ e₂ s' t' x hwfbv hht xf hhto ih₁ ih₂ =>
      intro δ hδ k γ hE
      rw [Exp.substEnv_letin]
      simp only [Exp.erase]
      obtain ⟨o₁, hev₁, hres₁⟩ := ih₁ hδ hE
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
        obtain ⟨o, hev, hres⟩ := ih₂ hδ hEx
        rw [Exp.substEnv_write_openVar e₂ γ v₁ x 0 hxbody
              (fun w hw => EnvCloses.mem_lc hE (he₂_dom w hw)),
            Exp.erase_openExp, Exp.erase_of_typeFree _ (TyDenote.erased htd₁)] at hev
        exact ⟨o, Eval.letin hev₁ hev, fun vr m ho =>
          TyDenote.of_extendBy_fresh x v₁ hxt (hres vr m ho)⟩
  | ite hlk hfresh _ h₁ h₂ ih_e₁ ih_e₂ =>
      rename_i Γ x y e₁ e₂ r t _
      intro δ hδ k γ hE
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
        obtain ⟨o, hev, hres⟩ := ih_e₁ hδ hE₁
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
        obtain ⟨o, hev, hres⟩ := ih_e₂ hδ hE₂
        rw [Exp.substEnv_write_fresh e₂ γ y (.bconst (γ.bools y)) hy_e₂] at hev
        exact ⟨o, Eval.ite_f Eval.bconst hev, fun vr m ho =>
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y)) hy_tfv (hres vr m ho)⟩
  | @fix Γ' e s t f x as has hwf hf hx hbody ih =>
      intro δ₀ hδ₀ k γ hE₀
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
          obtain ⟨o, hev, hres⟩ := ih hδ hE₂
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
          refine ⟨_, o, rfl, hev, fun vr m ho => ?_⟩
          have h := (TyDenote.push_iff κ δ m t x (γ.write f vf) va vr hxt).mpr (hres vr m ho)
          rw [REnv.push_write_comm] at h
          exact TyDenote.of_extendBy_fresh f vf hft h
      exact ⟨_, Eval.fix, fun v m ho => by
        injection ho with h₁ h₂; subst h₁ h₂; exact key k hE₀ δ₀ (.refl δ₀)⟩

  | @tabs Γ' kd e t a hwf hka hfresh hbody ih =>
      intro δ hδ k γ hE
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
        have := ih (TyEnvSem.set_WK hδ a R (hka ▸ hR)) (EnvCloses.set_fresh haΓ hE)
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
      intro δ hδ k γ hE
      rw [Exp.substEnv_tapp]
      simp only [Exp.erase]
      obtain ⟨o, hev, hres⟩ := ih hδ hE
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
      have key := TyDenote.instTy_iff (κ := κ) s kd hw₂ hk δ γ R (fun _ _ => Iff.rfl)
        t [] δ.bv [kd] [] m γ v hwt rfl rfl rfl (fun _ i hi => by simp at hi)
      simp only [List.nil_append, List.length_nil] at key
      exact key.mp (by simpa [TyEnvSem.push] using h R hRfits)

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
theorem type_safety {κ : KEnv} {e : Exp} {t : Ty} (h : Hastype κ [] e t) :
    ∀ n, ∃ o, Run n e o ∧
      ∀ v m, o = .val v m → TyDenote κ TyEnvSem.empty m t REnv.empty v := by
  intro n
  have hfv : e.fv = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun z hz => by
      obtain ⟨t', ht'⟩ := h.fv_subset z hz; simp at ht'
  have hden := hastype_fundamental h TyEnvSem.empty_WK (k := n) (γ := REnv.empty)
    (by simp [EnvCloses])
  rw [Exp.substEnv_closed REnv.empty e hfv] at hden
  exact hden

/-! ## T4 — End-to-end VCGen safety

  VCGen soundness composes with the logical-relations fundamental lemma to give
  end-to-end (fuel-indexed, partial) refinement type safety for `topVC`. -/

theorem vcgen_safety {κ : KEnv} {e : Exp} {t : Ty}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t) :
    ∀ n, ∃ o, Run n e o ∧
      ∀ v m, o = .val v m → TyDenote κ TyEnvSem.empty m t REnv.empty v :=
  type_safety (topVC_decl_sound κ e t hE ht h)

/-- Progress: a program accepted by VCGen never gets stuck. -/
theorem vcgen_no_stuck {κ : KEnv} {e : Exp} {t : Ty}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t) :
    ∀ n, ∃ o, Run n e o := fun n =>
  let ⟨o, hev, _⟩ := vcgen_safety hE ht h n
  ⟨o, hev⟩

/-- Partial correctness at base type: if a program accepted by VCGen terminates
    (under any fuel budget), its value has the result sort and satisfies the
    result refinement. -/
theorem vcgen_partial_correct {κ : KEnv} {e : Exp} {b : Base} {r : Refinement}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars (.refine b r)) (h : topVC κ [] e (.refine b r))
    {n m : Nat} {v : Val} (hev : Run n e (.val v m)) :
    BaseDen TyEnvSem.empty m b v ∧ Refinement.interp κ r (REnv.empty.push v) := by
  obtain ⟨o, hev', hres⟩ := vcgen_safety hE ht h n
  cases Eval.det hev hev'
  simpa only [TyDenote] using hres v m rfl
