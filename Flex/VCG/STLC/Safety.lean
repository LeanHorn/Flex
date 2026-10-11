import Flex.VCG.STLC.Semantics
import Flex.VCG.STLC.Declarative
import Flex.VCG.STLC.Soundness
import Flex.VCG.STLC.Model

open STLC

/-! # Refinement Type Safety for STLC (LN + deep refinements + κ + recursion)

  With general recursion (`Exp.fix`) programs may diverge, so safety is stated
  *partially* but *fuel-indexed*, against the semantics `Eval` of
  `Semantics.lean`: for every fuel budget, a well-typed closed program either
  times out or returns a value in its type's denotation — and it never gets
  stuck. The logical relation (`TyDenote`, `Model.lean`) is step-indexed by the
  remaining fuel.

    (T1) `subtyp_sound`         — Subtyping is semantic inclusion of denotations.
    (T2) `hastype_fundamental`  — Well-typed terms are in the expression relation
                                   at every index, under a closing substitution.
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

end STLC


/-- Every value in the denotation is closed (no free names). -/
theorem TyDenote.closed {κ : KEnv} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ k t γ v) : Val.closed v := by
  cases t with
  | refine b r =>
    cases b with
    | int  =>
      simp only [TyDenote] at h
      obtain ⟨n, hvn, _⟩ := h
      subst hvn; simp [Val.closed, Val.fv]
    | bool =>
      simp only [TyDenote] at h
      obtain ⟨bv, hvb, _⟩ := h
      subst hvb; simp [Val.closed, Val.fv]
  | arrow s t =>
    simp only [TyDenote] at h
    exact h.2.2.1

/-- Every value in the denotation is locally closed (Val.lc). -/
theorem TyDenote.lc {κ : KEnv} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ k t γ v) : Val.lc v := by
  cases t with
  | refine b r =>
    cases b with
    | int  => simp only [TyDenote] at h; obtain ⟨n, hvn, _⟩ := h; subst hvn; exact True.intro
    | bool => simp only [TyDenote] at h; obtain ⟨b, hvb, _⟩ := h; subst hvb; exact True.intro
  | arrow s t =>
    simp only [TyDenote] at h; exact h.2.1

/-- A value in the denotation is in the expression relation (it evaluates to
    itself without consuming fuel). -/
theorem ExpDenote.of_val {κ : KEnv} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (h : TyDenote κ k t γ v) : ExpDenote κ k t γ v.toExp :=
  ⟨_, Eval.toExp k v, fun v' m ho => by
    injection ho with h₁ h₂; subst h₁ h₂; exact h⟩

/-! ## Closing environment

  `EnvCloses κ k Γ γ` says: `γ` assigns each Γ-binding a value in that binding's
  logical relation at index `k`. Duplicate keys are tolerated (head-shadowed
  entries from `ite`'s context). -/
def EnvCloses : KEnv → Nat → TEnv → REnv → Prop
  | _, _, [],          _ => True
  | κ, k, (x, t) :: Γ, γ => TyDenote κ k t γ (γ.map x) ∧ EnvCloses κ k Γ γ

/-- Downward closure of `EnvCloses`. -/
theorem EnvCloses.mono {κ : KEnv} {j k : Nat} (hjk : j ≤ k) :
    ∀ {Γ γ}, EnvCloses κ k Γ γ → EnvCloses κ j Γ γ
  | [],          _, _ => trivial
  | (_, _) :: _, _, ⟨h, hΓ⟩ => ⟨TyDenote.mono hjk h, EnvCloses.mono hjk hΓ⟩

/-- `EnvCloses` projects to `ModelsEnv` (at any index: refinement bindings
    ignore the step index). -/
theorem EnvCloses.toModelsEnv :
    ∀ {κ k Γ γ}, EnvCloses κ k Γ γ → ModelsEnv κ γ Γ
  | _, _, [],                    _, _ => by simp [ModelsEnv]
  | _, _, (x, .refine b r) :: Γ, γ, h => by
      obtain ⟨hv, hΓ⟩ := h
      have hrest := EnvCloses.toModelsEnv hΓ
      cases b with
      | int  =>
        simp only [TyDenote] at hv
        obtain ⟨n, hmap, hp⟩ := hv
        refine ⟨⟨n, hmap⟩, ?_, hrest⟩
        simp only [REnv.lookup, hmap]; exact hp
      | bool =>
        simp only [TyDenote] at hv
        obtain ⟨bv, hmap, hp⟩ := hv
        refine ⟨⟨bv, hmap⟩, ?_, hrest⟩
        simp only [REnv.lookup, hmap]; exact hp
  | _, _, (_, .arrow _ _) :: _,  _, h => by
      obtain ⟨_, hΓ⟩ := h
      simp only [ModelsEnv]; exact EnvCloses.toModelsEnv hΓ

/-- Looking up `x` in Γ recovers its denotation at the γ-slot value `γ.map x`. -/
theorem EnvCloses.lookup :
    ∀ {κ k Γ γ}, EnvCloses κ k Γ γ → ∀ {x t}, Γ.lookup x = some t →
      TyDenote κ k t γ (γ.map x)
  | _, _, [],          _, _, _, _, hl => by simp [List.lookup] at hl
  | _, _, (y, s) :: Γ, γ, h, x, t, hl => by
      obtain ⟨hv, hΓ⟩ := h
      by_cases heq : x = y
      · subst heq
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hl
        exact hl ▸ hv
      · have hne_beq : (x == y) = false := by rw [beq_eq_false_iff_ne]; exact heq
        simp only [List.lookup, hne_beq] at hl
        exact EnvCloses.lookup hΓ hl

/-- Every Γ-bound name maps to a locally-closed value under `EnvCloses`. -/
theorem EnvCloses.mem_lc :
    ∀ {κ k Γ γ}, EnvCloses κ k Γ γ → ∀ {x}, x ∈ TEnv.dom Γ → Val.lc (γ.map x)
  | _, _, [],          _, _, _, hx => by simp [TEnv.dom] at hx
  | _, _, (y, t) :: Γ, γ, h, x, hx => by
      obtain ⟨hv, hΓ⟩ := h
      simp only [TEnv.dom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact TyDenote.lc hv
      · exact EnvCloses.mem_lc hΓ hx

/-- Every Γ-bound name maps to a closed value (no free names) under `EnvCloses`. -/
theorem EnvCloses.mem_closed :
    ∀ {κ k Γ γ}, EnvCloses κ k Γ γ → ∀ {x}, x ∈ TEnv.dom Γ → Val.closed (γ.map x)
  | _, _, [],          _, _, _, hx => by simp [TEnv.dom] at hx
  | _, _, (y, t) :: Γ, γ, h, x, hx => by
      obtain ⟨hv, hΓ⟩ := h
      simp only [TEnv.dom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact TyDenote.closed hv
      · exact EnvCloses.mem_closed hΓ hx

/-! ## extendBy commutativity and extendBy_fresh -/

/-- Writing a fresh `x` (`x ∉ r.fv`) does not change `Refinement.interp` under
    *any* `γ`. -/
private theorem Refinement.interp_write_fresh {κ : KEnv} (r : Refinement)
    (x : EVar) (va : Val) (γ : REnv)
    (hx : x ∉ Refinement.fv r) :
    Refinement.interp κ r γ ↔ Refinement.interp κ r (γ.write x va) := by
  cases r with
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

/-- `TyDenote` is invariant under writing a name `x` not free in `t`. -/
theorem TyDenote.extendBy_fresh_iff {κ : KEnv} (t : Ty) :
    ∀ (k : Nat) (γ : REnv) (v : Val) (x : EVar) (va : Val), x ∉ t.fv →
      (TyDenote κ k t γ v ↔ TyDenote κ k t (γ.write x va) v) := by
  induction t with
  | refine b r =>
    intro k γ v x va hx
    have hx' : x ∉ Refinement.fv r := by simpa [Ty.fv] using hx
    simp only [TyDenote]
    exact exists_congr (fun _ => and_congr_right (fun _ =>
      Refinement.interp_write_fresh r x va _ hx'))
  | arrow s' t' ihs iht =>
    intro k γ v x va hx
    simp only [Ty.fv, List.mem_append, not_or] at hx
    simp only [TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ => ?_)))
    constructor
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ := hLR j hj va' ((ihs j γ va' x va hx.1).mpr htd)
      refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
      rw [REnv.push_write_comm]
      exact (iht m (γ.push va') vr x va hx.2).mp (hres vr m ho)
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ := hLR j hj va' ((ihs j γ va' x va hx.1).mp htd)
      refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
      have h := hres vr m ho
      rw [REnv.push_write_comm] at h
      exact (iht m (γ.push va') vr x va hx.2).mpr h

/-- TyDenote is monotone under writing at a variable `x` not free in `t`. -/
theorem TyDenote.extendBy_fresh {κ : KEnv} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (x : EVar) (va : Val) (hx : x ∉ t.fv) (h : TyDenote κ k t γ v) :
    TyDenote κ k t (γ.write x va) v :=
  (TyDenote.extendBy_fresh_iff t k γ v x va hx).mp h

/-- Reverse direction: TyDenote under a fresh write implies TyDenote at γ. -/
theorem TyDenote.of_extendBy_fresh {κ : KEnv} {k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (x : EVar) (va : Val) (hx : x ∉ t.fv) (h : TyDenote κ k t (γ.write x va) v) :
    TyDenote κ k t γ v :=
  (TyDenote.extendBy_fresh_iff t k γ v x va hx).mpr h

/-! ## push ↔ openVar bridge

  `TyDenote` threads arrow-binder values through the de Bruijn stack (`γ.push
  va`). Relating that to `openVar` uses the premise-free model bridge
  `Refinement.interp_openBVar` (Substitution.lean). -/

/-- Master bridge (push ↔ openVar): interpreting `t` with `va` inserted at de
    Bruijn level `ρ.length` equals interpreting `t.openVar` with `x ↦ va` written
    into the name map. -/
private theorem TyDenote.insertBV_openVar_aux {κ : KEnv} (t : Ty) :
    ∀ (ρ : List (Option Base)) (k : Nat) (x : EVar) (γ : REnv) (va : Val) (v : Val),
      ρ.length ≤ γ.bv.length → x ∉ t.fv →
      (TyDenote κ k t (γ.insertBV ρ.length va) v ↔
       TyDenote κ k (t.openVar ρ.length x) (γ.write x va) v) := by
  induction t with
  | refine b r =>
    intro ρ k x γ va v hlen hxf
    simp only [Ty.fv] at hxf
    simp only [Ty.openVar, TyDenote]
    refine exists_congr (fun ν => and_congr_right (fun _ => ?_))
    rw [REnv.push_insertBV_comm, REnv.write_push]
    exact (Refinement.interp_openBVar κ r (γ.push (Val.inj b ν)) x va (ρ.length + 1)
      (by simpa using Nat.succ_le_succ hlen) hxf).symm
  | arrow s' t' ihs iht =>
    intro ρ k x γ va v hlen hxf
    simp only [Ty.fv, List.mem_append, not_or] at hxf
    simp only [Ty.openVar, TyDenote]
    refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ => ?_)))
    constructor
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ :=
        hLR j hj va' ((ihs ρ j x γ va va' hlen hxf.1).mpr htd)
      refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
      have h := hres vr m ho
      rw [REnv.push_insertBV_comm] at h
      rw [REnv.push_write_comm]
      exact (iht (s'.optBase :: ρ) m x (γ.push va') va vr
        (Nat.succ_le_succ hlen) hxf.2).mp h
    · intro hLR j hj va' htd
      obtain ⟨body, o, hap, hev, hres⟩ :=
        hLR j hj va' ((ihs ρ j x γ va va' hlen hxf.1).mp htd)
      refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
      have h := hres vr m ho
      rw [REnv.push_write_comm] at h
      rw [REnv.push_insertBV_comm]
      exact (iht (s'.optBase :: ρ) m x (γ.push va') va vr
        (Nat.succ_le_succ hlen) hxf.2).mpr h

/-- `push va` in TyDenote corresponds to `openVar 0 x` with `γ.write x va`, when
    `x` is fresh for `t`. -/
theorem TyDenote.push_iff (κ : KEnv) (k : Nat) (t : Ty) (x : EVar) (γ : REnv)
    (va : Val) (v : Val) (hx_fv : x ∉ t.fv) :
    TyDenote κ k t (γ.push va) v ↔
    TyDenote κ k (t.openVar 0 x) (γ.write x va) v := by
  have h := TyDenote.insertBV_openVar_aux (κ := κ) t [] k x γ va v (by simp) hx_fv
  simpa using h

/-- `EnvCloses` is preserved when extending `γ` at a name `x` fresh for Γ. -/
theorem EnvCloses.extendBy_fresh {κ k Γ γ} (hE : EnvCloses κ k Γ γ)
    (x : EVar) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ) :
    EnvCloses κ k Γ (γ.write x va) := by
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
theorem EnvCloses.extend {κ k Γ γ} (hE : EnvCloses κ k Γ γ)
    (x : EVar) (s : Ty) (va : Val) (hx_dom : x ∉ TEnv.dom Γ)
    (hx_fv : x ∉ TEnv.tyFv Γ)
    (htd : TyDenote κ k s (γ.write x va) va) :
    EnvCloses κ k ((x, s) :: Γ) (γ.write x va) := by
  refine ⟨?_, EnvCloses.extendBy_fresh hE x va hx_dom hx_fv⟩
  rw [show (γ.write x va).map x = va by exact REnv.write_self γ x va]
  exact htd

/-! ## T1 — Subtyping is semantic inclusion of denotations -/

private theorem Subtyp.optBase_eq {κ Γ s t} (h : Subtyp κ Γ s t) : s.optBase = t.optBase := by
  cases h with
  | refine _ _ => rfl
  | arrow => simp [Ty.optBase]

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
    cases t with
    | arrow s' t' =>
      simp only [ModelsEnv] at hm ⊢
      exact ih hm hz_dom.2 hz_fv.2
    | refine b r =>
      simp only [ModelsEnv] at hm ⊢
      obtain ⟨hHB, hhead, htail⟩ := hm
      have hzy : z ≠ y := hz_dom.1
      have hmap : (γ.write z va).map y = γ.map y :=
        REnv.write_other γ z va hzy
      refine ⟨?_, ?_, ih htail hz_dom.2 hz_fv.2⟩
      · cases b with
        | int  => obtain ⟨n, hn⟩ := hHB; exact ⟨n, by rw [hmap]; exact hn⟩
        | bool => obtain ⟨c, hc⟩ := hHB; exact ⟨c, by rw [hmap]; exact hc⟩
      · have hz_rfv : z ∉ Refinement.fv r := by simpa [Ty.fv] using hz_fv.1
        rw [show (γ.write z va).lookup y = γ.lookup y from hmap]
        exact (Refinement.interp_write_fresh r z va _ hz_rfv).mp hhead

/-- Build ModelsEnv after prepending a fresh binding (z, s₂). -/
private theorem ModelsEnv.extendBy_cons {κ : KEnv} {Γ : TEnv} {γ : REnv} {k : Nat}
    (hm : ModelsEnv κ γ Γ) (s₂ : Ty) (z : EVar) (va : Val)
    (hz_dom : z ∉ TEnv.dom Γ)
    (hz_fv : z ∉ TEnv.tyFv Γ)
    (hz_s2fv : z ∉ s₂.fv)
    (htd_va : TyDenote κ k s₂ γ va) :
    ModelsEnv κ (γ.write z va) ((z, s₂) :: Γ) := by
  have htail := ModelsEnv.extendBy_fresh_aux hm z va hz_dom hz_fv
  cases s₂ with
  | arrow s' t' => simp only [ModelsEnv]; exact htail
  | refine b r =>
    simp only [ModelsEnv]
    have hz_rfv : z ∉ Refinement.fv r := by simpa [Ty.fv] using hz_s2fv
    cases b with
    | int =>
      simp only [TyDenote] at htd_va
      obtain ⟨n, hvn, hp⟩ := htd_va; subst hvn
      refine ⟨⟨n, ?_⟩, ?_, htail⟩
      · simp
      · rw [show (γ.write z (Val.inj .int n)).lookup z = Val.inj .int n from REnv.write_self γ z _]
        exact (Refinement.interp_write_fresh r z (Val.inj .int n) _ hz_rfv).mp hp
    | bool =>
      simp only [TyDenote] at htd_va
      obtain ⟨bv, hvb, hp⟩ := htd_va; subst hvb
      refine ⟨⟨bv, ?_⟩, ?_, htail⟩
      · simp
      · rw [show (γ.write z (Val.inj .bool bv)).lookup z = Val.inj .bool bv from REnv.write_self γ z _]
        exact (Refinement.interp_write_fresh r z (Val.inj .bool bv) _ hz_rfv).mp hp

theorem subtyp_sound {κ Γ s t} (hsub : Subtyp κ Γ s t)
    (hWF_s : Ty.WFBVars s) (hWF_t : Ty.WFBVars t) :
    ∀ {k γ}, ModelsEnv κ γ Γ → ∀ {v}, TyDenote κ k s γ v → TyDenote κ k t γ v := by
  induction hsub with
  | refine hfresh hent =>
      rename_i b r₁ r₂ x
      intro k γ hΓ v hs
      simp only [List.mem_append, not_or] at hfresh
      obtain ⟨⟨⟨hx_dom, hx_tyfv⟩, hx_r₁⟩, hx_r₂⟩ := hfresh
      have hx_r₁' : x ∉ (Ty.refine b r₁).fv := by simpa [Ty.fv] using hx_r₁
      cases b with
      | int =>
        simp only [TyDenote] at hs ⊢
        obtain ⟨n, hvn, hp₁⟩ := hs
        have h := hent _ (ModelsEnv.extendBy_cons (k := k) hΓ _ x _ hx_dom hx_tyfv hx_r₁'
          (by simp only [TyDenote]; exact ⟨n, rfl, hp₁⟩))
        exact ⟨n, hvn, (Refinement.interp_openBVar κ r₂ γ x (Val.inj .int n) 0 (Nat.zero_le _) hx_r₂).mp h⟩
      | bool =>
        simp only [TyDenote] at hs ⊢
        obtain ⟨bv, hvb, hp₁⟩ := hs
        have h := hent _ (ModelsEnv.extendBy_cons (k := k) hΓ _ x _ hx_dom hx_tyfv hx_r₁'
          (by simp only [TyDenote]; exact ⟨bv, rfl, hp₁⟩))
        exact ⟨bv, hvb, (Refinement.interp_openBVar κ r₂ γ x (Val.inj .bool bv) 0 (Nat.zero_le _) hx_r₂).mp h⟩
  | arrow hdom hfresh hcodom ih_hdom ih_hcodom =>
    rename_i Γ' s₁ t₁ s₂ t₂ x
    obtain ⟨hWF_s1, hWF_st1⟩ := hWF_s
    obtain ⟨hWF_s2, hWF_t2⟩ := hWF_t
    have hopt_eq : s₂.optBase = s₁.optBase := by grind [Subtyp.optBase_eq]
    have hWF_st1' : Ty.WFBVarCtx [s₂.optBase] t₁ := hopt_eq ▸ hWF_st1
    simp only [List.mem_append, not_or] at hfresh
    obtain ⟨⟨⟨⟨⟨hx_Γdom, hx_Γfv⟩, hx_s1fv⟩, hx_s2fv⟩, hx_t1fv⟩, hx_t2fv⟩ := hfresh
    intro k γ hm v htd
    simp only [TyDenote] at htd ⊢
    obtain ⟨hfun, hlc, hcl, hLR⟩ := htd
    refine ⟨hfun, hlc, hcl, fun j hj va htd_va => ?_⟩
    -- Domain conversion (contravariant): s₂ <: s₁
    have htd_va_s1 : TyDenote κ j s₁ γ va := ih_hdom hWF_s2 hWF_s1 hm htd_va
    obtain ⟨body, o, hap, hev, hres⟩ := hLR j hj va htd_va_s1
    refine ⟨body, o, hap, hev, fun vr m ho => ?_⟩
    have hWF_t1x : Ty.WFBVars (t₁.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₁ [] s₂.optBase x hWF_st1'
    have hWF_t2x : Ty.WFBVars (t₂.openVar 0 x) :=
      Ty.WFBVarCtx_openVar_last t₂ [] s₂.optBase x hWF_t2
    have htd_vr_t1 := (TyDenote.push_iff κ m t₁ x γ va vr hx_t1fv).mp (hres vr m ho)
    have hm_ext : ModelsEnv κ (γ.write x va) ((x, s₂) :: Γ') :=
      ModelsEnv.extendBy_cons hm s₂ x va hx_Γdom hx_Γfv hx_s2fv htd_va
    exact (TyDenote.push_iff κ m t₂ x γ va vr hx_t2fv).mpr
      (ih_hcodom hWF_t1x hWF_t2x hm_ext htd_vr_t1)

/-! ## T2 — Fundamental Lemma -/

/-- Any function value applies to any argument. -/
private theorem Val.apply_isSome {f : Val} (hf : ∃ body, f = .clos body ∨ f = .fclos body)
    (va : Val) : ∃ body, Val.apply f va = some body := by
  obtain ⟨b, rfl | rfl⟩ := hf <;> exact ⟨_, rfl⟩

theorem hastype_fundamental {κ Γ e t} (h : Hastype κ Γ e t) :
    ∀ {k γ}, EnvCloses κ k Γ γ → ExpDenote κ k t γ (Exp.substEnv γ e) := by
  induction h with
  | unreach hent _ =>
      intro k γ hE
      exact (hent γ hE.toModelsEnv).elim
  | var hlk _ =>
      rename_i Γ x t hwf
      intro k γ hE
      have hv := EnvCloses.lookup hE hlk
      rw [Exp.substEnv_fvar]
      apply ExpDenote.of_val
      cases t with
      | refine b r =>
          cases b with
          | int  =>
              simp only [TyDenote] at hv
              obtain ⟨n, hmap, _⟩ := hv
              simp only [self, TyDenote]
              refine ⟨n, hmap, ?_⟩
              simp [Refinement.interp, Formula.interp, Term.interp,
                    REnv.get, REnv.lookup, hmap]
          | bool =>
              simp only [TyDenote] at hv
              obtain ⟨bv, hmap, _⟩ := hv
              simp only [self, TyDenote]
              refine ⟨bv, hmap, ?_⟩
              simp [Refinement.interp, Formula.interp, Term.interp,
                    REnv.get, REnv.lookup, hmap]
      | arrow _ _ =>
          simp only [self]
          exact hv
  | int_const =>
      rename_i n
      intro k γ _
      show ExpDenote _ _ _ _ (Val.iconst n).toExp
      apply ExpDenote.of_val
      simp only [prim, TyDenote]
      refine ⟨n, rfl, ?_⟩
      simp [Refinement.interp, Formula.interp, Term.interp]
  | bool_const =>
      rename_i b
      intro k γ _
      show ExpDenote _ _ _ _ (Val.bconst b).toExp
      apply ExpDenote.of_val
      simp only [primBool, TyDenote]
      refine ⟨b, rfl, ?_⟩
      simp [Refinement.interp, Formula.interp, Term.interp]
  | ann _ _ ih =>
      intro k γ hE
      obtain ⟨o, hev, hres⟩ := ih hE
      exact ⟨o, Eval.ann hev, hres⟩
  | sub hhs hsub hwf_t ih =>
      intro k γ hE
      obtain ⟨o, hev, hres⟩ := ih hE
      exact ⟨o, hev, fun v m ho =>
        subtyp_sound hsub hhs.wf_bvars hwf_t (EnvCloses.toModelsEnv hE) (hres v m ho)⟩
  | add_var hlk₁ hlk₂ =>
      rename_i x y r₁ r₂
      intro k γ hE
      have hv₁ := EnvCloses.lookup hE hlk₁
      simp only [TyDenote] at hv₁; obtain ⟨n₁, hγx, _⟩ := hv₁
      have hv₂ := EnvCloses.lookup hE hlk₂
      simp only [TyDenote] at hv₂; obtain ⟨n₂, hγy, _⟩ := hv₂
      have hx : Exp.substEnv γ (.fvar x) = .iconst n₁ := by simp [Exp.substEnv_fvar, hγx]
      have hy : Exp.substEnv γ (.fvar y) = .iconst n₂ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.val (.iconst (n₁ + n₂)) k, ?_, fun v m ho => ?_⟩
      · rw [Exp.substEnv_add, hx, hy]; exact Eval.add Eval.iconst Eval.iconst
      · injection ho with h₁ h₂; subst h₁ h₂
        simp only [TyDenote]; refine ⟨n₁ + n₂, rfl, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx, hγy]
  | leq_var hlk₁ hlk₂ =>
      rename_i x y r₁ r₂
      intro k γ hE
      have hv₁ := EnvCloses.lookup hE hlk₁
      simp only [TyDenote] at hv₁; obtain ⟨n₁, hγx, _⟩ := hv₁
      have hv₂ := EnvCloses.lookup hE hlk₂
      simp only [TyDenote] at hv₂; obtain ⟨n₂, hγy, _⟩ := hv₂
      have hx : Exp.substEnv γ (.fvar x) = .iconst n₁ := by simp [Exp.substEnv_fvar, hγx]
      have hy : Exp.substEnv γ (.fvar y) = .iconst n₂ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.val (.bconst (decide (n₁ ≤ n₂))) k, ?_, fun v m ho => ?_⟩
      · rw [Exp.substEnv_leq, hx, hy]; exact Eval.leq Eval.iconst Eval.iconst
      · injection ho with h₁ h₂; subst h₁ h₂
        simp only [TyDenote]; refine ⟨decide (n₁ ≤ n₂), rfl, ?_⟩
        simp only [Refinement.interp, Formula.interp, Term.interp,
                   REnv.getBV, REnv.get, REnv.lookup, REnv.push, Val.proj, Val.inj,
                   hγx, hγy, List.getElem?_cons_zero, Option.getD_some]
        constructor
        · intro h; exact decide_eq_true_iff.mp h
        · intro h; exact decide_eq_true_iff.mpr h
  | not_var hlk =>
      rename_i x r
      intro k γ hE
      have hv₁ := EnvCloses.lookup hE hlk
      simp only [TyDenote] at hv₁; obtain ⟨b, hγx, _⟩ := hv₁
      have hx : Exp.substEnv γ (.fvar x) = .bconst b := by simp [Exp.substEnv_fvar, hγx]
      refine ⟨.val (.bconst (!b)) k, ?_, fun v m ho => ?_⟩
      · rw [Exp.substEnv_not, hx]; exact Eval.not_ Eval.bconst
      · injection ho with h₁ h₂; subst h₁ h₂
        simp only [TyDenote]; refine ⟨!b, rfl, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx]
  | and_var hlkx hlky =>
      rename_i x y rx ry
      intro k γ hE
      have hvx := EnvCloses.lookup hE hlkx
      simp only [TyDenote] at hvx; obtain ⟨bx, hγx, _⟩ := hvx
      have hvy := EnvCloses.lookup hE hlky
      simp only [TyDenote] at hvy; obtain ⟨by_, hγy, _⟩ := hvy
      have hxx : Exp.substEnv γ (.fvar x) = .bconst bx := by simp [Exp.substEnv_fvar, hγx]
      have hyy : Exp.substEnv γ (.fvar y) = .bconst by_ := by simp [Exp.substEnv_fvar, hγy]
      refine ⟨.val (.bconst (bx && by_)) k, ?_, fun v m ho => ?_⟩
      · rw [Exp.substEnv_and, hxx, hyy]; exact Eval.and_ Eval.bconst Eval.bconst
      · injection ho with h₁ h₂; subst h₁ h₂
        simp only [TyDenote]; refine ⟨bx && by_, rfl, ?_⟩
        simp [Refinement.interp, Formula.interp, Term.interp,
              REnv.getBV, REnv.get, REnv.lookup, hγx, hγy]
  | lam hwf_arr hfresh ih =>
      rename_i Γ' body s₁ s₂ x ih_fund
      intro k γ hE
      rw [Exp.substEnv_lam]
      have hbody_dom : ∀ z ∈ body.fv, z ∈ TEnv.dom Γ' := by
        intro z hz
        obtain ⟨t', hzΓ⟩ := (Hastype.lam hwf_arr hfresh ih).fv_subset z (by simpa [Exp.fv] using hz)
        exact mem_TEnv_dom hzΓ
      show ExpDenote _ _ _ _ (Val.clos (Exp.substEnv γ body)).toExp
      apply ExpDenote.of_val
      simp only [TyDenote]
      refine ⟨⟨_, Or.inl rfl⟩, ?_, ?_, ?_⟩
      · simp only [Val.lc]
        exact Exp.substEnv_lc_at γ body 1
          (fun z hz => EnvCloses.mem_lc hE (hbody_dom z hz))
          (Hastype.lam hwf_arr hfresh ih).lc_at
      · simp only [Val.closed, Val.fv]
        exact Exp.substEnv_fv_nil γ body
          (fun z hz => EnvCloses.mem_closed hE (hbody_dom z hz))
      · intro j hj va htd_va
        simp [List.mem_append, not_or] at hfresh
        obtain ⟨hxΓ, hxΓfv, hxbody, hxs₁, hxs₂⟩ := hfresh
        have hEx : EnvCloses κ j ((x, s₁) :: Γ') (γ.write x va) :=
          EnvCloses.extend (hE.mono (Nat.le_of_lt hj)) x s₁ va hxΓ hxΓfv
            (TyDenote.extendBy_fresh x va hxs₁ htd_va)
        obtain ⟨o, hev, hres⟩ := ih_fund hEx
        rw [Exp.substEnv_write_openVar body γ va x 0 hxbody
              (fun w hw => EnvCloses.mem_lc hE (hbody_dom w hw))] at hev
        exact ⟨_, o, rfl, hev, fun vr m ho =>
          (TyDenote.push_iff κ m s₂ x γ va vr hxs₂).mpr (hres vr m ho)⟩
  | app h_fn h_arg hyfv ih_fn ih_arg =>
      rename_i e₁ y s t
      intro k γ hE
      rw [Exp.substEnv_app]
      obtain ⟨o₁, hev₁, hres₁⟩ := ih_fn hE
      cases o₁ with
      | timeout => exact ⟨.timeout, Eval.app_to₁ hev₁, fun _ _ ho => by cases ho⟩
      | val f n₁ =>
        have htd_f := hres₁ f n₁ rfl
        have hn₁ := Eval.fuel_le hev₁
        -- The argument is the variable `y`: it evaluates to `γ.map y` for free.
        obtain ⟨o₂, hev₂, hres₂⟩ := ih_arg (hE.mono hn₁)
        rw [Exp.substEnv_fvar] at hev₂ ⊢
        have ho₂ := Eval.toExp_inv hev₂
        subst ho₂
        have htd_va := hres₂ _ _ rfl
        simp only [TyDenote] at htd_f
        obtain ⟨hfun, _, _, hLR⟩ := htd_f
        cases n₁ with
        | zero =>
          obtain ⟨body, hap⟩ := Val.apply_isSome hfun (γ.map y)
          exact ⟨.timeout, Eval.app_tick hev₁ (Eval.toExp 0 _) hap, fun _ _ ho => by cases ho⟩
        | succ m₁ =>
          obtain ⟨body, o, hap, hev, hres⟩ :=
            hLR m₁ (Nat.lt_succ_self _) (γ.map y) (TyDenote.mono (Nat.le_succ _) htd_va)
          refine ⟨o, Eval.app hev₁ (Eval.toExp _ _) hap hev, fun vr m ho => ?_⟩
          have h := (TyDenote.push_iff κ m t y γ (γ.map y) vr hyfv).mp (hres vr m ho)
          rwa [REnv.write_idem] at h
  | @letin Γ' e₁ e₂ s' t' x hwfbv hht xf hhto ih₁ ih₂ =>
      intro k γ hE
      rw [Exp.substEnv_letin]
      obtain ⟨o₁, hev₁, hres₁⟩ := ih₁ hE
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
        have hEx : EnvCloses κ n₁ ((x, s') :: Γ') (γ.write x v₁) :=
          EnvCloses.extend (hE.mono (Eval.fuel_le hev₁)) x s' v₁ hxΓ hxΓfv
            (TyDenote.extendBy_fresh x v₁ hxs htd₁)
        obtain ⟨o, hev, hres⟩ := ih₂ hEx
        rw [Exp.substEnv_write_openVar e₂ γ v₁ x 0 hxbody
              (fun w hw => EnvCloses.mem_lc hE (he₂_dom w hw))] at hev
        exact ⟨o, Eval.letin hev₁ hev, fun vr m ho =>
          TyDenote.of_extendBy_fresh x v₁ hxt (hres vr m ho)⟩
  | ite hlk hfresh _ h₁ h₂ ih_e₁ ih_e₂ =>
      rename_i Γ x y e₁ e₂ r t _
      intro k γ hE
      have htd_x := EnvCloses.lookup hE hlk
      simp only [TyDenote] at htd_x
      obtain ⟨bx, hγx, _⟩ := htd_x
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
      cases bx with
      | true =>
        have htd_guard : TyDenote κ k (.refine .bool r_true)
            (γ.write y (.bconst (γ.bools y)))
            (.bconst (γ.bools y)) := by
          simp only [TyDenote, r_true]
          refine ⟨γ.bools y, rfl, ?_⟩
          simp [Refinement.interp, Formula.interp, Term.interp,
                REnv.get, REnv.lookup, hyx, hγx]
        have hE₁ : EnvCloses κ k ((y, .refine .bool r_true) :: Γ)
            (γ.write y (.bconst (γ.bools y))) :=
          EnvCloses.extend hE y (.refine .bool r_true) (.bconst (γ.bools y))
            hy_dom hy_tyfv htd_guard
        obtain ⟨o, hev, hres⟩ := ih_e₁ hE₁
        rw [Exp.substEnv_write_fresh e₁ γ y (.bconst (γ.bools y)) hy_e₁] at hev
        exact ⟨o, Eval.ite_t Eval.bconst hev, fun vr m ho =>
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y)) hy_tfv (hres vr m ho)⟩
      | false =>
        have htd_guard : TyDenote κ k (.refine .bool r_false)
            (γ.write y (.bconst (γ.bools y)))
            (.bconst (γ.bools y)) := by
          simp only [TyDenote, r_false]
          refine ⟨γ.bools y, rfl, ?_⟩
          simp [Refinement.interp, Formula.interp, Term.interp,
                REnv.get, REnv.lookup, hyx, hγx]
        have hE₂ : EnvCloses κ k ((y, .refine .bool r_false) :: Γ)
            (γ.write y (.bconst (γ.bools y))) :=
          EnvCloses.extend hE y (.refine .bool r_false) (.bconst (γ.bools y))
            hy_dom hy_tyfv htd_guard
        obtain ⟨o, hev, hres⟩ := ih_e₂ hE₂
        rw [Exp.substEnv_write_fresh e₂ γ y (.bconst (γ.bools y)) hy_e₂] at hev
        exact ⟨o, Eval.ite_f Eval.bconst hev, fun vr m ho =>
          TyDenote.of_extendBy_fresh y (.bconst (γ.bools y)) hy_tfv (hres vr m ho)⟩
  | @fix Γ' e s t f x hwf hf hx hbody ih =>
      intro k γ hE
      rw [Exp.substEnv_fix]
      have hfix := Hastype.fix hwf hf hx hbody
      have he_dom : ∀ w ∈ e.fv, w ∈ TEnv.dom Γ' := by
        intro w hw
        obtain ⟨t', hwΓ⟩ := hfix.fv_subset w (by simpa [Exp.fv] using hw)
        exact mem_TEnv_dom hwΓ
      have he_lc : e.lc_at 2 := by simpa [Exp.lc_at] using hfix.lc_at
      simp only [List.mem_append, List.mem_singleton, not_or] at hf hx
      obtain ⟨⟨⟨⟨hfΓ, hfΓfv⟩, hfe⟩, hfs⟩, hft⟩ := hf
      obtain ⟨⟨⟨⟨⟨hxΓ, hxΓfv⟩, hxe⟩, hxs⟩, hxt⟩, hxf⟩ := hx
      -- The recursive closure is in the relation at every index, by induction
      -- on the index: a recursive call happens after a β-step, i.e. at `j < k`.
      have key : ∀ k, EnvCloses κ k Γ' γ →
          TyDenote κ k (.arrow s t) γ (.fclos (Exp.substEnv γ e)) := by
        intro k
        induction k using Nat.strongRecOn with
        | ind k IH =>
        intro hE
        simp only [TyDenote]
        refine ⟨⟨_, Or.inr rfl⟩, ?_, ?_, ?_⟩
        · simp only [Val.lc]
          exact Exp.substEnv_lc_at γ e 2
            (fun z hz => EnvCloses.mem_lc hE (he_dom z hz)) he_lc
        · simp only [Val.closed, Val.fv]
          exact Exp.substEnv_fv_nil γ e
            (fun z hz => EnvCloses.mem_closed hE (he_dom z hz))
        · intro j hj va htd_va
          have hEj := hE.mono (Nat.le_of_lt hj)
          let vf : Val := .fclos (Exp.substEnv γ e)
          have htd_f : TyDenote κ j (.arrow s t) γ vf := IH j hj hEj
          have hf_st : f ∉ (Ty.arrow s t).fv := by simp [Ty.fv, hfs, hft]
          have hx_st : x ∉ (Ty.arrow s t).fv := by simp [Ty.fv, hxs, hxt]
          have hE₁ : EnvCloses κ j ((f, .arrow s t) :: Γ') (γ.write f vf) :=
            EnvCloses.extend hEj f _ vf hfΓ hfΓfv (TyDenote.extendBy_fresh f vf hf_st htd_f)
          have hE₂ : EnvCloses κ j ((x, s) :: (f, .arrow s t) :: Γ')
              ((γ.write f vf).write x va) :=
            EnvCloses.extend hE₁ x s va
              (by simp only [TEnv.dom, List.mem_cons, not_or]; exact ⟨hxf, hxΓ⟩)
              (by simp only [TEnv.tyFv, List.mem_append, not_or]; exact ⟨hx_st, hxΓfv⟩)
              (TyDenote.extendBy_fresh x va hxs (TyDenote.extendBy_fresh f vf hfs htd_va))
          obtain ⟨o, hev, hres⟩ := ih hE₂
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
                (fun w hw => EnvCloses.mem_lc hE (he_dom w hw))] at hev
          refine ⟨_, o, rfl, hev, fun vr m ho => ?_⟩
          have h := (TyDenote.push_iff κ m t x (γ.write f vf) va vr hxt).mpr (hres vr m ho)
          rw [REnv.push_write_comm] at h
          exact TyDenote.of_extendBy_fresh f vf hft h
      exact ⟨_, Eval.fix, fun v m ho => by
        injection ho with h₁ h₂; subst h₁ h₂; exact key k hE⟩

/-! ## T3 — Closed-term type safety (corollary of T2) -/

/-- A well-typed closed program never gets stuck: for every fuel budget `n` it
    either times out or returns a value, and every returned value (with `m`
    fuel left) is in its type's denotation at index `m`. -/
theorem type_safety {κ : KEnv} {e : Exp} {t : Ty} (h : Hastype κ [] e t) :
    ∀ n, ∃ o, Eval n e o ∧ ∀ v m, o = .val v m → TyDenote κ m t REnv.empty v := by
  intro n
  have hfv : e.fv = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun z hz => by
      obtain ⟨t', ht'⟩ := h.fv_subset z hz; simp at ht'
  have hden := hastype_fundamental h (k := n) (γ := REnv.empty) (by simp [EnvCloses])
  rw [Exp.substEnv_closed REnv.empty e hfv] at hden
  exact hden

/-! ## T4 — End-to-end VCGen safety

  VCGen soundness composes with the logical-relations fundamental lemma to give
  end-to-end (fuel-indexed, partial) refinement type safety for `topVC`. -/

theorem vcgen_safety {κ : KEnv} {e : Exp} {t : Ty}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t) :
    ∀ n, ∃ o, Eval n e o ∧ ∀ v m, o = .val v m → TyDenote κ m t REnv.empty v :=
  type_safety (topVC_decl_sound κ e t hE ht h)

/-- Progress: a program accepted by VCGen never gets stuck. -/
theorem vcgen_no_stuck {κ : KEnv} {e : Exp} {t : Ty}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) (h : topVC κ [] e t) :
    ∀ n, ∃ o, Eval n e o := fun n =>
  let ⟨o, hev, _⟩ := vcgen_safety hE ht h n
  ⟨o, hev⟩

/-- Partial correctness at base type: if a program accepted by VCGen terminates
    (under any fuel budget), its value satisfies the result refinement. -/
theorem vcgen_partial_correct {κ : KEnv} {e : Exp} {b : Base} {r : Refinement}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars (.refine b r)) (h : topVC κ [] e (.refine b r))
    {n m : Nat} {v : Val} (hev : Eval n e (.val v m)) :
    ∃ ν : b.interp, v = Val.inj b ν ∧ Refinement.interp κ r (REnv.empty.push (Val.inj b ν)) := by
  obtain ⟨o, hev', hres⟩ := vcgen_safety hE ht h n
  cases Eval.det hev hev'
  simpa only [TyDenote] using hres v m rfl
