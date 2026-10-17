import Flex.VCG.STLC.VCGen
import Flex.VCG.STLC.Declarative

open STLC

/-! # VCGen Soundness (skeleton, κ-indexed)

  Algorithmic VC generation is sound w.r.t. the bidirectional and declarative
  typing rules. Every judgement is now parameterized by `κ : KEnv`.

-/

namespace STLC

/-- A binding type with a refined hypothesis is that refinement type. -/
theorem Ty.hyp?_eq_some {t : Ty} {b : Base} {r : Refinement}
    (h : t.hyp? = some (b, r)) : t = .refine b r := by
  cases t with
  | refine b' r' =>
    cases b' with
    | tfvar a =>
      rcases a with ⟨n, _ | _⟩
      · simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
      · simp at h
    | tbvar _ => simp at h
    | _ => simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | arrow _ _ | «forall» _ _ | prod _ _ | data _ _ _ _ => simp at h

/-- `implyBindCstr` over a binding with hypothesis `r` at sort `b` interprets
    as a `push`-form quantified bind, provided `x` is fresh for `r`. -/
theorem implyBindCstr_interp_some {κ : KEnv} {x : EVar} {t : Ty} {b : Base} {r : Refinement}
    {c : Cstr} {γ : REnv} (ht : t.hyp? = some (b, r)) (hx : x ∉ r.fv) :
    (implyBindCstr x t c).interp κ γ ↔
    ∀ v : b.sem γ.sorts, Refinement.interp κ r (γ.push (Val.inj (b.resolve γ.sorts) v)) →
      c.interp κ (REnv.update b γ x v) := by
  simp only [implyBindCstr, ht, Cstr.interp]
  constructor <;> intro h v
  · intro hr
    exact h v ((Refinement.interp_openBVar κ r γ x (Val.inj (b.resolve γ.sorts) v) 0
      (Nat.zero_le _) hx).mpr hr)
  · intro hr
    exact h v ((Refinement.interp_openBVar κ r γ x (Val.inj (b.resolve γ.sorts) v) 0
      (Nat.zero_le _) hx).mp hr)

/-- `implyBindCstr` over a binding with no hypothesis is the identity. -/
theorem implyBindCstr_interp_none {κ : KEnv} {x : EVar} {t : Ty} {c : Cstr} {γ : REnv}
    (ht : t.hyp? = none) (hd : t.dhyp? = none) :
    (implyBindCstr x t c).interp κ γ ↔ c.interp κ γ := by
  simp only [implyBindCstr, ht, hd]

/-- The refinement of a datatype binding is fresh for whatever is fresh for the type. -/
theorem Ty.dhyp?_fv {t : Ty} {r : Refinement} {x : EVar} (hd : t.dhyp? = some r)
    (hx : x ∉ t.fv) : x ∉ r.fv := by
  cases t <;> simp_all [Ty.dhyp?, Ty.fv]

/-- `implyBindCstr` over a datatype binding: its refinement, read at the slot
    `x` itself, is a hypothesis. -/
theorem implyBindCstr_interp_data {κ : KEnv} {x : EVar} {t : Ty} {r : Refinement} {c : Cstr}
    {γ : REnv} (hd : t.dhyp? = some r) (hx : x ∉ r.fv) :
    (implyBindCstr x t c).interp κ γ ↔
      (Refinement.interp κ r (γ.push (γ.map x)) → c.interp κ γ) := by
  simp only [implyBindCstr, Ty.hyp?_of_dhyp? hd, hd, Cstr.interp]
  have := Refinement.interp_openBVar κ r γ x (γ.map x) 0 (Nat.zero_le _) hx
  rw [REnv.write_idem, REnv.insertBV_zero] at this
  rw [this]

/-- Semantic (`push`-form) reading of a bind. -/
def implyBindSem (κ : KEnv) (x : EVar) (t : Ty) (c : Cstr) (γ : REnv) : Prop :=
  match t.hyp? with
  | some (b, r) => ∀ v : b.sem γ.sorts,
                     Refinement.interp κ r (γ.push (Val.inj (b.resolve γ.sorts) v)) →
                       c.interp κ (REnv.update b γ x v)
  | none        =>
    match t.dhyp? with
    | some r => Refinement.interp κ r (γ.push (γ.map x)) → c.interp κ γ
    | none   => c.interp κ γ

/-- `implyBindCstr` interprets as `implyBindSem`, for *any* binding type
    (provided `x` is fresh for the binding's refinement). -/
theorem implyBindCstr_interp_gen (κ : KEnv) (x : EVar) (t : Ty) (c : Cstr)
    (γ : REnv) (hx : x ∉ t.fv) :
    (implyBindCstr x t c).interp κ γ ↔ implyBindSem κ x t c γ := by
  cases ht : t.hyp? with
  | none =>
    cases hd : t.dhyp? with
    | none => simp only [implyBindSem, ht, hd]; exact implyBindCstr_interp_none ht hd
    | some r =>
      simp only [implyBindSem, ht, hd]
      exact implyBindCstr_interp_data hd (Ty.dhyp?_fv hd hx)
  | some p =>
    obtain ⟨b, r⟩ := p
    have htr := Ty.hyp?_eq_some ht
    subst htr
    simp only [implyBindSem, ht]
    exact implyBindCstr_interp_some ht (by simpa [Ty.fv] using hx)

/-- Eliminate a bind in a model of the extended context: if `γ` models
    `(x, t) :: Γ` then `implyBindCstr x t c` yields `c` at `γ` itself (instantiate
    the bound value with the one stored at `x`). -/
theorem implyBind_elim {κ : KEnv} {γ : REnv} {x : EVar} {t : Ty} {c : Cstr} {Γ : TEnv}
    (hm : ModelsEnv κ γ ((x, t) :: Γ)) (hx : x ∉ t.fv)
    (h : (implyBindCstr x t c).interp κ γ) : c.interp κ γ := by
  cases ht : t.hyp? with
  | none =>
    cases hd : t.dhyp? with
    | none => exact (implyBindCstr_interp_none ht hd).mp h
    | some r =>
      exact (implyBindCstr_interp_data hd (Ty.dhyp?_fv hd hx)).mp h ((ModelsEnv.cons_data hd).mp hm).1
  | some p =>
    obtain ⟨b, r⟩ := p
    have htr := Ty.hyp?_eq_some ht
    subst htr
    obtain ⟨⟨hb, hsat⟩, _⟩ := (ModelsEnv.cons_some ht).mp hm
    have hb' := (implyBindCstr_interp_some ht (by simpa [Ty.fv] using hx)).mp h
    rw [REnv.lookup_eq_inj_get b γ x hb] at hsat
    have h2 := hb' (REnv.get b γ x) hsat
    rwa [REnv.update_self b γ x hb] at h2

end STLC

/-! ## Sub soundness -/

/-- `Exp.WFBVars` is preserved under `Exp.openVar`. (openVar replaces a `bvar k`
    with a `fvar x`, neither of which adds annotations or otherwise affects
    the WFBVars predicate.) -/
@[simp]
theorem Exp.WFBVars_openVar (e : Exp) (k : Nat) (x : EVar) :
    Exp.WFBVars (e.openVar k x) ↔ Exp.WFBVars e := by
  induction e generalizing k with
  | bvar _ => simp [Exp.openVar, Exp.WFBVars]; split <;> simp [Exp.WFBVars]
  | fvar _ | iconst _ | bconst _ => simp [Exp.openVar, Exp.WFBVars]
  | lam e ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | letin e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | app e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | ann e t ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | and e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | not e ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | leq e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₀, ih₁, ih₂]
  | add e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | unreach => simp [Exp.openVar, Exp.WFBVars]
  | fix e ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | tabs _ e ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | tapp e t ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | pair e₁ e₂ ih₁ ih₂ | split e₁ e₂ ih₁ ih₂ => simp [Exp.openVar, Exp.WFBVars, ih₁, ih₂]
  | ctor C j τs e ih => simp [Exp.openVar, Exp.WFBVars, ih]
  | case e n alts ih ihs => simp [Exp.openVar, Exp.WFBVars, ih, ihs]


theorem sub_sound {de : DEnv} (κ : KEnv) (Γ : TEnv) (s t : Ty) (c : Cstr) :
    sub de Γ s t = some c → Entail κ Γ (c.interp κ) → Subtyp de κ Γ s t := by
  intro hsub hent
  match s, t with
  | .refine b₁ r1, .refine b₂ r2 =>
    simp only [sub] at hsub
    split at hsub
    · rename_i hb
      subst hb
      injection hsub with hc
      subst hc
      have hfr := EVar.fresh_not_mem (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r1.fv ++ r2.fv)
      have hx1 : EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r1.fv ++ r2.fv) ∉ (Ty.refine b₁ r1).fv := by
        simp only [Ty.fv]; simp only [List.mem_append, not_or] at hfr; exact hfr.1.2
      -- The emitted constraint binds the fresh `x` exactly as the extension
      -- binder of the opened rule does: eliminate it against the model.
      refine Subtyp.refine hfr ?_
      intro γ hm
      exact implyBind_elim hm hx1 (hent γ hm.tail)
    · simp at hsub
  | .arrow s1 t1, .arrow s2 t2 =>
    simp_all [sub]
    let w := (EVar.fresh (Γ.dom ++ (Γ.tyFv ++ (s1.fv ++ (s2.fv ++ (t1.fv ++ t2.fv))))))
    have hwd : w = EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ s1.fv ++ s2.fv ++ t1.fv ++ t2.fv) := by grind
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, sub de Γ s2 s1 = some c₁ := by
      rcases Option.eq_none_or_eq_some (sub de Γ s2 s1) with eqn | eqs
      · simp_all
      · assumption
    obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de ((w, s2) :: Γ) (t1.openVar 0 w) (t2.openVar 0 w) = some c₂ := by
      rcases Option.eq_none_or_eq_some (sub de ((w, s2) :: Γ) (t1.openVar 0 w) (t2.openVar 0 w)) with eqn | eqs
      · simp_all
      · assumption
    -- avoid `simp at hsub` to keep implyBind folded
    rw [hc₁, hc₂] at hsub
    simp only [Option.some.injEq] at hsub
    have hw : w ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ s1.fv ++ s2.fv ++ t1.fv ++ t2.fv := by
      grind [EVar.fresh_not_mem (Γ.dom ++ (Γ.tyFv ++ (s1.fv ++ (s2.fv ++ (t1.fv ++ t2.fv)))))]
    apply Subtyp.arrow (x := w) _ hw
    · apply sub_sound κ ((w, s2) :: Γ) _ _ c₂ hc₂
      intro γ hm
      rw [←hsub] at hent
      have hcγ := hent γ hm.tail
      simp only [Cstr.interp] at hcγ
      have hws : w ∉ s2.fv := by
        have := hw; simp only [List.mem_append, not_or] at this
        exact this.1.1.2
      exact implyBind_elim hm hws hcγ.2
    · apply sub_sound κ Γ s2 s1 c₁ hc₁
      intro γ hm
      rw [←hsub] at hent
      exact (hent γ hm).1
  | .forall k₁ t₁, .forall k₂ t₂ =>
    simp only [sub] at hsub
    split at hsub
    · rename_i hk
      subst hk
      exact Subtyp.forall rfl (TVar.fresh_not_mem _ _) (sub_sound κ Γ _ _ c hsub hent)
    · simp at hsub
  | .prod s1 t1, .prod s2 t2 =>
    simp only [sub] at hsub
    have hfr := EVar.fresh_not_mem (TEnv.dom Γ ++ TEnv.tyFv Γ ++ s1.fv ++ s2.fv ++ t1.fv ++ t2.fv)
    generalize EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ s1.fv ++ s2.fv ++ t1.fv ++ t2.fv) = w
      at hfr hsub
    cases hc₁ : sub de Γ s1 s2 with
    | none => simp [hc₁] at hsub
    | some c₁ =>
      cases hc₂ : sub de ((w, s1) :: Γ) (t1.openVar 0 w) (t2.openVar 0 w) with
      | none => simp [hc₁, hc₂] at hsub
      | some c₂ =>
        simp only [hc₁, hc₂, Option.some.injEq] at hsub
        subst hsub
        have hws : w ∉ s1.fv := by
          simp only [List.mem_append, not_or] at hfr; exact hfr.1.1.1.2
        exact Subtyp.prod (sub_sound κ Γ s1 s2 c₁ hc₁ fun γ hm => (hent γ hm).1) hfr
          (sub_sound κ ((w, s1) :: Γ) _ _ c₂ hc₂
            fun γ hm => implyBind_elim hm hws (hent γ hm.tail).2)
  | .data C1 n1 a1 r1, .data C2 n2 a2 r2 =>
    simp only [sub] at hsub
    split at hsub
    · rename_i h
      obtain ⟨hC, hn⟩ := h
      obtain ⟨ca, hall', hca⟩ := Option.map_eq_some_iff.mp hsub
      subst hca
      -- the per-argument constraints, by variance
      have hall : ∀ i, (de.var C1 i.val ≠ .contra → ∃ c₁, sub de Γ (a1 i) (a2 (Fin.cast hn i)) = some c₁ ∧
            ∀ γ, ca.interp κ γ → c₁.interp κ γ) ∧
          (de.var C1 i.val ≠ .co → ∃ c₂, sub de Γ (a2 (Fin.cast hn i)) (a1 i) = some c₂ ∧
            ∀ γ, ca.interp κ γ → c₂.interp κ γ) := by
        intro i
        obtain ⟨ci, hfi, himp⟩ := Cstr.conjAll_some hall' i (List.mem_finRange i)
        cases hv : de.var C1 i.val with
        | co =>
          simp only [hv] at hfi
          exact ⟨fun _ => ⟨ci, hfi, fun γ hc => himp κ γ hc⟩, fun h => absurd rfl h⟩
        | contra =>
          simp only [hv] at hfi
          exact ⟨fun h => absurd rfl h, fun _ => ⟨ci, hfi, fun γ hc => himp κ γ hc⟩⟩
        | inv =>
          simp only [hv] at hfi
          cases h₁ : sub de Γ (a1 i) (a2 (Fin.cast hn i)) with
          | none => simp [h₁] at hfi
          | some c₁ =>
            cases h₂ : sub de Γ (a2 (Fin.cast hn i)) (a1 i) with
            | none => simp [h₁, h₂] at hfi
            | some c₂ =>
              simp only [h₁, h₂, Option.some.injEq] at hfi
              subst hfi
              exact ⟨fun _ => ⟨c₁, rfl, fun γ hc => (himp κ γ hc).1⟩,
                     fun _ => ⟨c₂, rfl, fun γ hc => (himp κ γ hc).2⟩⟩
      have hs₁ : ∀ i, de.var C1 i.val ≠ .contra → Subtyp de κ Γ (a1 i) (a2 (Fin.cast hn i)) :=
        fun i hi => by
          obtain ⟨c₁, h₁, himp⟩ := (hall i).1 hi
          have := Ty.skel_data_lt C1 n1 a1 r1 i
          have := Ty.skel_data_lt C2 n2 a2 r2 (Fin.cast hn i)
          exact sub_sound κ Γ _ _ c₁ h₁ fun γ hm => himp γ (hent γ hm).1
      have hs₂ : ∀ i, de.var C1 i.val ≠ .co → Subtyp de κ Γ (a2 (Fin.cast hn i)) (a1 i) :=
        fun i hi => by
          obtain ⟨c₂, h₂, himp⟩ := (hall i).2 hi
          have := Ty.skel_data_lt C1 n1 a1 r1 i
          have := Ty.skel_data_lt C2 n2 a2 r2 (Fin.cast hn i)
          exact sub_sound κ Γ _ _ c₂ h₂ fun γ hm => himp γ (hent γ hm).1
      have hfr := EVar.fresh_not_mem (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r1.fv ++ r2.fv)
      have hx1 : EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r1.fv ++ r2.fv) ∉ r1.fv := by
        simp only [List.mem_append, not_or] at hfr; exact hfr.1.2
      subst hC hn
      refine Subtyp.data (fun i hi => by simpa using hs₁ i hi) (fun i hi => by simpa using hs₂ i hi)
        hfr ?_
      intro γ hm
      exact (implyBindCstr_interp_data rfl hx1).mp (hent γ hm.tail).2 ((ModelsEnv.cons_data rfl).mp hm).1
    · simp at hsub
  | .refine _ _, .arrow _ _ | .refine _ _, .forall _ _ | .arrow _ _, .refine _ _
  | .arrow _ _, .forall _ _ | .forall _ _, .refine _ _ | .forall _ _, .arrow _ _
  | .refine _ _, .prod _ _ | .refine _ _, .data _ _ _ _ | .arrow _ _, .prod _ _ | .arrow _ _, .data _ _ _ _
  | .forall _ _, .prod _ _ | .forall _ _, .data _ _ _ _ | .prod _ _, .refine _ _ | .prod _ _, .arrow _ _
  | .prod _ _, .forall _ _ | .prod _ _, .data _ _ _ _ | .data _ _ _ _, .refine _ _ | .data _ _ _ _, .arrow _ _
  | .data _ _ _ _, .forall _ _ | .data _ _ _ _, .prod _ _ =>
    simp [sub] at hsub
  termination_by s.skel + t.skel
  decreasing_by
    all_goals (simp_wf; simp only [Ty.skel, Ty.skel_openVar, Ty.skel_openTv] at *; omega)

/-! ## Synth / Check soundness (mutual) -/

mutual
  theorem synth_sound {de : DEnv} (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Cstr) (t : Ty) :
      synth de Γ e = some (c, t) → Entail κ Γ (c.interp κ) → Synth de κ Γ e t := by
    intro hsynth hent
    match e with
    | .bvar i =>
      simp_all [synth]
    | .fvar x =>
      simp only [synth] at hsynth
      cases hl : Γ.lookup x with
      | none => simp [hl] at hsynth
      | some t' =>
        simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsynth
        obtain ⟨-, rfl⟩ := hsynth
        exact Synth.var hl
    | .iconst i | .bconst b =>
      simp_all [synth]
      rw [←hsynth.2]
      constructor
    | .not (.fvar x) =>
      simp_all [synth]
      obtain ⟨r, hr⟩ : ∃ r, List.lookup x Γ = some (.refine .bool r) := by grind
      simp_all ; rw [←hsynth.2] ; constructor ; assumption
    | .and (.fvar x) (.fvar y) =>
      simp_all [synth]
      obtain ⟨rx, ry, hrx, hry⟩ : ∃ rx ry,
          List.lookup x Γ = some (.refine .bool rx) ∧
          List.lookup y Γ = some (.refine .bool ry) := by grind
      simp_all ; rw [←hsynth.2] ; constructor <;> assumption
    | .lam e | .letin e1 e2 | .ite _ _ _ | .fix _ | .tabs _ _ =>
      simp_all [synth]
    | .tapp e₀ s₀ =>
      simp only [synth] at hsynth
      cases hse : synth de Γ e₀ with
      | none => simp [hse] at hsynth
      | some p =>
        obtain ⟨c', t'⟩ := p
        rw [hse] at hsynth
        cases t' with
        | «forall» k t₀ =>
          simp only at hsynth
          split at hsynth
          · rename_i hcond
            obtain ⟨hk, h1, h2, h3⟩ := hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at hsynth
            obtain ⟨rfl, rfl⟩ := hsynth
            exact Synth.tapp (synth_sound κ Γ e₀ c' (.forall k t₀) hse hent) hk h1 h2 h3
          · simp at hsynth
        | refine _ _ | arrow _ _ | prod _ _ | data _ _ _ _ => simp at hsynth
    | .ctor C j τs e₀ =>
      simp only [synth] at hsynth
      cases hP : de.payload? C j with
      | none => simp [hP] at hsynth
      | some P =>
        simp only [hP] at hsynth
        split at hsynth
        · rename_i hok
          cases hc : check de Γ e₀ (Ty.instTys τs P) with
          | none => simp [hc] at hsynth
          | some c' =>
            simp only [hc, Option.some.injEq, Prod.mk.injEq] at hsynth
            obtain ⟨rfl, rfl⟩ := hsynth
            exact Synth.ctor hP hok (check_sound κ Γ e₀ _ c' hc hent)
        · simp at hsynth
    | .pair _ _ | .split _ _ | .case _ _ _ => simp_all [synth]
    | .app e1 (.fvar y) =>
      simp_all [synth]
      obtain ⟨c1, s', t', hse⟩ : ∃ c s t, synth de Γ e1 = some (c, .arrow s t) := by grind
      obtain ⟨c2, hy⟩ : ∃ c, check de Γ (.fvar y) s' = some c := by grind
      simp_all
      obtain ⟨hyfv, hceq, hteq⟩ := hsynth
      rw [← hteq]
      rw [← hceq] at hent
      exact Synth.app
        (synth_sound κ Γ e1 c1 _ hse fun γ hm => (hent γ hm).1)
        (check_sound κ Γ (.fvar y) s' c2 hy fun γ hm => (hent γ hm).2)
        hyfv
    | .ann e1 t' =>
      simp_all [synth]
      obtain ⟨c', hc⟩ : ∃ c, check de Γ e1 t' = some c := by grind
      simp_all
      exact Synth.ann (check_sound κ Γ e1 t c hc hent)
    | .leq (.fvar x) (.fvar y) =>
      simp only [synth] at hsynth
      split at hsynth
      · rename_i b r₁ b' r₂ hx hy
        split at hsynth
        · rename_i h
          obtain ⟨rfl, hb⟩ := h
          simp only [Option.some.injEq, Prod.mk.injEq] at hsynth
          rw [←hsynth.2]
          exact Synth.leq_var hx hy hb
        · cases hsynth
      · cases hsynth
    | .add (.fvar x) (.fvar y) =>
      simp_all [synth]
      obtain ⟨a, b, ha, hb⟩ : ∃ a b, List.lookup x Γ = some (.refine .int a) ∧
          List.lookup y Γ = some (.refine .int b) := by grind
      simp_all
      rw [←hsynth.2]
      constructor <;> assumption
    | (.not (.add _ _)) | (.not (.ite _ _ _)) | (.not (.leq _ _)) | (.not (.not _))
    | (.not (.and _ _)) | (.not (.ann _ _)) | (.not (.app _ _)) | (.not (.letin _ _))
    | (.not (.lam _)) | (.not (.bconst _)) | (.not (.iconst _)) | (.not (.bvar _))
    | (.and (.add _ _) _) | (.and (.ite _ _ _) _) | (.and (.leq _ _) _) | (.and (.not _) _)
    | (.and (.and _ _) _) | (.and (.ann _ _) _) | (.and (.app _ _) _) | (.and (.letin _ _) _)
    | (.and (.lam _) _) | (.and (.bconst _) _) | (.and (.iconst _) _) | (.and (.bvar _) _)
    | (.and (.fvar _) (.add _ _)) | (.and (.fvar _) (.ite _ _ _)) | (.and (.fvar _) (.leq _ _))
    | (.and (.fvar _) (.not _)) | (.and (.fvar _) (.and _ _)) | (.and (.fvar _) (.ann _ _))
    | (.and (.fvar _) (.app _ _)) | (.and (.fvar _) (.letin _ _)) | (.and (.fvar _) (.lam _))
    | (.and (.fvar _) (.bconst _)) | (.and (.fvar _) (.iconst _)) | (.and (.fvar _) (.bvar _))
    | (.add (.add _ _) _) | (.add (.leq _ _) _) | (.add (.and _ _) _) | (.add (.ann _ _) _) | (.add (.app _ _) _)
    | (.add (.ite _ _ _) _) | (.add (.not _) _) | (.add (.letin _ _) _) | (.add (.lam _) _) | (.add (.bconst _) _)
    | (.add (.iconst _) _) | (.add (.fvar _) (.add _ _)) | (.add (.fvar _) (.ite _ _ _)) | (.add (.fvar _) (.leq _ _))
    | (.add (.fvar _) (.not _)) | (.add (.fvar _) (.and _ _)) | (.add (.fvar _) (.ann _ _)) | (.add (.fvar _) (.app _ _))
    | (.add (.fvar _) (.letin _ _)) | (.add (.fvar _) (.lam _)) | (.add (.fvar _) (.bconst _)) | (.add (.fvar _) (.iconst _))
    | (.add (.fvar _) (.bvar _)) | (.add (.bvar _) _) | (.leq (.add _ _) _) | (.leq (.ite _ _ _) _) | (.leq (.leq _ _) _)
    | (.leq (.not _) _) | (.leq (.and _ _) _) | (.leq (.ann _ _) _) | (.leq (.app _ _) _) | (.leq (.letin _ _) _) | (.leq (.lam _) _)
    | (.leq (.bconst _) _) | (.leq (.iconst _) _) | (.leq (.fvar _) (.add _ _)) | (.leq (.fvar _) (.ite _ _ _)) | (.leq (.fvar _) (.leq _ _))
    | (.leq (.fvar _) (.not _)) | (.leq (.fvar _) (.and _ _)) | (.leq (.fvar _) (.ann _ _)) | (.leq (.fvar _) (.app _ _))
    | (.leq (.fvar _) (.letin _ _)) | (.leq (.fvar _) (.lam _)) | (.leq (.fvar _) (.bconst _)) | (.leq (.fvar _) (.iconst _))
    | (.leq (.fvar _) (.bvar _)) | (.leq (.bvar _) _) | (.app _ (.add _ _)) | (.app _ (.ite _ _ _)) | (.app _ (.leq _ _)) | (.app _ (.not _))
    | (.app _ (.and _ _)) | (.app _ (.ann _ _)) | (.app _ (.app _ _)) | (.app _ (.letin _ _)) | (.app _ (.lam _)) | (.app _ (.bconst _))
    | (.app _ (.iconst _)) | (.app _ (.bvar _))
    | .unreach | (.add .unreach _) | (.add (.fvar _) .unreach)
    | (.leq .unreach _) | (.leq (.fvar _) .unreach) | (.not .unreach)
    | (.and .unreach _) | (.and (.fvar _) .unreach) | (.app _ .unreach)
    | (.add (.fix _) _) | (.add (.tabs _ _) _) | (.add (.tapp _ _) _) | (.add (.fvar _) (.fix _)) | (.add (.fvar _) (.tabs _ _)) | (.add (.fvar _) (.tapp _ _))
    | (.leq (.fix _) _) | (.leq (.tabs _ _) _) | (.leq (.tapp _ _) _) | (.leq (.fvar _) (.fix _)) | (.leq (.fvar _) (.tabs _ _)) | (.leq (.fvar _) (.tapp _ _)) | (.not (.fix _)) | (.not (.tabs _ _)) | (.not (.tapp _ _))
    | (.and (.fix _) _) | (.and (.tabs _ _) _) | (.and (.tapp _ _) _) | (.and (.fvar _) (.fix _)) | (.and (.fvar _) (.tabs _ _)) | (.and (.fvar _) (.tapp _ _)) | (.app _ (.fix _)) | (.app _ (.tabs _ _)) | (.app _ (.tapp _ _))
    | (.not (.pair _ _)) | (.and (.pair _ _) _) | (.and (.fvar _) (.pair _ _)) | (.add (.pair _ _) _)
    | (.add (.fvar _) (.pair _ _)) | (.leq (.pair _ _) _) | (.leq (.fvar _) (.pair _ _)) | (.app _ (.pair _ _))
    | (.not (.split _ _)) | (.and (.split _ _) _) | (.and (.fvar _) (.split _ _)) | (.add (.split _ _) _)
    | (.add (.fvar _) (.split _ _)) | (.leq (.split _ _) _) | (.leq (.fvar _) (.split _ _)) | (.app _ (.split _ _))
    | (.not (.ctor _ _ _ _)) | (.and (.ctor _ _ _ _) _) | (.and (.fvar _) (.ctor _ _ _ _)) | (.add (.ctor _ _ _ _) _)
    | (.add (.fvar _) (.ctor _ _ _ _)) | (.leq (.ctor _ _ _ _) _) | (.leq (.fvar _) (.ctor _ _ _ _)) | (.app _ (.ctor _ _ _ _))
    | (.not (.case _ _ _)) | (.and (.case _ _ _) _) | (.and (.fvar _) (.case _ _ _)) | (.add (.case _ _ _) _)
    | (.add (.fvar _) (.case _ _ _)) | (.leq (.case _ _ _) _) | (.leq (.fvar _) (.case _ _ _)) | (.app _ (.case _ _ _))
      => simp_all [synth]
  termination_by 2*e.skel

  theorem check_sound {de : DEnv} (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Cstr) :
      check de Γ e t = some c → Entail κ Γ (c.interp κ) → Check de κ Γ e t := by
    intro hcheck hent
    match e with
    | .unreach =>
      simp only [check] at hcheck
      injection hcheck with hc
      subst hc
      exact Check.unreach hent
    | .bvar i =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth de Γ (.bvar i) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .fvar x =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth de Γ (.fvar x) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .iconst i =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth de Γ (.iconst i) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .bconst b =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth de Γ (.bconst b) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .add e1 e2 =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth de Γ (.add e1 e2) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .ite (.fvar cn) bt bf =>
      simp_all [check]
      obtain ⟨r, hr⟩ : ∃ r, List.lookup cn Γ = some (.refine .bool r) := by grind
      simp_all
      obtain ⟨c₁, c₂, hc₁, hc₂⟩ : ∃ c₁ c₂,
          (check de ((EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ bt.fv ++ bf.fv ++ t.fv ++ [cn]),
                   Ty.refine Base.bool (.fmla (.eq .bool (.fvar .bool cn) (.const .bool true)))) :: Γ) bt t = some c₁) ∧
          (check de ((EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ bt.fv ++ bf.fv ++ t.fv ++ [cn]),
                   Ty.refine .bool (.fmla (.eq .bool (.fvar .bool cn) (.const .bool false)))) :: Γ) bf t = some c₂) := by
        grind
      simp_all
      rw [← hcheck] at hent
      -- `y` is the fresh guard; freshness discharges by `EVar.fresh_not_mem`. The
      -- guard refinement reads `cn` (not `ν`), so the branch obligation is exactly
      -- the matching conjunct of `hent` — no case split on `v` needed.
      have hyf := EVar.fresh_not_mem (TEnv.dom Γ ++ TEnv.tyFv Γ ++ bt.fv ++ bf.fv ++ t.fv ++ [cn])
      refine Check.ite hr (EVar.fresh_not_mem _) ?_ ?_
      · simp only [List.append_assoc]
        apply check_sound _ _ _ _ _ hc₁
        refine Entail.ext (b := .bool)
          (r := .fmla (.eq .bool (.fvar .bool cn) (.const .bool true))) rfl ?_
        intro γ hm
        have hb := (hent γ hm).1
        rw [implyBindCstr_interp_gen κ _ _ c₁ γ
              (by simp only [Ty.fv, Refinement.fv, Formula.fv, Term.fv, List.append_nil,
                    List.mem_append, List.mem_singleton, not_or] at hyf ⊢
                  grind)] at hb
        simpa only [implyBindSem] using hb
      · simp only [List.append_assoc]
        apply check_sound _ _ _ _ _ hc₂
        refine Entail.ext (b := .bool)
          (r := .fmla (.eq .bool (.fvar .bool cn) (.const .bool false))) rfl ?_
        intro γ hm
        have hb := (hent γ hm).2
        rw [implyBindCstr_interp_gen κ _ _ c₂ γ
              (by simp only [Ty.fv, Refinement.fv, Formula.fv, Term.fv, List.append_nil,
                    List.mem_append, List.mem_singleton, not_or] at hyf ⊢
                  grind)] at hb
        simpa only [implyBindSem] using hb
    | .lam e =>
      match t with
      | .refine _ _ | .forall _ _ | .prod _ _ | .data _ _ _ _ =>
        simp_all [check, synth]
      | .arrow s1 t1 =>
        simp_all [check]
        -- Use the LITERAL right-associated fresh expression (matches simp's normal form
        -- so the second simp_all can substitute hc₁ into hcheck).
        obtain ⟨c₁, hc₁⟩ : ∃ c₁, check de ((EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++ TEnv.tyFv Γ)))) , s1) :: Γ)
            (Exp.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++ TEnv.tyFv Γ ))))) e)
            (Ty.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++ TEnv.tyFv Γ ))))) t1) = some c₁ := by grind
        simp_all
        let L₀ : List EVar := TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++ TEnv.tyFv Γ )))
        let x₀ : EVar := EVar.fresh L₀
        -- 1. Body proof at the specific fresh witness `x₀`.
        have hbody₀ :
            Check de κ ((x₀, s1) :: Γ) (Exp.openVar 0 x₀ e) (Ty.openVar 0 x₀ t1) := by
          apply check_sound κ _ _ _ _ hc₁
          intro γ hmγ
          have hcγ : c.interp κ γ := hent γ hmγ.tail
          rw [← hcheck] at hcγ
          have hx₀s : x₀ ∉ s1.fv := by
            have h := EVar.fresh_not_mem L₀
            simp only [L₀, List.mem_append, not_or] at h
            exact h.2.2.1
          exact implyBind_elim hmγ hx₀s hcγ
        have hfresh₀ : x₀ ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s1.fv ++ t1.fv := by
          have h := EVar.fresh_not_mem L₀
          simp only [L₀, List.mem_append, not_or] at h ⊢
          grind
        exact Check.lam hfresh₀ hbody₀
    | .letin e1 e2 =>
      -- check de Γ (.letin e1 e2) t algorithm: synth e1 → (c₁, s); check de ((x₀, s) :: Γ) (e2.openVar 0 x₀) t = some c₂
      simp_all [check]
      obtain ⟨c₁, s, hsynth⟩ : ∃ c₁ s, synth de Γ e1 = some (c₁, s) := by grind
      -- Use LITERAL right-associated fresh expression (matches simp's normal form).
      obtain ⟨c₂, hcheck₂⟩ : ∃ c₂, check de ((EVar.fresh (TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++ TEnv.tyFv Γ)))) , s) :: Γ)
          (Exp.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++ TEnv.tyFv Γ))))) e2) t = some c₂ := by grind
      simp_all
      let L₀ : List EVar := TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++ TEnv.tyFv Γ)))
      let x₀ : EVar := EVar.fresh L₀
      -- 1. Synth at e1 via synth_sound.
      have hsy : Synth de κ Γ e1 s := by
        apply synth_sound _ _ _ _ _ hsynth
        intro γ hγ
        have := hent γ hγ
        rw [←hcheck] at this
        exact this.1
      -- 2. Body Check at x₀ via check_sound.
      have hbody₀ : Check de κ ((x₀, s) :: Γ) (Exp.openVar 0 x₀ e2) t := by
        apply check_sound _ _ _ _ _ hcheck₂
        intro γ hmγ
        have hcγ : c.interp κ γ := hent γ hmγ.tail
        rw [← hcheck] at hcγ
        have hx₀s : x₀ ∉ s.fv := by
          have h := EVar.fresh_not_mem L₀
          simp only [L₀, List.mem_append, not_or] at h
          exact h.2.2.1
        exact implyBind_elim hmγ hx₀s hcγ.2
      have hfresh₀ : x₀ ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e2.fv ++ s.fv ++ t.fv  := by
        have h := EVar.fresh_not_mem L₀
        simp only [L₀, List.mem_append, not_or] at h ⊢
        grind
      exact Check.letin hsy hfresh₀ hbody₀
    | .leq (.fvar x) (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth de Γ ((Exp.fvar x).leq (Exp.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .ann e t' =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth de Γ (.ann e t') = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .app e1 (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth de Γ (.app e1 (.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .not (.fvar x) =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth de Γ (.not (.fvar x)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .and (.fvar x) (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth de Γ (.and (.fvar x) (.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | (.ite (.add _ _) _ _) | (.ite (.ite _ _ _) _ _) | (.ite (.leq _ _) _ _) | (.ite (.not _) _ _)
    | (.ite (.and _ _) _ _) | (.ite (.ann _ _) _ _) | (.ite (.app _ _) _ _) | (.ite (.letin _ _) _ _)
    | (.ite (.lam _) _ _) | (.ite (.bconst true) _ _) | (.ite (.bconst false) _ _)
    | (.ite (.iconst _) _ _) | (.ite (.bvar _) _ _) | (.ite .unreach _ _)
    | (.not (.bvar _)) | (.not (.iconst _)) | (.not (.bconst _)) | (.not (.lam _))
    | (.not (.letin _ _)) | (.not (.app _ _)) | (.not (.ann _ _)) | (.not (.and _ _))
    | (.not (.add _ _)) | (.not (.leq _ _)) | (.not (.ite _ _ _)) | (.not (.not _)) | (.not .unreach)
    | (.and (.fvar _) (.bvar _)) | (.and (.fvar _) (.iconst _)) | (.and (.fvar _) (.bconst _))
    | (.and (.fvar _) (.lam _)) | (.and (.fvar _) (.letin _ _)) | (.and (.fvar _) (.app _ _))
    | (.and (.fvar _) (.ann _ _)) | (.and (.fvar _) (.and _ _)) | (.and (.fvar _) (.add _ _))
    | (.and (.fvar _) (.leq _ _)) | (.and (.fvar _) (.ite _ _ _)) | (.and (.fvar _) (.not _)) | (.and (.fvar _) .unreach)
    | (.and (.bvar _) _) | (.and (.iconst _) _) | (.and (.bconst _) _) | (.and (.lam _) _)
    | (.and (.letin _ _) _) | (.and (.app _ _) _) | (.and (.ann _ _) _)
    | (.and (.add _ _) _) | (.and (.leq _ _) _) | (.and (.ite _ _ _) _) | (.and (.not _) _) | (.and (.and _ _) _) | (.and .unreach _)
    | (.leq (.add _ _) _) | (.leq (.ite _ _ _) _) | (.leq (.leq _ _) _) | (.leq (.not _) _)
    | (.leq (.and _ _) _) | (.leq (.ann _ _) _) | (.leq (.app _ _) _) | (.leq (.letin _ _) _)
    | (.leq (.lam _) _) | (.leq (.bconst _) _) | (.leq (.iconst _) _) | (.leq (.fvar _) (.add _ _))
    | (.leq (.fvar _) (.ite _ _ _)) | (.leq (.fvar _) (.leq _ _)) | (.leq (.fvar _) (.not _)) | (.leq (.fvar _) (.and _ _))
    | (.leq (.fvar _) (.ann _ _)) | (.leq (.fvar _) (.app _ _)) | (.leq (.fvar _) (.letin _ _)) | (.leq (.fvar _) (.lam _))
    | (.leq (.fvar _) (.bconst _)) | (.leq (.fvar _) (.iconst _)) | (.leq (.fvar _) (.bvar _)) | (.leq (.bvar _) _)
    | (.leq (.fvar _) .unreach) | (.leq .unreach _)
    | (.app _ (.add _ _)) | (.app _ (.ite _ _ _)) | (.app _ (.leq _ _)) | (.app _ (.not _))
    | (.app _ (.and _ _)) | (.app _ (.ann _ _)) | (.app _ (.app _ _)) | (.app _ (.letin _ _)) | (.app _ (.lam _)) | (.app _ (.bconst _))
    | (.app _ (.iconst _)) | (.app _ (.bvar _)) | (.app _ .unreach)
    | (.ite (.fix _) _ _) | (.ite (.tabs _ _) _ _) | (.ite (.tapp _ _) _ _) | (.not (.fix _)) | (.not (.tabs _ _)) | (.not (.tapp _ _)) | (.and (.fvar _) (.fix _)) | (.and (.fvar _) (.tabs _ _)) | (.and (.fvar _) (.tapp _ _)) | (.and (.fix _) _) | (.and (.tabs _ _) _) | (.and (.tapp _ _) _)
    | (.leq (.fix _) _) | (.leq (.tabs _ _) _) | (.leq (.tapp _ _) _) | (.leq (.fvar _) (.fix _)) | (.leq (.fvar _) (.tabs _ _)) | (.leq (.fvar _) (.tapp _ _)) | (.app _ (.fix _)) | (.app _ (.tabs _ _)) | (.app _ (.tapp _ _))
    | (.ite (.pair _ _) _ _) | (.not (.pair _ _)) | (.and (.pair _ _) _) | (.and (.fvar _) (.pair _ _))
    | (.leq (.pair _ _) _) | (.leq (.fvar _) (.pair _ _)) | (.app _ (.pair _ _)) | (.ite (.split _ _) _ _)
    | (.not (.split _ _)) | (.and (.split _ _) _) | (.and (.fvar _) (.split _ _)) | (.leq (.split _ _) _)
    | (.leq (.fvar _) (.split _ _)) | (.app _ (.split _ _)) | (.ite (.ctor _ _ _ _) _ _) | (.not (.ctor _ _ _ _))
    | (.and (.ctor _ _ _ _) _) | (.and (.fvar _) (.ctor _ _ _ _)) | (.leq (.ctor _ _ _ _) _) | (.leq (.fvar _) (.ctor _ _ _ _))
    | (.app _ (.ctor _ _ _ _)) | (.ite (.case _ _ _) _ _) | (.not (.case _ _ _)) | (.and (.case _ _ _) _)
    | (.and (.fvar _) (.case _ _ _)) | (.leq (.case _ _ _) _) | (.leq (.fvar _) (.case _ _ _)) | (.app _ (.case _ _ _)) =>
      simp_all [check, synth]
    | .tabs k e₀ =>
      match t with
      | .forall k' t₀ =>
        simp only [check] at hcheck
        split at hcheck
        · rename_i hk
          subst hk
          exact Check.tabs rfl (TVar.fresh_not_mem _ _) (check_sound κ Γ _ _ c hcheck hent)
        · simp at hcheck
      | .refine _ _ | .arrow _ _ | .prod _ _ | .data _ _ _ _ => simp_all [check, synth]
    | .tapp e₀ s₀ =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth de Γ (.tapp e₀ s₀) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .fix e =>
      match t with
      | .refine _ _ | .forall _ _ | .prod _ _ | .data _ _ _ _ => simp_all [check, synth]
      | .arrow s1 t1 =>
        simp only [check] at hcheck
        have hfF := EVar.fresh_not_mem (TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s1.fv ++ t1.fv)
        generalize EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s1.fv ++ t1.fv) = f at hfF hcheck
        have hxF := EVar.fresh_not_mem (TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s1.fv ++ t1.fv ++ [f])
        generalize EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s1.fv ++ t1.fv ++ [f]) = x
          at hxF hcheck
        split at hcheck
        · rename_i c₁ hc₁
          injection hcheck with hc
          subst hc
          refine Check.fix _ (fun a ha => ?_) hfF hxF (check_sound κ _ _ _ _ hc₁ ?_)
          · split at ha
            · exact TEnv.genVars_fresh ha
            · simp at ha
          intro γ hmγ
          have hcγ := hent γ hmγ.tail.tail
          have hxs : x ∉ s1.fv := by
            simp only [List.mem_append, not_or] at hxF; exact hxF.1.1.2
          exact implyBind_elim hmγ hxs hcγ
        · simp at hcheck
    | .ctor C j τs e₀ =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth de Γ (.ctor C j τs e₀) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub de Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .pair e₁ e₂ =>
      by_cases hp : ∃ x s t', e₁ = .fvar x ∧ t = .prod s t'
      · obtain ⟨x, s, t', rfl, rfl⟩ := hp
        simp only [check] at hcheck
        split at hcheck
        · simp at hcheck
        · rename_i hxt
          split at hcheck
          · rename_i c₁ c₂ h₁ h₂
            injection hcheck with hc
            subst hc
            have h₁' : check de Γ (.fvar x) s = some c₁ := by simp only [check]; exact h₁
            exact Check.pair (check_sound κ Γ _ _ c₁ h₁' fun γ hm => (hent γ hm).1) hxt
              (check_sound κ Γ _ _ c₂ h₂ fun γ hm => (hent γ hm).2)
          · simp at hcheck
      · exfalso
        have hnone : check de Γ (.pair e₁ e₂) t = none := by
          cases e₁ <;> cases t <;> simp_all [check, synth]
        simp_all
    | .split e₀ body =>
      simp only [check] at hcheck
      cases hs : synth de Γ e₀ with
      | none => simp [hs] at hcheck
      | some p =>
        obtain ⟨c₀, t₀⟩ := p
        rw [hs] at hcheck
        cases t₀ with
        | prod s t₁ =>
          simp only at hcheck
          have hxF := EVar.fresh_not_mem
            (TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t₁.fv ++ t.fv)
          generalize EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t₁.fv ++ t.fv) = x
            at hxF hcheck
          have hyF := EVar.fresh_not_mem
            (TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t₁.fv ++ t.fv ++ [x])
          generalize EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t₁.fv ++ t.fv ++ [x])
            = y at hyF hcheck
          split at hcheck
          · rename_i c' hc'
            injection hcheck with hc
            subst hc
            have hxs : x ∉ s.fv := by
              simp only [List.mem_append, not_or] at hxF; exact hxF.1.1.2
            have hyt : y ∉ (t₁.openVar 0 x).fv := by
              intro hmem
              simp only [List.mem_append, List.mem_singleton, not_or] at hyF
              rcases Ty.fv_openVar t₁ hmem with h | h
              · exact hyF.1.1.2 h
              · exact hyF.2 h
            refine Check.split (synth_sound κ Γ e₀ c₀ _ hs fun γ hm => (hent γ hm).1) hxF hyF
              (check_sound κ _ _ _ _ hc' ?_)
            intro γ hmγ
            have hcγ := (hent γ hmγ.tail.tail).2
            exact implyBind_elim hmγ hyt (implyBind_elim hmγ.tail hxs hcγ)
          · simp at hcheck
        | refine _ _ | arrow _ _ | «forall» _ _ | data _ _ _ _ => simp at hcheck
    | .case e₀ m alts =>
      simp only [check] at hcheck
      cases hs : synth de Γ e₀ with
      | none => simp [hs] at hcheck
      | some p =>
        obtain ⟨c₀, t₀⟩ := p
        rw [hs] at hcheck
        cases t₀ with
        | data C n args =>
          simp only at hcheck
          split at hcheck
          · rename_i hcond
            split at hcheck
            · rename_i cs hcs
              injection hcheck with hc
              subst hc
              let zs : Fin m → EVar := fun j =>
                match de.payload? C j.val with
                | some P => EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ (alts j).fv ++ t.fv ++
                    (de.altTy C j.val e₀.var? (Ty.instTys (List.ofFn args) P)).fv)
                | none => ""
              have hzs : ∀ (j : Fin m) P, de.payload? C j.val = some P →
                  zs j = EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ (alts j).fv ++ t.fv ++
                    (de.altTy C j.val e₀.var? (Ty.instTys (List.ofFn args) P)).fv) := fun j P hP => by
                simp only [zs, hP]
              refine Check.case zs
                (synth_sound κ Γ e₀ c₀ _ hs fun γ hm => (hent γ hm).1) hcond.1 hcond.2
                (fun j => ?_) (fun j P hP => ?_) ?_
              · obtain ⟨P, hP⟩ := DEnv.payload?_of_lt hcond.1 j.isLt
                rw [hzs j P hP]
                intro hmem
                exact EVar.fresh_not_mem _ (List.mem_append_left _ hmem)
              · rw [hzs j P hP]
                intro hmem
                exact EVar.fresh_not_mem _ (List.mem_append_right _ hmem)
              intro j P hP
              obtain ⟨cj, hfj, himp⟩ := Cstr.conjAll_some hcs j (List.mem_finRange j)
              simp only [hP] at hfj
              split at hfj
              · rename_i cj' hcj
                injection hfj with hfj
                subst hfj
                have hzt : zs j ∉ (de.altTy C j.val e₀.var? (Ty.instTys (List.ofFn args) P)).fv := by
                  rw [hzs j P hP]
                  intro hmem
                  exact EVar.fresh_not_mem _ (List.mem_append_right _ hmem)
                have := Exp.skel_case_lt e₀ m alts j
                rw [← hzs j P hP] at hcj
                exact check_sound κ _ _ _ _ hcj fun γ hm =>
                  implyBind_elim hm hzt (by rw [hzs j P hP]; exact himp κ γ (hent γ hm.tail).2)
              · simp at hfj
            · simp at hcheck
          · simp at hcheck
        | refine _ _ | arrow _ _ | «forall» _ _ | prod _ _ => simp at hcheck
  termination_by 2 * e.skel + 1
end

/-! ## Bidirectional → declarative -/

mutual
  theorem synth_to_hastype {de κ Γ e t}
      (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (h : Synth de κ Γ e t) :
      Hastype de κ Γ e t ∧ Ty.WFBVars t := by
    match h with
    | .var hl =>
      have htw := hΓ.lookup hl
      exact ⟨.var hl htw, Ty.WFBVars_self _ _ _ htw⟩
    | .int_const => exact ⟨.int_const, Ty.WFBVars_prim _⟩
    | .bool_const => exact ⟨.bool_const, Ty.WFBVars_primBool _⟩
    | .ann hck =>
      simp only [Exp.WFBVars] at hE
      have htw := hE.1
      have hht := check_to_hastype hΓ hE.2 htw hck
      exact ⟨.ann hht htw, htw⟩
    | .app hsy hck hyfv =>
      simp only [Exp.WFBVars] at hE
      have ⟨hht1, htw_arr⟩ := synth_to_hastype hΓ hE.1 hsy
      have htw_s_t := htw_arr
      simp only [Ty.WFBVars, Ty.WFBVarCtx] at htw_s_t
      have hht2 := check_to_hastype hΓ (by simp [Exp.WFBVars]) htw_s_t.1 hck
      refine ⟨.app hht1 hht2 hyfv, ?_⟩
      exact Ty.WFBVarCtx_openVar_last _ [] _ _ htw_s_t.2
    | .add_var hxlk hylk =>
      exact ⟨.add_var hxlk hylk, Ty.WFBVars_add_result _ _⟩
    | .leq_var hxlk hylk hb =>
      exact ⟨.leq_var hxlk hylk hb, Ty.WFBVars_leq_result _ _ _⟩
    | .not_var hxlk =>
      exact ⟨.not_var hxlk, Ty.WFBVars_not_result _⟩
    | .and_var hxlk hylk =>
      exact ⟨.and_var hxlk hylk, Ty.WFBVars_and_result _ _⟩
    | .tapp hsy hk h1 h2 h3 =>
      simp only [Exp.WFBVars] at hE
      have ⟨hht, _⟩ := synth_to_hastype hΓ hE hsy
      exact ⟨.tapp hht hk h1 h2 h3, Ty.wfB_WFBVars _ h3⟩
    | .ctor hP hok hck =>
      simp only [Exp.WFBVars] at hE
      have hht := check_to_hastype hΓ hE
        (Ty.wfB_WFBVars _ (DEnv.instOK_payload_wfB hok hP)) hck
      exact ⟨.ctor hP hok hht, DEnv.instOK_WFBVars hok (DEnv.ctorRefine_noBVar _ _ _ _)⟩

  theorem check_to_hastype {de κ Γ e t}
      (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (ht : Ty.WFBVars t)
      (h : Check de κ Γ e t) :
      Hastype de κ Γ e t := by
    match h with
    | .unreach hent =>
      exact .unreach hent ht
    | .sub hsy hsub =>
      have ⟨hht, _⟩ := synth_to_hastype hΓ hE hsy
      exact .sub hht hsub ht
    | .lam hfresh hck =>
      rename_i e s₁ s₂ x
      have ht_split : Ty.WFBVarCtx [] s₁ ∧ Ty.WFBVarCtx [s₁.optBase] s₂ := by
        simp only [Ty.WFBVars, Ty.WFBVarCtx] at ht; exact ht
      have hs₂_open_wfb : Ty.WFBVars (s₂.openVar 0 x) :=
        Ty.WFBVarCtx_openVar_last s₂ [] s₁.optBase x ht_split.2
      have hΓ_ext : TEnv.WFBVars ((x, s₁) :: Γ) := hΓ.cons ht_split.1
      have hE_ext : Exp.WFBVars (e.openVar 0 x) := by
        simp only [Exp.WFBVars] at hE; exact (Exp.WFBVars_openVar e 0 x).mpr hE
      exact .lam ht hfresh (check_to_hastype hΓ_ext hE_ext hs₂_open_wfb hck)
    | .letin hsy hfresh hck =>
      rename_i e₁ e₂ s x
      simp only [Exp.WFBVars] at hE
      have ⟨hht1, hs_wfb⟩ := synth_to_hastype hΓ hE.1 hsy
      have hΓ_ext : TEnv.WFBVars ((x, s) :: Γ) := hΓ.cons hs_wfb
      have hE_ext : Exp.WFBVars (e₂.openVar 0 x) :=
        (Exp.WFBVars_openVar e₂ 0 x).mpr hE.2
      exact .letin ht hht1 hfresh (check_to_hastype hΓ_ext hE_ext ht hck)
    | .ite hlk hfresh hck1 hck2 =>
      rename_i x y e₁ e₂ r
      simp only [Exp.WFBVars] at hE
      obtain ⟨_, hE1, hE2⟩ := hE
      -- The branch guard `{ν | x = const}` references `x` free and is kvar-free
      -- with no bvars, so it is WFBVars outright.
      have hstr_wfb : ∀ (const : Bool), Ty.WFBVars (.refine .bool
          (.fmla (.eq .bool (.fvar .bool x) (.const .bool const)))) := by
        intro const
        simp [Ty.WFBVars, Ty.WFBVarCtx, Refinement.hasBVar, Formula.hasBVar, Term.hasBVar]
      -- Extended TEnv.WFBVars for the fresh-guard true / false branches.
      have hΓ1 : TEnv.WFBVars ((y, .refine .bool
          (.fmla (.eq .bool (.fvar .bool x) (.const .bool true)))) :: Γ) :=
        hΓ.cons (hstr_wfb true)
      have hΓ2 : TEnv.WFBVars ((y, .refine .bool
          (.fmla (.eq .bool (.fvar .bool x) (.const .bool false)))) :: Γ) :=
        hΓ.cons (hstr_wfb false)
      have hht1 := check_to_hastype hΓ1 hE1 ht hck1
      have hht2 := check_to_hastype hΓ2 hE2 ht hck2
      exact .ite hlk hfresh ht hht1 hht2
    | .fix as has hf hx hck =>
      rename_i e s t f x
      have ht_split : Ty.WFBVarCtx [] s ∧ Ty.WFBVarCtx [s.optBase] t := by
        simp only [Ty.WFBVars, Ty.WFBVarCtx] at ht; exact ht
      have hΓ_ext : TEnv.WFBVars ((x, s) :: (f, Ty.gen as (.arrow s t)) :: Γ) :=
        (hΓ.cons (Ty.WFBVars_gen as _ ht)).cons ht_split.1
      have hE_ext : Exp.WFBVars ((e.openVar 1 f).openVar 0 x) := by
        simp only [Exp.WFBVars] at hE; simp [hE]
      exact .fix as has ht hf hx (check_to_hastype hΓ_ext hE_ext
        (Ty.WFBVarCtx_openVar_last t [] s.optBase x ht_split.2) hck)
    | .tabs hk hfresh hck =>
      rename_i k e t a
      simp only [Exp.WFBVars] at hE
      have htb : Ty.WFBVars t := by simpa [Ty.WFBVars, Ty.WFBVarCtx] using ht
      exact .tabs ht hk hfresh (check_to_hastype hΓ (Exp.WFBVars_openTv e 0 a hE)
        (Ty.WFBVars_openTv t 0 a htb) hck)
    | .pair hck₁ hxt hck₂ =>
      rename_i x e₂ s t
      simp only [Exp.WFBVars] at hE
      have ht_split : Ty.WFBVarCtx [] s ∧ Ty.WFBVarCtx [s.optBase] t := by
        simp only [Ty.WFBVars, Ty.WFBVarCtx] at ht; exact ht
      exact .pair ht (check_to_hastype hΓ (by simp [Exp.WFBVars]) ht_split.1 hck₁) hxt
        (check_to_hastype hΓ hE.2 (Ty.WFBVarCtx_openVar_last t [] s.optBase x ht_split.2) hck₂)
    | .split hsy hx hy hck =>
      rename_i e body s t x y
      simp only [Exp.WFBVars] at hE
      have ⟨hht, hpw⟩ := synth_to_hastype hΓ hE.1 hsy
      have hp_split : Ty.WFBVarCtx [] s ∧ Ty.WFBVarCtx [s.optBase] t := by
        simp only [Ty.WFBVars, Ty.WFBVarCtx] at hpw; exact hpw
      have hΓ_ext : TEnv.WFBVars ((y, t.openVar 0 x) :: (x, s) :: Γ) :=
        (hΓ.cons hp_split.1).cons (Ty.WFBVarCtx_openVar_last t [] s.optBase x hp_split.2)
      have hE_ext : Exp.WFBVars ((body.openVar 1 x).openVar 0 y) := by simp [hE.2]
      exact .split ht hht hx hy (check_to_hastype hΓ_ext hE_ext ht hck)
    | .case zs hsy hm hok hz hzP hcks =>
      simp only [Exp.WFBVars] at hE
      have ⟨hht, _⟩ := synth_to_hastype hΓ hE.1 hsy
      exact .case zs ht hht hm hok hz hzP fun j P hP =>
        check_to_hastype (hΓ.cons (DEnv.altTy_WFBVars _ _ _ _
            (Ty.wfB_WFBVars _ (DEnv.instOK_payload_wfB hok hP))))
          ((Exp.WFBVars_openVar _ _ _).mpr (hE.2 j)) ht (hcks j P hP)
end

theorem synth_decl_sound {de : DEnv} (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Cstr) (t : Ty)
    (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) :
    synth de Γ e = some (c, t) → Entail κ Γ (c.interp κ) → Hastype de κ Γ e t :=
  fun h hc => (synth_to_hastype hΓ hE (synth_sound κ Γ e c t h hc)).1

theorem check_decl_sound {de : DEnv} (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Cstr)
    (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) :
    check de Γ e t = some c → Entail κ Γ (c.interp κ) → Hastype de κ Γ e t :=
  fun h hc => check_to_hastype hΓ hE ht (check_sound κ Γ e t c h hc)

theorem topVC_decl_sound (κ : KEnv) (e : Exp) (t : Ty) {de : DEnv}
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) :
    topVC κ [] e t de → Hastype de κ [] e t := by
  unfold topVC
  cases hck : check de [] e t with
  | none   => intro hf; exact hf.elim
  | some c =>
    intro h
    exact check_decl_sound κ [] e t c TEnv.WFBVars.empty hE ht hck (Entail.emp h)
