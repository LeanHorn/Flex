import Flex.VCG.STLC.VCGen
import Flex.VCG.STLC.Declarative

open STLC

/-! # VCGen Soundness (skeleton, κ-indexed)

  Algorithmic VC generation is sound w.r.t. the bidirectional and declarative
  typing rules. Every judgement is now parameterized by `κ : KEnv`.

-/

namespace STLC

/-- `implyBindCstr` over a refined binding interprets as a `push`-form
    quantified bind, provided `x` is fresh for `r`. -/
theorem implyBindCstr_interp (κ : KEnv) (x : EVar) (b : Base) (r : Refinement)
    (c : Cstr) (γ : REnv) (hx : x ∉ r.fv) :
    (implyBindCstr x (.refine b r) c).interp κ γ ↔
    ∀ v : b.interp, Refinement.interp κ r (γ.push (Val.inj b v)) →
      c.interp κ (REnv.update b γ x v) := by
  simp only [implyBindCstr, Cstr.interp]
  constructor <;> intro h v
  · intro hr
    exact h v ((Refinement.interp_openBVar κ r γ x (Val.inj b v) 0 (Nat.zero_le _) hx).mpr hr)
  · intro hr
    exact h v ((Refinement.interp_openBVar κ r γ x (Val.inj b v) 0 (Nat.zero_le _) hx).mp hr)

/-- Semantic (`push`-form) reading of a bind; keeps the soundness proofs'
    `cases s` structure. -/
def implyBindSem (κ : KEnv) (x : EVar) (t : Ty) (c : Cstr) (γ : REnv) : Prop :=
  match t with
  | .refine b r => ∀ v : b.interp,
                     Refinement.interp κ r (γ.push (Val.inj b v)) →
                       c.interp κ (REnv.update b γ x v)
  | .arrow _ _  => c.interp κ γ

/-- `implyBindCstr` interprets as `implyBindSem`, for *any* binding type
    (provided `x` is fresh for the binding's refinement). -/
theorem implyBindCstr_interp_gen (κ : KEnv) (x : EVar) (t : Ty) (c : Cstr)
    (γ : REnv) (hx : x ∉ t.fv) :
    (implyBindCstr x t c).interp κ γ ↔ implyBindSem κ x t c γ := by
  cases t with
  | refine b r =>
      exact implyBindCstr_interp κ x b r c γ (by simpa [Ty.fv] using hx)
  | arrow s t => simp only [implyBindCstr, implyBindSem]

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


theorem sub_sound (κ : KEnv) (Γ : TEnv) (s t : Ty) (c : Cstr) :
    sub Γ s t = some c → Entail κ Γ (c.interp κ) → Subtyp κ Γ s t := by
  intro hsub hent
  match s, t with
  | .refine .int r1, .refine .int r2 =>
    simp only [sub, Option.some.injEq] at hsub
    subst hsub
    let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r1.fv ++ r2.fv)
    have hfr : x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ r1.fv ++ r2.fv := EVar.fresh_not_mem _
    have hx1 : x ∉ r1.fv := by simp only [List.mem_append, not_or] at hfr; exact hfr.1.2
    -- The emitted constraint is already the *opened* form the rule expects; close
    -- the extension binder with `Entail.ext` and open r₁'s ν back to `x`.
    refine Subtyp.refine hfr (Entail.ext ?_)
    intro γ hm v h1
    have hc := hent γ hm; simp only [Cstr.interp] at hc
    exact hc v ((Refinement.interp_openBVar κ r1 γ x (Val.inj .int v) 0 (Nat.zero_le _) hx1).mpr h1)
  | .refine .bool r1, .refine .bool r2 =>
    simp only [sub, Option.some.injEq] at hsub
    subst hsub
    let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r1.fv ++ r2.fv)
    have hfr : x ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ r1.fv ++ r2.fv := EVar.fresh_not_mem _
    have hx1 : x ∉ r1.fv := by simp only [List.mem_append, not_or] at hfr; exact hfr.1.2
    refine Subtyp.refine hfr (Entail.ext ?_)
    intro γ hm v h1
    have hc := hent γ hm; simp only [Cstr.interp] at hc
    exact hc v ((Refinement.interp_openBVar κ r1 γ x (Val.inj .bool v) 0 (Nat.zero_le _) hx1).mpr h1)
  | .arrow s1 t1, .arrow s2 t2 =>
    simp_all [sub]
    let w := (EVar.fresh (Γ.dom ++ (Γ.tyFv ++ (s1.fv ++ (s2.fv ++ (t1.fv ++ t2.fv))))))
    have hwd : w = EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ s1.fv ++ s2.fv ++ t1.fv ++ t2.fv) := by grind
    obtain ⟨c₁, hc₁⟩ : ∃ c₁, sub Γ s2 s1 = some c₁ := by
      rcases Option.eq_none_or_eq_some (sub Γ s2 s1) with eqn | eqs
      · simp_all
      · assumption
    obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub ((w, s2) :: Γ) (t1.openVar 0 w) (t2.openVar 0 w) = some c₂ := by
      rcases Option.eq_none_or_eq_some (sub ((w, s2) :: Γ) (t1.openVar 0 w) (t2.openVar 0 w)) with eqn | eqs
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
      have hΓγ : ModelsEnv κ γ Γ := by
        cases s2 with | refine _ _ => exact hm.2.2 | arrow _ _ => exact hm
      rw [←hsub] at hent
      have hcγ := hent γ hΓγ
      simp only [Cstr.interp] at hcγ
      cases s2 with
      | refine b r =>
        have hwr : w ∉ r.fv := by
          have := hw; simp only [Ty.fv, List.mem_append, not_or] at this
          exact this.1.1.2
        have hb := (implyBindCstr_interp κ w b r c₂ γ hwr).mp hcγ.2
        have hsat := hm.2.1
        rw [REnv.lookup_eq_inj_get b γ w hm.1] at hsat
        have h := hb (REnv.get b γ w) hsat
        rw [REnv.update_self b γ w hm.1] at h ; exact h
      | arrow _ _ => exact hcγ.2
    · apply sub_sound κ Γ s2 s1 c₁ hc₁
      intro γ hm
      rw [←hsub] at hent
      exact (hent γ hm).1
  | .refine _ _ , .arrow _ _ | .arrow _ _, .refine _ _ | .refine .int _, .refine .bool _ | .refine .bool _, .refine .int _=>
    simp_all [sub]
  termination_by s.skel + t.skel

/-! ## Synth / Check soundness (mutual) -/

mutual
  theorem synth_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Cstr) (t : Ty) :
      synth Γ e = some (c, t) → Entail κ Γ (c.interp κ) → Synth κ Γ e t := by
    intro hsynth hent
    match e with
    | .bvar i =>
      simp_all [synth]
    | .fvar x =>
      simp_all [synth]
      rcases hsynth with ⟨t', ⟨hl, hc, hs⟩⟩
      match t' with
      | .refine .int r | .refine .bool r =>
        simp_all ; rw [←hs, ←self]
        constructor
        assumption
      | .arrow _ _ =>
        simp_all ; rw [←hs, ←self] ; rw [←hs] at hl
        constructor ; assumption
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
    | .lam e | .letin e1 e2 | .ite _ _ _  =>
      simp_all [synth]
    | .app e1 (.fvar y) =>
      simp_all [synth]
      obtain ⟨c1, s', t', hse⟩ : ∃ c s t, synth Γ e1 = some (c, .arrow s t) := by grind
      obtain ⟨c2, hy⟩ : ∃ c, check Γ (.fvar y) s' = some c := by grind
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
      obtain ⟨c', hc⟩ : ∃ c, check Γ e1 t' = some c := by grind
      simp_all
      exact Synth.ann (check_sound κ Γ e1 t c hc hent)
    | .leq (.fvar x) (.fvar y) | .add (.fvar x) (.fvar y) =>
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
      => simp_all [synth]
  termination_by 2*e.skel

  theorem check_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Cstr) :
      check Γ e t = some c → Entail κ Γ (c.interp κ) → Check κ Γ e t := by
    intro hcheck hent
    match e with
    | .unreach =>
      simp only [check] at hcheck
      injection hcheck with hc
      subst hc
      exact Check.unreach hent
    | .bvar i =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.bvar i) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .fvar x =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.fvar x) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .iconst i =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.iconst i) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .bconst b =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.bconst b) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .add e1 e2 =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.add e1 e2) = some (c₁, s) := by grind
      simp_all
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound κ Γ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .ite (.fvar cn) bt bf =>
      simp_all [check]
      obtain ⟨r, hr⟩ : ∃ r, List.lookup cn Γ = some (.refine .bool r) := by grind
      simp_all
      obtain ⟨c₁, c₂, hc₁, hc₂⟩ : ∃ c₁ c₂,
          (check ((EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ bt.fv ++ bf.fv ++ t.fv ++ [cn]),
                   Ty.refine Base.bool (.fmla (.eq .bool (.fvar .bool cn) (.const .bool true)))) :: Γ) bt t = some c₁) ∧
          (check ((EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ bt.fv ++ bf.fv ++ t.fv ++ [cn]),
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
        apply Entail.ext
        intro γ hm
        have hb := (hent γ hm).1
        rw [implyBindCstr_interp_gen κ _ _ c₁ γ
              (by simp only [Ty.fv, Refinement.fv, Formula.fv, Term.fv, List.append_nil,
                    List.mem_append, List.mem_singleton, not_or] at hyf ⊢
                  grind)] at hb
        simpa only [implyBindSem] using hb
      · simp only [List.append_assoc]
        apply check_sound _ _ _ _ _ hc₂
        apply Entail.ext
        intro γ hm
        have hb := (hent γ hm).2
        rw [implyBindCstr_interp_gen κ _ _ c₂ γ
              (by simp only [Ty.fv, Refinement.fv, Formula.fv, Term.fv, List.append_nil,
                    List.mem_append, List.mem_singleton, not_or] at hyf ⊢
                  grind)] at hb
        simpa only [implyBindSem] using hb
    | .lam e =>
      match t with
      | .refine _ r =>
        simp_all [check, synth]
      | .arrow s1 t1 =>
        simp_all [check]
        -- Use the LITERAL right-associated fresh expression (matches simp's normal form
        -- so the second simp_all can substitute hc₁ into hcheck).
        obtain ⟨c₁, hc₁⟩ : ∃ c₁, check ((EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++ TEnv.tyFv Γ)))) , s1) :: Γ)
            (Exp.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++ TEnv.tyFv Γ ))))) e)
            (Ty.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++ TEnv.tyFv Γ ))))) t1) = some c₁ := by grind
        simp_all
        let L₀ : List EVar := TEnv.dom Γ ++ (e.fv ++ (s1.fv ++ (t1.fv ++ TEnv.tyFv Γ )))
        let x₀ : EVar := EVar.fresh L₀
        -- 1. Body proof at the specific fresh witness `x₀`.
        have hbody₀ :
            Check κ ((x₀, s1) :: Γ) (Exp.openVar 0 x₀ e) (Ty.openVar 0 x₀ t1) := by
          apply check_sound κ _ _ _ _ hc₁
          intro γ hmγ
          have hΓγ : ModelsEnv κ γ Γ := by
            cases s1 with
            | refine _ _ => exact hmγ.2.2
            | arrow _ _  => exact hmγ
          have hcγ : c.interp κ γ := hent γ hΓγ
          rw [← hcheck] at hcγ
          have hx₀s : x₀ ∉ s1.fv := by
            have h := EVar.fresh_not_mem L₀
            simp only [L₀, List.mem_append, not_or] at h
            exact h.2.2.1
          rw [implyBindCstr_interp_gen κ x₀ s1 c₁ γ hx₀s] at hcγ
          simp only [implyBindSem] at hcγ
          cases s1 with
          | refine b r =>
            have hsat : Refinement.interp κ r (γ.push (γ.lookup x₀)) := hmγ.2.1
            rw [REnv.lookup_eq_inj_get b γ x₀ hmγ.1] at hsat
            have h := hcγ (REnv.get b γ x₀) hsat
            rw [REnv.update_self b γ x₀ hmγ.1] at h
            exact h
          | arrow _ _ => exact hcγ
        have hfresh₀ : x₀ ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s1.fv ++ t1.fv := by
          have h := EVar.fresh_not_mem L₀
          simp only [L₀, List.mem_append, not_or] at h ⊢
          grind
        exact Check.lam hfresh₀ hbody₀
    | .letin e1 e2 =>
      -- check Γ (.letin e1 e2) t algorithm: synth e1 → (c₁, s); check ((x₀, s) :: Γ) (e2.openVar 0 x₀) t = some c₂
      simp_all [check]
      obtain ⟨c₁, s, hsynth⟩ : ∃ c₁ s, synth Γ e1 = some (c₁, s) := by grind
      -- Use LITERAL right-associated fresh expression (matches simp's normal form).
      obtain ⟨c₂, hcheck₂⟩ : ∃ c₂, check ((EVar.fresh (TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++ TEnv.tyFv Γ)))) , s) :: Γ)
          (Exp.openVar 0 (EVar.fresh (TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++ TEnv.tyFv Γ))))) e2) t = some c₂ := by grind
      simp_all
      let L₀ : List EVar := TEnv.dom Γ ++ (e2.fv ++ (s.fv ++ (t.fv ++ TEnv.tyFv Γ)))
      let x₀ : EVar := EVar.fresh L₀
      -- 1. Synth at e1 via synth_sound.
      have hsy : Synth κ Γ e1 s := by
        apply synth_sound _ _ _ _ _ hsynth
        intro γ hγ
        have := hent γ hγ
        rw [←hcheck] at this
        exact this.1
      -- 2. Body Check at x₀ via check_sound.
      have hbody₀ : Check κ ((x₀, s) :: Γ) (Exp.openVar 0 x₀ e2) t := by
        apply check_sound _ _ _ _ _ hcheck₂
        intro γ hmγ
        have hΓγ : ModelsEnv κ γ Γ := by
          cases s with
          | refine _ _ => exact hmγ.2.2
          | arrow _ _  => exact hmγ
        have hcγ : c.interp κ γ := hent γ hΓγ
        rw [← hcheck] at hcγ
        have hx₀s : x₀ ∉ s.fv := by
          have h := EVar.fresh_not_mem L₀
          simp only [L₀, List.mem_append, not_or] at h
          exact h.2.2.1
        have himply := (implyBindCstr_interp_gen κ x₀ s c₂ γ hx₀s).mp hcγ.2
        simp only [implyBindSem] at himply
        cases s with
        | refine b r =>
          have hsat : Refinement.interp κ r (γ.push (γ.lookup x₀)) := hmγ.2.1
          rw [REnv.lookup_eq_inj_get b γ x₀ hmγ.1] at hsat
          have h := himply (REnv.get b γ x₀) hsat
          rw [REnv.update_self b γ x₀ hmγ.1] at h
          exact h
        | arrow _ _ => exact himply
      have hfresh₀ : x₀ ∉ TEnv.dom Γ ++ TEnv.tyFv Γ ++ e2.fv ++ s.fv ++ t.fv  := by
        have h := EVar.fresh_not_mem L₀
        simp only [L₀, List.mem_append, not_or] at h ⊢
        grind
      exact Check.letin hsy hfresh₀ hbody₀
    | .leq (.fvar x) (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ ((Exp.fvar x).leq (Exp.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .ann e t' =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ (.ann e t') = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .app e1 (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s, hc₁⟩ : ∃ c₁ s, synth Γ (.app e1 (.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .not (.fvar x) =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.not (.fvar x)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
      simp_all ; rw [←hcheck] at hent
      exact Check.sub (synth_sound _ _ _ _ _ hc₁ fun γ hm => (hent γ hm).1)
                      (sub_sound _ _ _ _ _ hc₂ fun γ hm => (hent γ hm).2)
    | .and (.fvar x) (.fvar y) =>
      simp_all [check]
      obtain ⟨c₁, s', hc₁⟩ : ∃ c₁ s, synth Γ (.and (.fvar x) (.fvar y)) = some (c₁, s) := by grind
      obtain ⟨c₂, hc₂⟩ : ∃ c₂, sub Γ s' t = some c₂ := by grind
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
    | (.app _ (.iconst _)) | (.app _ (.bvar _)) | (.app _ .unreach)=>
      simp_all [check, synth]
  termination_by 2 * e.skel + 1
end

/-! ## Bidirectional → declarative -/

mutual
  theorem synth_to_hastype {κ Γ e t}
      (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (h : Synth κ Γ e t) :
      Hastype κ Γ e t ∧ Ty.WFBVars t := by
    match h with
    | .var hl =>
      have htw := hΓ.lookup hl
      exact ⟨.var hl htw, Ty.WFBVars_self _ _ htw⟩
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
    | .leq_var hxlk hylk =>
      exact ⟨.leq_var hxlk hylk, Ty.WFBVars_leq_result _ _⟩
    | .not_var hxlk =>
      exact ⟨.not_var hxlk, Ty.WFBVars_not_result _⟩
    | .and_var hxlk hylk =>
      exact ⟨.and_var hxlk hylk, Ty.WFBVars_and_result _ _⟩

  theorem check_to_hastype {κ Γ e t}
      (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (ht : Ty.WFBVars t)
      (h : Check κ Γ e t) :
      Hastype κ Γ e t := by
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
end

theorem synth_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (c : Cstr) (t : Ty)
    (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) :
    synth Γ e = some (c, t) → Entail κ Γ (c.interp κ) → Hastype κ Γ e t :=
  fun h hc => (synth_to_hastype hΓ hE (synth_sound κ Γ e c t h hc)).1

theorem check_decl_sound (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (c : Cstr)
    (hΓ : TEnv.WFBVars Γ) (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) :
    check Γ e t = some c → Entail κ Γ (c.interp κ) → Hastype κ Γ e t :=
  fun h hc => check_to_hastype hΓ hE ht (check_sound κ Γ e t c h hc)

theorem topVC_decl_sound (κ : KEnv) (e : Exp) (t : Ty)
    (hE : Exp.WFBVars e) (ht : Ty.WFBVars t) :
    topVC κ [] e t → Hastype κ [] e t := by
  unfold topVC
  cases hck : check [] e t with
  | none   => intro hf; exact hf.elim
  | some c =>
    intro h
    exact check_decl_sound κ [] e t c TEnv.WFBVars.empty hE ht hck (Entail.emp h)
