import Flex.VCG.STLC.Checker.WellFormed
import Flex.VCG.STLC.Proofs.Model

open STLC

/-! # Lemmas about the syntactic operations -/

namespace STLC

theorem Term.fv_openBVar {k : Nat} {x z : EVar} : ∀ {b : Base} (t : Term b),
    z ∈ (t.openBVar k x).fv → z ∈ t.fv ∨ z = x := by
  intro b t
  induction t with
  | bvar b j =>
    simp only [Term.openBVar]
    split
    · simp [Term.fv]
    · split <;> simp [Term.fv]
  | const => simp [Term.openBVar, Term.fv]
  | fvar => simp only [Term.openBVar, Term.fv, List.mem_singleton]; exact Or.inl
  | mbvar m j =>
    simp only [Term.openBVar]
    split
    · simp [Term.fv]
    · split <;> simp [Term.fv]
  | mfvar => simp only [Term.openBVar, Term.fv, List.mem_singleton]; exact Or.inl
  | ibvar j =>
    simp only [Term.openBVar]
    split
    · simp [Term.fv]
    · split <;> simp [Term.fv]
  | bbvar j =>
    simp only [Term.openBVar]
    split
    · simp [Term.fv]
    · split <;> simp [Term.fv]
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | leqI _ _ ih₁ ih₂ =>
    simp only [Term.openBVar, Term.fv, List.mem_append]
    rintro (h | h)
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | ite _ c t e ihc iht ihe =>
    simp only [Term.openBVar, Term.fv, List.mem_append]
    rintro ((h | h) | h)
    · rcases ihc h with h | h <;> simp [h]
    · rcases iht h with h | h <;> simp [h]
    · rcases ihe h with h | h <;> simp [h]
  | not _ ih => simpa [Term.openBVar, Term.fv] using ih

theorem Formula.fv_openBVar {x z : EVar} (φ : Formula) : ∀ {k : Nat},
    z ∈ (φ.openBVar k x).fv → z ∈ φ.fv ∨ z = x := by
  induction φ with
  | tt | ff => simp [Formula.openBVar, Formula.fv]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro k
    simp only [Formula.openBVar, Formula.fv, List.mem_append]
    rintro (h | h)
    · rcases Term.fv_openBVar t₁ h with h | h <;> simp [h]
    · rcases Term.fv_openBVar t₂ h with h | h <;> simp [h]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro k
    simp only [Formula.openBVar, Formula.fv, List.mem_append]
    rintro (h | h)
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | not _ ih | ex _ _ ih | all _ _ ih => intro k h; exact ih h

theorem Refinement.fv_openBVar {k : Nat} {x z : EVar} (r : Refinement) :
    z ∈ (r.openBVar k x).fv → z ∈ r.fv ∨ z = x := by
  induction r with
  | fmla φ => exact Formula.fv_openBVar φ
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.fv, List.flatMap_map, List.mem_flatMap]
    rintro ⟨a, ha, h⟩
    rcases Term.fv_openBVar a.2 h with h | h
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr h
  | conj _ _ ih₁ ih₂ =>
    simp only [Refinement.openBVar, Refinement.fv, List.mem_append]
    rintro (h | h)
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]

theorem Ty.fv_openVar {x z : EVar} (t : Ty) : ∀ {k : Nat},
    z ∈ (t.openVar k x).fv → z ∈ t.fv ∨ z = x := by
  induction t with
  | refine b r => intro k h; exact Refinement.fv_openBVar r h
  | arrow _ _ ih₁ ih₂ | prod _ _ ih₁ ih₂ =>
    intro k
    simp only [Ty.openVar, Ty.fv, List.mem_append]
    rintro (h | h)
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | «forall» _ _ ih => intro k h; exact ih h
  | data C n args r ih =>
    intro k
    simp only [Ty.openVar, Ty.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
    rintro (⟨i, h⟩ | h)
    · rcases ih i h with h | h
      · exact Or.inl (Or.inl ⟨i, h⟩)
      · exact Or.inr h
    · rcases Refinement.fv_openBVar r h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem TEnv.WFBVars.empty : TEnv.WFBVars [] := by intros x t h ; trivial

/-- Cons preserves `TEnv.WFBVars` given the new binding has WFBVars type. -/
theorem TEnv.WFBVars.cons {Γ : TEnv} {x : EVar} {t : Ty}
    (hΓ : TEnv.WFBVars Γ) (ht : Ty.WFBVars t) :
    TEnv.WFBVars ((x, t) :: Γ) := by
  intro y s h
  simp only [List.mem_cons, Prod.mk.injEq] at h
  rcases h with ⟨_, hst⟩ | h
  · exact hst ▸ ht
  · exact hΓ y s h

/-- Lookup in a WFBVars context yields a WFBVars type. -/
theorem TEnv.WFBVars.lookup {Γ : TEnv} (hΓ : TEnv.WFBVars Γ) {x : EVar} {t : Ty}
    (hlk : Γ.lookup x = some t) : Ty.WFBVars t := by
  induction Γ with
  | nil => simp [List.lookup] at hlk
  | cons hd tl ih =>
    obtain ⟨y, s⟩ := hd
    simp only [List.lookup] at hlk
    by_cases hxy : x = y
    · have heq : (x == y) = true := by simp [hxy]
      rw [heq] at hlk
      have hst : s = t := Option.some.inj hlk
      subst hst
      exact hΓ y s (by simp)
    · have hne : (x == y) = false := by simp [hxy]
      rw [hne] at hlk
      have hΓ_tl : TEnv.WFBVars tl := fun z r h => hΓ z r (by simp [List.mem_cons, h])
      exact ih hΓ_tl hlk

/-! ### `hasBVar` under the shifting open

  A `BVar b i` occurs in `t.openBVar k x` iff it came from level `i` (below the
  opened level `k`) or from level `i+1` (at/above `k`, shifted down). This
  characterization drives `Ty.WFBVarCtx_openVar_last`. -/

theorem Term.hasBVar_openBVar {b'' : Base} (t : Term b'') (b : Base) (i k : Nat) (x : EVar) :
    Term.hasBVar b i (Term.openBVar k x t) ↔
      (i < k ∧ Term.hasBVar b i t) ∨ (k ≤ i ∧ Term.hasBVar b (i+1) t) := by
  induction t with
  | const _ _ => simp [Term.openBVar, Term.hasBVar]
  | bvar b' j =>
    by_cases hbb : b = b'
    · subst hbb
      by_cases hjk : j = k
      · subst hjk; simp [Term.openBVar, Term.hasBVar]; omega
      · by_cases hlt : k < j
        · simp [Term.openBVar, hjk, hlt, Term.hasBVar]; omega
        · simp [Term.openBVar, hjk, hlt, Term.hasBVar]; omega
    · by_cases hjk : j = k
      · subst hjk; simp [Term.openBVar, Term.hasBVar, hbb]
      · by_cases hlt : k < j
        · simp [Term.openBVar, hjk, hlt, Term.hasBVar, hbb]
        · simp [Term.openBVar, hjk, hlt, Term.hasBVar, hbb]
  | fvar _ _ => simp [Term.openBVar, Term.hasBVar]
  | mbvar m j => simp only [Term.openBVar]; split <;> (try split) <;> simp [Term.hasBVar]
  | mfvar _ _ => simp [Term.openBVar, Term.hasBVar]
  | ibvar j => simp only [Term.openBVar]; split <;> (try split) <;> simp [Term.hasBVar]
  | bbvar j => simp only [Term.openBVar]; split <;> (try split) <;> simp [Term.hasBVar]
  | add t₁ t₂ ih1 ih2 => simp only [Term.openBVar, Term.hasBVar, ih1, ih2]; grind
  | leqI t₁ t₂ ih1 ih2 => simp only [Term.openBVar, Term.hasBVar, ih1, ih2]; grind
  | ite _ c t e ihc iht ihe => simp only [Term.openBVar, Term.hasBVar, ihc, iht, ihe]; grind
  | not t ih  => simp only [Term.openBVar, Term.hasBVar, ih]
  | and t₁ t₂ ih1 ih2 => simp only [Term.openBVar, Term.hasBVar, ih1, ih2]; grind

theorem Formula.hasBVar_openBVar (φ : Formula) (b : Base) (i k : Nat) (x : EVar) :
    Formula.hasBVar b i (φ.openBVar k x) ↔
      (i < k ∧ Formula.hasBVar b i φ) ∨ (k ≤ i ∧ Formula.hasBVar b (i+1) φ) := by
  induction φ generalizing i k with
  | tt | ff => simp [Formula.hasBVar, Formula.openBVar]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    simp only [Formula.hasBVar, Formula.openBVar, Term.hasBVar_openBVar]; grind
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp only [Formula.hasBVar, Formula.openBVar, ih1, ih2]; grind
  | not φ ih => simp only [Formula.hasBVar, Formula.openBVar, ih]
  | ex _ φ ih | all _ φ ih =>
    simp only [Formula.hasBVar, Formula.openBVar]
    rw [ih (i+1) (k+1)]
    exact or_congr (and_congr (by omega) Iff.rfl) (and_congr (by omega) Iff.rfl)

theorem Refinement.hasBVar_openBVar (r : Refinement) (b : Base) (i k : Nat) (x : EVar) :
    Refinement.hasBVar b i (r.openBVar k x) ↔
      (i < k ∧ Refinement.hasBVar b i r) ∨ (k ≤ i ∧ Refinement.hasBVar b (i+1) r) := by
  induction r with
  | conj r₁ r₂ ih1 ih2 =>
    simp only [Refinement.openBVar, Refinement.hasBVar, ih1, ih2]; grind
  | fmla φ => exact Formula.hasBVar_openBVar φ b i k x
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.hasBVar]
    constructor
    · rintro ⟨a, hmem, hbv⟩
      simp only [List.mem_map] at hmem
      obtain ⟨a', hmem', rfl⟩ := hmem
      rcases (Term.hasBVar_openBVar a'.2 b i k x).mp hbv with ⟨hlt, h⟩ | ⟨hle, h⟩
      · exact Or.inl ⟨hlt, a', hmem', h⟩
      · exact Or.inr ⟨hle, a', hmem', h⟩
    · have hmk : ∀ a ∈ args, (⟨a.1, Term.openBVar k x a.2⟩ : Σ b : Base, Term b)
          ∈ args.map (fun a => ⟨a.1, Term.openBVar k x a.2⟩) :=
        fun a ha => by simp only [List.mem_map]; exact ⟨a, ha, rfl⟩
      rintro (⟨hlt, a, hmem, h⟩ | ⟨hle, a, hmem, h⟩)
      · exact ⟨_, hmk a hmem, (Term.hasBVar_openBVar a.2 b i k x).mpr (Or.inl ⟨hlt, h⟩)⟩
      · exact ⟨_, hmk a hmem, (Term.hasBVar_openBVar a.2 b i k x).mpr (Or.inr ⟨hle, h⟩)⟩

/-- `optBase` is unchanged by `openVar` (shape refine/arrow is preserved). -/
theorem Ty.optBase_openVar (t : Ty) (k : Nat) (y : EVar) :
    (t.openVar k y).optBase = t.optBase := by
  cases t <;> simp [Ty.openVar, Ty.optBase]

/-- Opening at level `ctx.length` (the last binder position) consumes the last
    context entry. For the `app` case use ctx = [], opt = s.optBase:
    `WFBVarCtx [s.optBase] t → WFBVarCtx [] (t.openVar 0 y)`. -/
theorem Ty.WFBVarCtx_openVar_last (t : Ty) (ctx : List (Option Base)) (opt : Option Base)
    (y : EVar) (hWF : Ty.WFBVarCtx (ctx ++ [opt]) t) :
    Ty.WFBVarCtx ctx (t.openVar ctx.length y) := by
  induction t generalizing ctx opt with
  | refine b r =>
    -- ν occupies formula-level 0 (base `b`), so the arrow binder opened by
    -- `openVar ctx.length` lives at formula-level `ctx.length + 1`, and the
    -- WFBVarCtx index list is `some b :: …`. `openBVar` is base-agnostic and
    -- shifting, so `hasBVar` in the opened refinement comes from level `k`
    -- (below the opened level) or the shifted level `k+1` (at/above it).
    simp only [Ty.openVar, Ty.WFBVarCtx] at hWF ⊢
    intro b' k hbv
    rcases (Refinement.hasBVar_openBVar r b' k (ctx.length + 1) y).mp hbv with
      ⟨hlt, hbvr⟩ | ⟨hle, hbvr⟩
    · -- k < ctx.length+1: the occurrence was already at level k in r; the extra
      -- `[opt]` slot sits beyond index k, so it doesn't affect the lookup.
      have hWF' := hWF b' k hbvr
      cases k with
      | zero => simpa using hWF'
      | succ k' =>
        have hk' : k' < ctx.length := by omega
        simp only [List.getElem?_cons_succ] at hWF' ⊢
        rw [List.getElem?_append_left hk'] at hWF'
        exact hWF'
    · -- ctx.length+1 ≤ k: the shifted occurrence sits at index k+1, past the end
      -- of `some b :: (ctx ++ [opt])` (length ctx.length+2) → the lookup is none,
      -- contradicting well-formedness.
      exfalso
      have hWF' := hWF b' (k + 1) hbvr
      rw [List.getElem?_eq_none_iff.mpr (by simp; omega)] at hWF'
      exact absurd hWF' (by simp)
  | arrow s t ihs iht =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.openVar]
    refine ⟨ihs ctx opt hWF.1, ?_⟩
    -- Codomain uses IH with ctx' = s.optBase :: ctx
    have ih := iht (s.optBase :: ctx) opt (by simpa using hWF.2)
    simp only [List.length_cons] at ih
    rw [Ty.optBase_openVar]
    exact ih
  | «forall» kd t ih =>
    simp only [Ty.WFBVarCtx, Ty.openVar] at hWF ⊢
    have h := ih (ctx.map (Option.map Base.shiftT)) (opt.map Base.shiftT)
      (by simpa [List.map_append] using hWF)
    simpa using h
  | prod s t ihs iht =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.openVar]
    refine ⟨ihs ctx opt hWF.1, ?_⟩
    have ih := iht (s.optBase :: ctx) opt (by simpa using hWF.2)
    simp only [List.length_cons] at ih
    rw [Ty.optBase_openVar]
    exact ih
  | data C n args r ih =>
    simp only [Ty.WFBVarCtx, Ty.openVar] at hWF ⊢
    refine ⟨?_, fun i => ih i ctx opt (hWF.2 i)⟩
    intro b' k hbv
    rcases (Refinement.hasBVar_openBVar r b' k (ctx.length + 1) y).mp hbv with
      ⟨hlt, hbvr⟩ | ⟨hle, hbvr⟩
    · have hWF' := hWF.1 b' k hbvr
      cases k with
      | zero => simpa using hWF'
      | succ k' =>
        have hk' : k' < ctx.length := by omega
        simp only [List.getElem?_cons_succ] at hWF' ⊢
        rw [List.getElem?_append_left hk'] at hWF'
        exact hWF'
    · exfalso
      have hWF' := hWF.1 b' (k + 1) hbvr
      rw [List.getElem?_eq_none_iff.mpr (by simp; omega)] at hWF'
      exact absurd hWF' (by simp)

@[simp] theorem Val.proj_inj (s : BSort) (v : s.ty) : Val.proj s (Val.inj s v) = v := by
  cases s <;> rfl

theorem Val.inj_injective (s : BSort) {v w : s.ty} : Val.inj s v = Val.inj s w ↔ v = w := by
  cases s <;> simp

@[simp] theorem Term.fv_substB (σ : BSubst) : ∀ {b : Base} (t : Term b),
    (t.substB σ).fv = t.fv := by
  intro b t
  induction t with
  | const _ _ | bvar _ _ | fvar _ _ | mbvar _ _ | mfvar _ _ | ibvar _ | bbvar _ => rfl
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | leqI _ _ ih₁ ih₂ =>
    simp only [Term.substB, Term.fv]; exact congr (congrArg (· ++ ·) ih₁) ih₂
  | ite _ c t e ihc iht ihe =>
    simp only [Term.substB, Term.fv, iht, ihe]
    exact congrArg (· ++ Term.fv t ++ Term.fv e) ihc
  | not _ ih => simp only [Term.substB, Term.fv]; exact ih

@[simp] theorem Formula.fv_substB (σ : BSubst) (φ : Formula) : (φ.substB σ).fv = φ.fv := by
  induction φ with
  | tt | ff => rfl
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    simp only [Formula.substB, Formula.fv]
    exact congr (congrArg (· ++ ·) (Term.fv_substB σ t₁)) (Term.fv_substB σ t₂)
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp only [Formula.substB, Formula.fv]; exact congr (congrArg (· ++ ·) ih₁) ih₂
  | not _ ih | ex _ _ ih | all _ _ ih => simp only [Formula.substB, Formula.fv]; exact ih

@[simp] theorem Refinement.fv_substB (σ : BSubst) (r : Refinement) :
    (r.substB σ).fv = r.fv := by
  induction r with
  | fmla φ => simp [Refinement.substB, Refinement.fv]
  | kapp kn args =>
    simp only [Refinement.substB, Refinement.fv, List.flatMap_map]
    congr 1; funext a; exact Term.fv_substB σ a.2
  | conj r₁ r₂ ih₁ ih₂ => simp [Refinement.substB, Refinement.fv, ih₁, ih₂]

@[simp] theorem Ty.fv_openTv (k : Nat) (a : TVar) (t : Ty) : (t.openTv k a).fv = t.fv := by
  induction t generalizing k <;> simp_all [Ty.openTv, Ty.fv]

theorem Term.wfB_hasBVar {kctx : List Kind} {ctx : List (Option Base)} :
    ∀ {b'' : Base} (t : Term b''), t.wfB kctx ctx = true →
      ∀ b k, Term.hasBVar b k t → ctx[k]? = some (some b) := by
  intro b'' t
  induction t with
  | const _ _ | fvar _ _ | mbvar _ _ | mfvar _ _ | ibvar _ | bbvar _ => intro _ b k h; simp [Term.hasBVar] at h
  | bvar b' i =>
    intro hw b k h
    simp only [Term.hasBVar] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Term.wfB, Bool.and_eq_true, beq_iff_eq] at hw
    exact hw.1
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | leqI _ _ ih₁ ih₂ =>
    intro hw b k h
    simp only [Term.wfB, Bool.and_eq_true] at hw
    simp only [Term.hasBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 b k h
    · exact ih₂ hw.2 b k h
  | ite _ c t e ihc iht ihe =>
    intro hw b k h
    simp only [Term.wfB, Bool.and_eq_true] at hw
    simp only [Term.hasBVar] at h
    rcases h with h | h | h
    · exact ihc hw.1.1 b k h
    · exact iht hw.1.2 b k h
    · exact ihe hw.2 b k h
  | not _ ih =>
    intro hw b k h
    simp only [Term.wfB] at hw
    exact ih hw b k h

theorem Formula.wfB_hasBVar (φ : Formula) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    φ.wfB kctx ctx = true → ∀ b k, Formula.hasBVar b k φ → ctx[k]? = some (some b) := by
  induction φ with
  | tt | ff => intro _ _ _ b k h; simp [Formula.hasBVar] at h
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro kctx ctx hw b k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasBVar] at h
    rcases h with h | h
    · exact Term.wfB_hasBVar t₁ hw.1 b k h
    · exact Term.wfB_hasBVar t₂ hw.2 b k h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro kctx ctx hw b k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 b k h
    · exact ih₂ hw.2 b k h
  | not _ ih =>
    intro kctx ctx hw b k h
    simp only [Formula.wfB] at hw
    exact ih hw b k h
  | ex b₀ _ ih | all b₀ _ ih =>
    intro kctx ctx hw b k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasBVar] at h
    have := ih hw.2 b (k+1) h
    simpa using this

theorem Refinement.wfB_hasBVar (r : Refinement) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    r.wfB kctx ctx = true → ∀ b k, Refinement.hasBVar b k r → ctx[k]? = some (some b) := by
  induction r with
  | fmla φ => intro kctx ctx hw; exact Formula.wfB_hasBVar φ hw
  | kapp kn args =>
    intro kctx ctx hw b k h
    simp only [Refinement.wfB, List.all_eq_true, Bool.and_eq_true] at hw
    simp only [Refinement.hasBVar] at h
    obtain ⟨a, ha, hbv⟩ := h
    exact Term.wfB_hasBVar a.2 (hw a ha).2 b k hbv
  | conj _ _ ih₁ ih₂ =>
    intro kctx ctx hw b k h
    simp only [Refinement.wfB, Bool.and_eq_true] at hw
    simp only [Refinement.hasBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 b k h
    · exact ih₂ hw.2 b k h

theorem Term.wfB_hasMBVar {kctx : List Kind} {ctx : List (Option Base)} :
    ∀ {b'' : Base} (t : Term b''), t.wfB kctx ctx = true → ∀ k, Term.hasMBVar k t → k < ctx.length := by
  intro b'' t
  induction t with
  | const _ _ | bvar _ _ | fvar _ _ | mfvar _ _ => intro _ k h; simp [Term.hasMBVar] at h
  | mbvar m j =>
    intro hw k h
    simp only [Term.hasMBVar] at h; subst h
    simpa [Term.wfB] using hw
  | ibvar j =>
    intro hw k h
    simp only [Term.hasMBVar] at h; subst h
    simpa [Term.wfB] using hw
  | bbvar j =>
    intro hw k h
    simp only [Term.hasMBVar] at h; subst h
    simpa [Term.wfB] using hw
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | leqI _ _ ih₁ ih₂ =>
    intro hw k h
    simp only [Term.wfB, Bool.and_eq_true] at hw
    simp only [Term.hasMBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 k h
    · exact ih₂ hw.2 k h
  | ite _ c t e ihc iht ihe =>
    intro hw k h
    simp only [Term.wfB, Bool.and_eq_true] at hw
    simp only [Term.hasMBVar] at h
    rcases h with h | h | h
    · exact ihc hw.1.1 k h
    · exact iht hw.1.2 k h
    · exact ihe hw.2 k h
  | not _ ih => intro hw k h; exact ih hw k h

theorem Formula.wfB_hasMBVar (φ : Formula) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    φ.wfB kctx ctx = true → ∀ k, Formula.hasMBVar k φ → k < ctx.length := by
  induction φ with
  | tt | ff => intro _ _ _ k h; simp [Formula.hasMBVar] at h
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro kctx ctx hw k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasMBVar] at h
    rcases h with h | h
    · exact Term.wfB_hasMBVar t₁ hw.1 k h
    · exact Term.wfB_hasMBVar t₂ hw.2 k h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro kctx ctx hw k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasMBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 k h
    · exact ih₂ hw.2 k h
  | not _ ih =>
    intro kctx ctx hw k h
    simp only [Formula.wfB] at hw
    exact ih hw k h
  | ex b₀ _ ih | all b₀ _ ih =>
    intro kctx ctx hw k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasMBVar] at h
    have := ih hw.2 (k+1) h
    simpa using this

theorem Refinement.wfB_hasMBVar (r : Refinement) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    r.wfB kctx ctx = true → ∀ k, Refinement.hasMBVar k r → k < ctx.length := by
  induction r with
  | fmla φ => intro kctx ctx hw; exact Formula.wfB_hasMBVar φ hw
  | kapp kn args =>
    intro kctx ctx hw k h
    simp only [Refinement.wfB, List.all_eq_true, Bool.and_eq_true] at hw
    simp only [Refinement.hasMBVar] at h
    obtain ⟨a, ha, hbv⟩ := h
    exact Term.wfB_hasMBVar a.2 (hw a ha).2 k hbv
  | conj _ _ ih₁ ih₂ =>
    intro kctx ctx hw k h
    simp only [Refinement.wfB, Bool.and_eq_true] at hw
    simp only [Refinement.hasMBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 k h
    · exact ih₂ hw.2 k h

/-- The checker is sound for bound-variable sort consistency. -/
theorem Ty.wfB_WFBVarCtx (t : Ty) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    t.wfB kctx ctx = true → Ty.WFBVarCtx ctx t := by
  induction t with
  | refine b r =>
    intro kctx ctx hw
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    exact Refinement.wfB_hasBVar r hw.2
  | arrow s t ihs iht =>
    intro kctx ctx hw
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    exact ⟨ihs hw.1, iht hw.2⟩
  | «forall» κ t ih =>
    intro kctx ctx hw
    simp only [Ty.wfB] at hw
    exact ih hw
  | prod s t ihs iht =>
    intro kctx ctx hw
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    exact ⟨ihs hw.1, iht hw.2⟩
  | data C n args r ih =>
    intro kctx ctx hw
    simp only [Ty.wfB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hw
    exact ⟨Refinement.wfB_hasBVar r hw.1, fun i => ih i (hw.2 i)⟩

theorem Ty.wfB_WFBVars (t : Ty) (h : t.wfB [] [] = true) : Ty.WFBVars t :=
  Ty.wfB_WFBVarCtx t h

/-! ### Bound-variable sort consistency under type-binder opening -/

theorem Term.hasBVar_substB (σ : BSubst) (b : Base) (k : Nat) :
    ∀ {b'' : Base} (t : Term b''), Term.hasBVar b k (t.substB σ) →
      ∃ b₀, b = b₀.substB σ ∧ Term.hasBVar b₀ k t := by
  intro b'' t
  induction t with
  | const _ _ | fvar _ _ | mbvar _ _ | mfvar _ _ | ibvar _ | bbvar _ => intro h; simp [Term.substB, Term.hasBVar] at h
  | bvar b' i =>
    intro h
    simp only [Term.substB, Term.hasBVar] at h
    exact ⟨b', h.1, rfl, h.2⟩
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | leqI _ _ ih₁ ih₂ =>
    intro h
    simp only [Term.substB, Term.hasBVar] at h
    rcases h with h | h
    · obtain ⟨b₀, hb, h⟩ := ih₁ h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := ih₂ h; exact ⟨b₀, hb, Or.inr h⟩
  | ite _ c t e ihc iht ihe =>
    intro h
    simp only [Term.substB, Term.hasBVar] at h
    rcases h with h | h | h
    · obtain ⟨b₀, hb, h⟩ := ihc h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := iht h; exact ⟨b₀, hb, Or.inr (Or.inl h)⟩
    · obtain ⟨b₀, hb, h⟩ := ihe h; exact ⟨b₀, hb, Or.inr (Or.inr h)⟩
  | not _ ih => intro h; simp only [Term.substB, Term.hasBVar] at h; exact ih h

theorem Formula.hasBVar_substB (σ : BSubst) (b : Base) (φ : Formula) :
    ∀ k, Formula.hasBVar b k (φ.substB σ) → ∃ b₀, b = b₀.substB σ ∧ Formula.hasBVar b₀ k φ := by
  induction φ with
  | tt | ff => intro k h; simp [Formula.substB, Formula.hasBVar] at h
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro k h
    simp only [Formula.substB, Formula.hasBVar] at h
    rcases h with h | h
    · obtain ⟨b₀, hb, h⟩ := Term.hasBVar_substB σ b k t₁ h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := Term.hasBVar_substB σ b k t₂ h; exact ⟨b₀, hb, Or.inr h⟩
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro k h
    simp only [Formula.substB, Formula.hasBVar] at h
    rcases h with h | h
    · obtain ⟨b₀, hb, h⟩ := ih₁ k h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := ih₂ k h; exact ⟨b₀, hb, Or.inr h⟩
  | not _ ih => intro k h; simp only [Formula.substB, Formula.hasBVar] at h; exact ih k h
  | ex _ _ ih | all _ _ ih =>
    intro k h; simp only [Formula.substB, Formula.hasBVar] at h; exact ih (k+1) h

theorem Refinement.hasBVar_substB (σ : BSubst) (b : Base) (r : Refinement) (k : Nat)
    (h : Refinement.hasBVar b k (r.substB σ)) :
    ∃ b₀, b = b₀.substB σ ∧ Refinement.hasBVar b₀ k r := by
  induction r with
  | fmla φ => exact Formula.hasBVar_substB σ b φ k h
  | kapp kn args =>
    simp only [Refinement.substB, Refinement.hasBVar, List.mem_map] at h
    obtain ⟨_, ⟨a, ha, rfl⟩, hbv⟩ := h
    obtain ⟨b₀, hb, hbv⟩ := Term.hasBVar_substB σ b k a.2 hbv
    exact ⟨b₀, hb, a, ha, hbv⟩
  | conj _ _ ih₁ ih₂ =>
    simp only [Refinement.substB, Refinement.hasBVar] at h
    rcases h with h | h
    · obtain ⟨b₀, hb, h⟩ := ih₁ h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := ih₂ h; exact ⟨b₀, hb, Or.inr h⟩

/-- Opening commutes with entering a further type binder. -/
theorem Base.shiftT_substB_openAt (k : Nat) (a : TVar) (b : Base) :
    (b.substB (BSubst.openAt k a)).shiftT = b.shiftT.substB (BSubst.openAt (k+1) a) := by
  cases b with
  | tbvar j =>
    simp only [Base.substB, BSubst.openAt, BSubst.instAt, Base.shiftT]
    by_cases h₁ : j = k
    · subst h₁; simp
    · by_cases h₂ : k < j
      · simp [h₁, h₂] <;> omega
      · simp [h₁, h₂] <;> omega
  | _ => rfl

/-- Opening a type binder preserves bound-variable sort consistency (with the
    recorded sorts opened alike). -/
theorem Ty.WFBVarCtx_openTv (t : Ty) : ∀ (k : Nat) (a : TVar) (ctx : List (Option Base)),
    Ty.WFBVarCtx ctx t →
    Ty.WFBVarCtx (ctx.map (Option.map (Base.substB (BSubst.openAt k a)))) (t.openTv k a) := by
  induction t with
  | refine br r =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    intro b i hbv
    obtain ⟨b₀, rfl, hbv₀⟩ := Refinement.hasBVar_substB _ b r i hbv
    have := h b₀ i hbv₀
    show ((some br :: ctx).map (Option.map (Base.substB (BSubst.openAt k a))))[i]? = _
    rw [List.getElem?_map, this]; rfl
  | arrow s t ihs iht =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨ihs k a ctx h.1, ?_⟩
    have := iht k a (s.optBase :: ctx) h.2
    have hopt : (s.openTv k a).optBase = s.optBase.map (Base.substB (BSubst.openAt k a)) := by
      cases s <;> rfl
    rw [hopt]; simpa using this
  | «forall» κ t ih =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    have := ih (k+1) a (ctx.map (Option.map Base.shiftT)) h
    have hmap : (ctx.map (Option.map (Base.substB (BSubst.openAt k a)))).map (Option.map Base.shiftT)
        = (ctx.map (Option.map Base.shiftT)).map (Option.map (Base.substB (BSubst.openAt (k+1) a))) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro o _
      cases o <;> simp [Base.shiftT_substB_openAt]
    rw [hmap]; exact this
  | prod s t ihs iht =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨ihs k a ctx h.1, ?_⟩
    have := iht k a (s.optBase :: ctx) h.2
    have hopt : (s.openTv k a).optBase = s.optBase.map (Base.substB (BSubst.openAt k a)) := by
      cases s <;> rfl
    rw [hopt]; simpa using this
  | data C n args r ih =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨?_, fun i => ih i k a ctx (h.2 i)⟩
    intro b i hbv
    obtain ⟨b₀, rfl, hbv₀⟩ := Refinement.hasBVar_substB _ b r i hbv
    have := h.1 b₀ i hbv₀
    show ((none :: ctx).map (Option.map (Base.substB (BSubst.openAt k a))))[i]? = _
    rw [List.getElem?_map, this]; rfl

theorem Ty.WFBVars_openTv (t : Ty) (k : Nat) (a : TVar) (h : Ty.WFBVars t) :
    Ty.WFBVars (t.openTv k a) := by
  have := Ty.WFBVarCtx_openTv t k a [] h
  simpa using this

@[simp] theorem Ty.fv_closeTv (k : Nat) (a : TVar) (t : Ty) : (t.closeTv k a).fv = t.fv := by
  induction t generalizing k <;> simp_all [Ty.closeTv, Ty.fv]

@[simp] theorem Ty.fv_gen (as : List TVar) (t : Ty) : (Ty.gen as t).fv = t.fv := by
  induction as <;> simp_all [Ty.gen, Ty.fv]

theorem Base.shiftT_substB_closeAt (k : Nat) (a : TVar) (b : Base) :
    (b.substB (BSubst.closeAt k a)).shiftT = b.shiftT.substB (BSubst.closeAt (k+1) a) := by
  cases b with
  | tbvar j =>
    simp only [Base.substB, BSubst.closeAt, Base.shiftT]
    by_cases h : k ≤ j
    · simp [h, show k + 1 ≤ j + 1 by omega]
    · simp [h, show ¬ k + 1 ≤ j + 1 by omega]
  | tfvar a' =>
    simp only [Base.substB, BSubst.closeAt]
    by_cases h : a' = a <;> simp [h, Base.shiftT]
  | _ => rfl

theorem Ty.WFBVarCtx_closeTv (t : Ty) : ∀ (k : Nat) (a : TVar) (ctx : List (Option Base)),
    Ty.WFBVarCtx ctx t →
    Ty.WFBVarCtx (ctx.map (Option.map (Base.substB (BSubst.closeAt k a)))) (t.closeTv k a) := by
  induction t with
  | refine br r =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    intro b i hbv
    obtain ⟨b₀, rfl, hbv₀⟩ := Refinement.hasBVar_substB _ b r i hbv
    have := h b₀ i hbv₀
    show ((some br :: ctx).map (Option.map (Base.substB (BSubst.closeAt k a))))[i]? = _
    rw [List.getElem?_map, this]; rfl
  | arrow s t ihs iht =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨ihs k a ctx h.1, ?_⟩
    have := iht k a (s.optBase :: ctx) h.2
    have hopt : (s.closeTv k a).optBase = s.optBase.map (Base.substB (BSubst.closeAt k a)) := by
      cases s <;> rfl
    rw [hopt]; simpa using this
  | «forall» κ t ih =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    have := ih (k+1) a (ctx.map (Option.map Base.shiftT)) h
    have hmap : (ctx.map (Option.map (Base.substB (BSubst.closeAt k a)))).map (Option.map Base.shiftT)
        = (ctx.map (Option.map Base.shiftT)).map (Option.map (Base.substB (BSubst.closeAt (k+1) a))) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro o _
      cases o <;> simp [Base.shiftT_substB_closeAt]
    rw [hmap]; exact this
  | prod s t ihs iht =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨ihs k a ctx h.1, ?_⟩
    have := iht k a (s.optBase :: ctx) h.2
    have hopt : (s.closeTv k a).optBase = s.optBase.map (Base.substB (BSubst.closeAt k a)) := by
      cases s <;> rfl
    rw [hopt]; simpa using this
  | data C n args r ih =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨?_, fun i => ih i k a ctx (h.2 i)⟩
    intro b i hbv
    obtain ⟨b₀, rfl, hbv₀⟩ := Refinement.hasBVar_substB _ b r i hbv
    have := h.1 b₀ i hbv₀
    show ((none :: ctx).map (Option.map (Base.substB (BSubst.closeAt k a))))[i]? = _
    rw [List.getElem?_map, this]; rfl

theorem Ty.WFBVars_gen (as : List TVar) (t : Ty) (h : Ty.WFBVars t) : Ty.WFBVars (Ty.gen as t) := by
  induction as with
  | nil => exact h
  | cons a as ih =>
    have := Ty.WFBVarCtx_closeTv _ 0 a [] ih
    simpa [Ty.gen, Ty.WFBVars, Ty.WFBVarCtx] using this

theorem Exp.WFBVars_openTv (e : Exp) (k : Nat) (a : TVar) (h : Exp.WFBVars e) :
    Exp.WFBVars (e.openTv k a) := by
  induction e generalizing k with
  | ann e t ih =>
    simp only [Exp.WFBVars, Exp.openTv] at h ⊢
    exact ⟨Ty.WFBVars_openTv t k a h.1, ih k h.2⟩
  | _ => simp_all [Exp.WFBVars, Exp.openTv]

@[simp] theorem Exp.lc_at_openTv (k : Nat) (a : TVar) (e : Exp) (n : Nat) :
    (e.openTv k a).lc_at n ↔ e.lc_at n := by
  induction e generalizing k n <;> simp_all [Exp.openTv, Exp.lc_at]

@[simp] theorem Exp.fv_openTv (k : Nat) (a : TVar) (e : Exp) :
    (e.openTv k a).fv = e.fv := by
  induction e generalizing k <;> simp_all [Exp.openTv, Exp.fv]

theorem TEnv.genVars_fresh {Γ : TEnv} {t : Ty} {a : TVar} (h : a ∈ TEnv.genVars Γ t) :
    a ∉ TEnv.ftv Γ := by
  simp only [TEnv.genVars, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

@[simp] theorem Exp.erase_erase (e : Exp) : e.erase.erase = e.erase := by
  induction e <;> simp_all [Exp.erase]

@[simp] theorem Exp.erase_openTv (k : Nat) (a : TVar) (e : Exp) :
    (e.openTv k a).erase = e.erase := by
  induction e generalizing k <;> simp_all [Exp.openTv, Exp.erase]

theorem Exp.erase_openExp (k : Nat) (u e : Exp) :
    (Exp.openExp k u e).erase = Exp.openExp k u.erase e.erase := by
  induction e generalizing k with
  | bvar j => by_cases h : j = k <;> simp [Exp.openExp, Exp.erase, h]
  | _ => simp_all [Exp.openExp, Exp.erase]

theorem Exp.fv_erase_subset (e : Exp) : ∀ z ∈ e.erase.fv, z ∈ e.fv := by
  induction e <;> simp_all [Exp.erase, Exp.fv] <;> grind

theorem Exp.lc_at_erase (e : Exp) (k : Nat) (h : e.lc_at k) : e.erase.lc_at k := by
  induction e generalizing k <;> simp_all [Exp.erase, Exp.lc_at]

theorem Exp.typeFree_erase (e : Exp) : e.erase.TypeFree := by
  induction e <;> simp_all [Exp.erase, Exp.TypeFree]

theorem Exp.erase_of_typeFree (e : Exp) (h : e.TypeFree) : e.erase = e := by
  induction e <;> simp_all [Exp.erase, Exp.TypeFree]

/-- A type-free expression is unaffected by opening a type binder. -/
theorem Exp.openTv_of_typeFree (k : Nat) (a : TVar) (e : Exp) (h : e.TypeFree) :
    e.openTv k a = e := by
  induction e generalizing k <;> simp_all [Exp.openTv, Exp.TypeFree]

/-- The closing substitution commutes with erasure, provided the substituted
    values are erased. -/
theorem Exp.erase_substEnv (γ : REnv) (e : Exp)
    (hγ : ∀ z ∈ e.fv, Val.Erased (γ.map z)) :
    (Exp.substEnv γ e).erase = Exp.substEnv γ e.erase := by
  induction e with
  | fvar x => exact Exp.erase_of_typeFree _ (hγ x (by simp [Exp.fv]))
  | case e n alts ih ihs =>
    simp only [Exp.substEnv, Exp.erase, Exp.fv, List.mem_append, List.mem_flatMap,
      List.mem_finRange, true_and] at hγ ⊢
    rw [ih (fun z hz => hγ z (Or.inl hz))]
    congr 1; funext j; exact ihs j (fun z hz => hγ z (Or.inr ⟨j, hz⟩))
  | _ => simp_all [Exp.substEnv, Exp.erase, Exp.fv]

/-- The closing substitution commutes with opening a type binder, provided the
    substituted values are erased (hence type-free). -/
theorem Exp.substEnv_openTv (γ : REnv) (k : Nat) (a : TVar) (e : Exp)
    (hγ : ∀ z ∈ e.fv, Val.Erased (γ.map z)) :
    Exp.substEnv γ (e.openTv k a) = (Exp.substEnv γ e).openTv k a := by
  induction e generalizing k with
  | fvar x =>
    simp only [Exp.openTv, Exp.substEnv]
    exact (Exp.openTv_of_typeFree k a _ (hγ x (by simp [Exp.fv]))).symm
  | case e n alts ih ihs =>
    simp only [Exp.substEnv, Exp.openTv, Exp.fv, List.mem_append, List.mem_flatMap,
      List.mem_finRange, true_and] at hγ ⊢
    rw [ih k (fun z hz => hγ z (Or.inl hz))]
    congr 1; funext j; exact ihs j k (fun z hz => hγ z (Or.inr ⟨j, hz⟩))
  | _ => simp_all [Exp.substEnv, Exp.openTv, Exp.fv, Ty.openTv, Base.substB, Refinement.substB,
      Formula.substB]

/-! ## 10. REnv helpers -/

@[simp] theorem REnv.get_update_same (b : Base) (γ : REnv) (x : EVar) (v : b.sem γ.sorts) :
    REnv.get b (γ.update b x v) x = v := by
  simp [REnv.get, REnv.update, REnv.write, REnv.lookup]

/-! ## 11. EVar.fresh proof -/

private theorem EVar.maxLen_ge {L : List EVar} {s : EVar} (h : s ∈ L) :
    s.length ≤ EVar.maxLen L := by
  induction L with
  | nil => simp at h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [EVar.maxLen]; exact Nat.le_max_left _ _
    · simp [EVar.maxLen]
      exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

private theorem EVar.fresh_length (L : List EVar) :
    (EVar.fresh L).length = EVar.maxLen L + 1 := by
  show (String.ofList (List.replicate (EVar.maxLen L + 1) 'x')).length
       = EVar.maxLen L + 1
  rw [String.length_ofList, List.length_replicate]

theorem EVar.fresh_not_mem (L : List EVar) : EVar.fresh L ∉ L := by
  intro h
  have h₁ : (EVar.fresh L).length = EVar.maxLen L + 1 := EVar.fresh_length L
  have h₂ : (EVar.fresh L).length ≤ EVar.maxLen L := EVar.maxLen_ge h
  rw [h₁] at h₂
  omega

theorem TVar.fresh_not_mem (L : List TVar) (κ : Kind) : TVar.fresh L κ ∉ L := fun h =>
  EVar.fresh_not_mem (L.map Prod.fst) (List.mem_map.mpr ⟨_, h, rfl⟩)


/-- A fresh name is `≠` any member of the list it was drawn from — decided by
    *length* (`EVar.maxLen`), not by comparing the `x`-strings character by
    character (which is prohibitively deep for nested contexts). Stated as
    `beq = false` so it fires as a `simp` rewrite on `if · == · …`. -/
@[simp] theorem EVar.fresh_beq_mem_left (L : List EVar) (x : EVar) (h : x ∈ L) :
    (EVar.fresh L == x) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq; subst heq; exact EVar.fresh_not_mem L h

@[simp] theorem EVar.fresh_beq_mem_right (L : List EVar) (x : EVar) (h : x ∈ L) :
    (x == EVar.fresh L) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq; subst heq; exact EVar.fresh_not_mem L h

/-! ## 15. `Exp.substEnv` push-through lemmas

  Under the structural definition each constructor case is *definitional*
  (`rfl`); the lemmas are kept (as `@[simp]`) so existing call sites and the
  `simp` set continue to fire by name. -/

@[simp]
theorem Exp.substEnv_fvar (γ : REnv) (x : EVar) :
    Exp.substEnv γ (.fvar x) = (γ.map x).toExp := rfl

@[simp]
theorem Exp.substEnv_iconst (γ : REnv) (n : Int) :
    Exp.substEnv γ (.iconst n) = .iconst n := rfl

@[simp]
theorem Exp.substEnv_bconst (γ : REnv) (b : Bool) :
    Exp.substEnv γ (.bconst b) = .bconst b := rfl

@[simp]
theorem Exp.substEnv_lam (γ : REnv) (body : Exp) :
    Exp.substEnv γ (.lam body) = .lam (Exp.substEnv γ body) := rfl

@[simp]
theorem Exp.substEnv_letin (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.letin e₁ e₂) = .letin (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_app (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.app e₁ e₂) = .app (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_ann (γ : REnv) (e : Exp) (t : Ty) :
    Exp.substEnv γ (.ann e t) = .ann (Exp.substEnv γ e) t := rfl

@[simp]
theorem Exp.substEnv_add (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.add e₁ e₂) = .add (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_leq (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.leq e₁ e₂) = .leq (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_not (γ : REnv) (e : Exp) :
    Exp.substEnv γ (.not e) = .not (Exp.substEnv γ e) := rfl

@[simp]
theorem Exp.substEnv_and (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.and e₁ e₂) = .and (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_ite (γ : REnv) (e₀ e₁ e₂ : Exp) :
    Exp.substEnv γ (.ite e₀ e₁ e₂) = .ite (Exp.substEnv γ e₀) (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_unreach (γ : REnv) :
    Exp.substEnv γ .unreach = .unreach := rfl

@[simp]
theorem Exp.substEnv_fix (γ : REnv) (body : Exp) :
    Exp.substEnv γ (.fix body) = .fix (Exp.substEnv γ body) := rfl

@[simp]
theorem Exp.substEnv_tabs (γ : REnv) (κ : Kind) (e : Exp) :
    Exp.substEnv γ (.tabs κ e) = .tabs κ (Exp.substEnv γ e) := rfl

@[simp]
theorem Exp.substEnv_tapp (γ : REnv) (e : Exp) (t : Ty) :
    Exp.substEnv γ (.tapp e t) = .tapp (Exp.substEnv γ e) (.refine .int (.fmla .tt)) := rfl

/-- A closed expression is fixed, up to erasure, under the closing substitution
    (which drops type-application and constructor instances). -/
theorem Exp.substEnv_closed (γ : REnv) (e : Exp) (he : e.fv = []) :
    (Exp.substEnv γ e).erase = e.erase := by
  induction e with
  | fvar y => simp [Exp.fv] at he
  | case e n alts ih ihs =>
    simp only [Exp.fv, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.mem_finRange,
      true_implies] at he
    simp only [Exp.substEnv, Exp.erase, ih he.1]
    congr 1; funext j; exact ihs j (he.2 j)
  | _ => simp_all [Exp.substEnv, Exp.erase, Exp.fv]

theorem Val.toExp_closed_of_closed {v : Val} (h : Val.closed v) : v.toExp.fv = [] := h

theorem Val.toExp_lc_at_zero {v : Val} (h : Val.lc v) : Exp.lc_at 0 v.toExp := h

/-- If every free name of `e` is mapped to a closed value by `γ`, then the
    closing substitution produces a closed expression. -/
theorem Exp.substEnv_fv_nil (γ : REnv) (e : Exp)
    (hcl : ∀ z ∈ e.fv, Val.closed (γ.map z)) :
    (Exp.substEnv γ e).fv = [] := by
  induction e with
  | bvar _ | iconst _ | bconst _ | unreach => rfl
  | fvar x => exact Val.toExp_closed_of_closed (hcl x (by simp [Exp.fv]))
  | lam body ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | fix body ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | ann e t ih | tapp e t ih | tabs t e ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | not e ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨ih₁ fun z hz => hcl z (by simp [Exp.fv, hz]),
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨⟨ih₀ fun z hz => hcl z (by simp [Exp.fv, hz]),
            ih₁ fun z hz => hcl z (by simp [Exp.fv, hz])⟩,
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩
  | pair e₁ e₂ ih₁ ih₂ | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨ih₁ fun z hz => hcl z (by simp [Exp.fv, hz]),
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩
  | ctor C j τs e ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | case e n alts ih ihs =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
      List.mem_finRange, true_implies]
    exact ⟨ih fun z hz => hcl z (by simp [Exp.fv, hz]),
           fun j => ihs j fun z hz => hcl z (by simp only [Exp.fv, List.mem_append,
             List.mem_flatMap, List.mem_finRange, true_and]; exact Or.inr ⟨j, hz⟩)⟩

/-! ## 17b. openVar of lc_at is identity -/

/-- Converse of openVar_of_lc_at: if opening e at depth k with any name gives lc_at k,
    then e itself is lc_at (k+1). This is the standard LN "body is lc" lemma. -/
theorem Exp.lc_at_of_openVar (e : Exp) (k : Nat) (x : EVar)
    (h : (e.openVar k x).lc_at k) : e.lc_at (k + 1) := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.openVar] at h
    simp only [Exp.lc_at]
    by_cases hjk : j = k
    · subst hjk; omega
    · simp only [hjk, ↓reduceIte, Exp.lc_at] at h; omega
  | fvar _ => trivial
  | iconst _ => trivial
  | bconst _ => trivial
  | unreach => trivial
  | lam body ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih (k + 1) h
  | fix body ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih (k + 2) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ (k + 1) h.2⟩
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | ann e t ih | tapp e t ih | tabs t e ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih k h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | not e ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih k h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₀ k h.1, ih₁ k h.2.1, ih₂ k h.2.2⟩
  | add e₁ e₂ ih₁ ih₂ | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ (k + 2) h.2⟩
  | ctor C j τs e ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih k h
  | case e n alts ih ihs =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih k h.1, fun j => ihs j (k + 1) (h.2 j)⟩

/-- Opening a binder with `y` adds at most `y` to the free names. -/
theorem Exp.fv_openVar {e : Exp} {k : Nat} {y z : EVar}
    (h : z ∈ (e.openVar k y).fv) : z ∈ e.fv ∨ z = y := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.openVar] at h
    split at h <;> simp_all [Exp.fv]
  | fvar _ | iconst _ | bconst _ | unreach => simp_all [Exp.openVar, Exp.fv]
  | lam _ ih | ann _ _ ih | not _ ih | fix _ ih | tapp _ _ ih | tabs _ _ ih =>
    simp only [Exp.openVar, Exp.fv] at h ⊢; exact ih h
  | letin _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | and _ _ ih₁ ih₂
  | leq _ _ ih₁ ih₂ | add _ _ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | ite _ _ _ ih₀ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.fv, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · rcases ih₀ h with h | h <;> simp [h]
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | pair _ _ ih₁ ih₂ | split _ _ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | ctor _ _ _ _ ih => simp only [Exp.openVar, Exp.fv] at h ⊢; exact ih h
  | case _ _ _ ih ihs =>
    simp only [Exp.openVar, Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange,
      true_and] at h ⊢
    rcases h with h | ⟨j, h⟩
    · rcases ih h with h | h <;> simp [h]
    · rcases ihs j h with h | h
      · exact Or.inl (Or.inr ⟨j, h⟩)
      · exact Or.inr h

/-- openExp with any u is identity when e has lc_at k (no BVar k inside). -/
theorem Exp.openExp_of_lc_at (e : Exp) (k : Nat) (u : Exp) (h : Exp.lc_at k e) :
    Exp.openExp k u e = e := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openExp, if_neg (Nat.ne_of_lt h)]
  | fvar _ => rfl
  | iconst _ => rfl
  | bconst _ => rfl
  | unreach => rfl
  | lam body ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih (k+1) h
  | fix body ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih (k+2) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih₁ k h.1, ih₂ (k+1) h.2]
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | ann e t ih | tapp e t ih | tabs t e ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih k h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | not e ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih k h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih₀ k h.1, ih₁ k h.2.1, ih₂ k h.2.2]
  | add e₁ e₂ ih₁ ih₂ | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih₁ k h.1, ih₂ (k+2) h.2]
  | ctor C j τs e ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih k h
  | case e n alts ih ihs =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih k h.1]; congr 1; funext j; exact ihs j (k+1) (h.2 j)

/-- lc_at is monotone: lc_at j implies lc_at k for k ≥ j. -/
theorem Exp.lc_at_mono (e : Exp) {j k : Nat} (hjk : j ≤ k) (h : Exp.lc_at j e) :
    Exp.lc_at k e := by
  induction e generalizing j k with
  | bvar i => exact Nat.lt_of_lt_of_le h hjk
  | fvar _ => trivial
  | iconst _ => trivial
  | bconst _ => trivial
  | unreach => trivial
  | lam body ih =>
    simp only [Exp.lc_at] at *
    exact ih (Nat.succ_le_succ hjk) h
  | fix body ih =>
    simp only [Exp.lc_at] at *
    exact ih (by omega) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ (Nat.succ_le_succ hjk) h.2⟩
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | ann e t ih | tapp e t ih | tabs t e ih =>
    simp only [Exp.lc_at] at *
    exact ih hjk h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | not e ih =>
    simp only [Exp.lc_at] at *
    exact ih hjk h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₀ hjk h.1, ih₁ hjk h.2.1, ih₂ hjk h.2.2⟩
  | add e₁ e₂ ih₁ ih₂ | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ (by omega) h.2⟩
  | ctor C j τs e ih =>
    simp only [Exp.lc_at] at *
    exact ih hjk h
  | case e n alts ih ihs =>
    simp only [Exp.lc_at] at *
    exact ⟨ih hjk h.1, fun j => ihs j (by omega) (h.2 j)⟩

/-! ## 17b. subst/substEnv preserve lc_at -/

theorem Exp.substEnv_lc_at (γ : REnv) (e : Exp) (k : Nat)
    (hγ : ∀ z ∈ e.fv, Val.lc (γ.map z)) (hlc_e : e.lc_at k) :
    (e.substEnv γ).lc_at k := by
  induction e generalizing k with
  | bvar j => simpa [Exp.substEnv] using hlc_e
  | iconst _ | bconst _ | unreach => trivial
  | fvar x =>
    exact Exp.lc_at_mono _ (Nat.zero_le k) (Val.toExp_lc_at_zero (hγ x (by simp [Exp.fv])))
  | lam body ih =>
    exact ih (k+1) (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | fix body ih =>
    exact ih (k+2) (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | ann e t ih | tapp e t ih | tabs t e ih =>
    exact ih k (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | not e ih =>
    exact ih k (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | letin e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ (k+1) (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    obtain ⟨h₀, h₁, h₂⟩ := hlc_e
    exact ⟨ih₀ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₀,
           ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | pair e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | split e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ (k+2) (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | ctor C j τs e ih =>
    exact ih k (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | case e n alts ih ihs =>
    obtain ⟨h₀, h₁⟩ := hlc_e
    exact ⟨ih k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₀,
           fun j => ihs j (k+1) (fun z hz => hγ z (by
             simp only [Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
             exact Or.inr ⟨j, hz⟩)) (h₁ j)⟩


/-! ## 19. substEnv-openVal: key lemma for lam/letin cases -/

theorem REnv.write_self (γ : REnv) (x : EVar) (v : Val) : (γ.write x v).map x = v := by
  simp

theorem REnv.write_other (γ : REnv) (x : EVar) (v : Val) {y : EVar} (h : x ≠ y) :
    (γ.write x v).map y = γ.map y := by
  have hxy : (x == y) = false := by simp [h]
  simp [hxy]

/-- Writing a cell's current value back is the identity (no `HasBase` needed,
    since `write` is lossless). Drives the simplified `app` case of the
    fundamental lemma. -/
theorem REnv.write_idem (γ : REnv) (x : EVar) : γ.write x (γ.map x) = γ := by
  apply REnv.ext
  · funext y
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  · rfl
  · rfl

/-- The closing substitution depends only on `γ` over the free names of `e`. -/
theorem Exp.substEnv_congr (e : Exp) (γ₁ γ₂ : REnv)
    (h : ∀ z ∈ e.fv, γ₁.map z = γ₂.map z) :
    Exp.substEnv γ₁ e = Exp.substEnv γ₂ e := by
  induction e with
  | bvar _ | iconst _ | bconst _ | unreach => rfl
  | fvar x => simp only [Exp.substEnv, h x (by simp [Exp.fv])]
  | lam e ih | ann e _ ih | not e ih | fix e ih | tapp e _ ih | tabs _ e ih =>
    simp only [Exp.substEnv, ih fun z hz => h z (by simpa [Exp.fv] using hz)]
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₀ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]
  | pair e₁ e₂ ih₁ ih₂ | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]
  | ctor _ _ _ e ih =>
    simp only [Exp.substEnv, ih fun z hz => h z (by simpa [Exp.fv] using hz)]
  | case e n alts ih ihs =>
    simp only [Exp.substEnv, ih fun z hz => h z (by simp [Exp.fv, hz])]
    congr 1; funext j
    exact ihs j fun z hz => h z (by
      simp only [Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
      exact Or.inr ⟨j, hz⟩)

/-- Extending `γ` at a name `y` not free in `e` does not change `substEnv`. -/
theorem Exp.substEnv_write_fresh (e : Exp) (γ : REnv) (y : EVar) (v : Val)
    (h : y ∉ e.fv) :
    Exp.substEnv (γ.write y v) e = Exp.substEnv γ e := by
  apply Exp.substEnv_congr
  intro z hz
  exact REnv.write_other γ y v (by rintro rfl; exact h hz)

/-- Key lemma for the lam/letin cases: opening the binder with a fresh `z` and
    then closing under `γ.write z va` equals closing the body under `γ` and then
    plugging `va` into the bound position. -/
theorem Exp.substEnv_write_openVar (e : Exp) (γ : REnv) (va : Val) (z : EVar) (k : Nat)
    (hz_fv : z ∉ e.fv) (hγ : ∀ w ∈ e.fv, Val.lc (γ.map w)) :
    Exp.substEnv (γ.write z va) (Exp.openVar k z e) =
      Exp.openExp k va.toExp (Exp.substEnv γ e) := by
  induction e generalizing k with
  | bvar j =>
    by_cases hjk : j = k
    · subst hjk; simp [Exp.openVar, Exp.substEnv, Exp.openExp]
    · simp [Exp.openVar, Exp.substEnv, Exp.openExp, hjk]
  | iconst _ | bconst _ | unreach => rfl
  | fvar y =>
    have hyz : z ≠ y := fun he => hz_fv (by simp [Exp.fv, he])
    show Exp.substEnv (γ.write z va) (.fvar y) = Exp.openExp k va.toExp ((γ.map y).toExp)
    rw [Exp.substEnv_fvar, REnv.write_other γ z va hyz]
    exact (Exp.openExp_of_lc_at _ k va.toExp
      (Exp.lc_at_mono _ (Nat.zero_le k)
        (Val.toExp_lc_at_zero (hγ y (by simp [Exp.fv]))))).symm
  | lam e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih (k+1) (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | fix e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih (k+2) (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | ann e t ih | tapp e t ih | tabs t e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | not e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ (k+1) hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ k hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    obtain ⟨⟨hz₀, hz₁⟩, hz₂⟩ := hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₀ k hz₀ (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₁ k hz₁ (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ k hz₂ (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ k hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ (k+2) hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | ctor C j τs e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | case e n alts ih ihs =>
    simp only [Exp.fv, List.mem_append, not_or, List.mem_flatMap, List.mem_finRange,
      true_and, not_exists] at hz_fv
    have hmem : ∀ j, ∀ w ∈ (alts j).fv, w ∈ (Exp.case e n alts).fv := fun j w hw => by
      simp only [Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
      exact Or.inr ⟨j, hw⟩
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
    congr 1; funext j
    exact ihs j (k+1) (hz_fv.2 j) (fun w hw => hγ w (hmem j w hw))

/-- `write` (on the name map) commutes with `push` (on the de Bruijn stack):
    they touch disjoint fields of `REnv`. -/
theorem REnv.push_write_comm (γ : REnv) (w : Val) (x : EVar) (v : Val) :
    (γ.write x v).push w = (γ.push w).write x v := by
  apply REnv.ext <;> rfl


/-! ## Rename keystone: interpretation

  Renaming `x → y` corresponds to copying `y`'s cell into `x` with the Val-level
  `write`. -/

theorem REnv.get_write_other (b : Base) (γ : REnv) (x : EVar) (v : Val) {y : EVar}
    (h : x ≠ y) : REnv.get b (γ.write x v) y = REnv.get b γ y := by
  have hxy : (x == y) = false := by simp [h]
  simp [REnv.get, REnv.lookup, hxy]

/-! ## write-at-fresh-variable invariance of interpretation

  Writing *any* `Val` at a name not occurring in a term/formula leaves its
  interpretation unchanged. Generalizes `interp_update_fresh_*` to arbitrary
  written values (incl. closures) — needed because the merged extension
  `γ.write`.write may store a closure at a fresh higher-order binder. -/

theorem Term.interp_write_fresh {b : Base} (t : Term b)
    (x : EVar) (v : Val) (γ : REnv) (h : x ∉ t.fv) :
    Term.interp (γ.write x v) t = Term.interp γ t := by
  induction t with
  | const _ _ => rfl
  | bvar bv _ => cases bv <;> rfl
  | fvar bv y =>
    have hxy : x ≠ y := fun he => h (by subst he; simp [Term.fv])
    exact REnv.get_write_other bv γ x v hxy
  | mbvar _ _ => rfl
  | ibvar _ | bbvar _ => rfl
  | mfvar m y =>
    have hxy : x ≠ y := fun he => h (by subst he; simp [Term.fv])
    simp [Term.interp, REnv.write, hxy]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]
  | leqI t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]
  | ite _ c t e ihc iht ihe =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ihc h.1.1, iht h.1.2, ihe h.2]
  | not t ih => simp only [Term.interp, ih h]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]

theorem Formula.interp_write_fresh (φ : Formula)
    (x : EVar) (v : Val) (γ : REnv)
    (hfv : x ∉ φ.fv) :
    Formula.interp (γ.write x v) φ ↔ Formula.interp γ φ := by
  have not_mem_l : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₁ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inl ha))
  have not_mem_r : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₂ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inr ha))
  induction φ generalizing γ with
  | tt => simp [Formula.interp]
  | ff => simp [Formula.interp]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp,
      Term.interp_write_fresh t₁ x v γ (not_mem_l _ _ _ hfv),
      Term.interp_write_fresh t₂ x v γ (not_mem_r _ _ _ hfv)]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, List.mem_append, not_or] at hfv
    simp only [Formula.interp, ih₁ γ hfv.1, ih₂ γ hfv.2]
  | not φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    exact not_congr (ih γ hfv)
  | ex _ φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    refine exists_congr (fun n => ?_)
    rw [REnv.push_write_comm]
    exact ih (γ.push _) hfv
  | all _ φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    refine forall_congr' (fun n => ?_)
    rw [REnv.push_write_comm]
    exact ih (γ.push _) hfv

/-! ## Model-level bridge for the shifting open: `openBVar` = `insertBV`

  `openBVar k` opens the de Bruijn level `k` to the free name `x` and shifts
  deeper indices down; interpreting the opened term through a `write`-updated
  name map (`x ↦ w`) agrees with interpreting the original through a value
  `insertBV`-ed into the de Bruijn stack at level `k`. The bridge is
  **premise-free** beyond `k ≤ len` and freshness `x ∉ fv` — no well-formedness
  hypothesis — which is what keeps the VCGen soundness chain WF-free. ν-opening
  is the `k = 0` case (`insertBV 0 = push`), which is what lets `Subtyp.refine`
  be stated in *opened* form (mirroring `Subtyp.arrow`). We prove the general
  `insertBV k` form so the induction goes under `Formula` quantifiers. -/

theorem REnv.write_push (γ : REnv) (x : EVar) (w u : Val) :
    (γ.write x w).push u = (γ.push u).write x w := rfl

theorem Term.interp_openBVar {b : Base} (x : EVar) (w : Val) :
    ∀ (t : Term b) (γ : REnv) (k : Nat),
      k ≤ γ.bv.length → x ∉ t.fv →
      Term.interp (γ.write x w) (t.openBVar k x) = Term.interp (γ.insertBV k w) t := by
  intro t
  induction t with
  | const b c => intro γ k _ _; rfl
  | bvar b j =>
      intro γ k hk _
      by_cases hjk : j = k
      · subst hjk
        simp only [Term.openBVar, Term.interp, REnv.get, REnv.lookup,
          REnv.write, beq_self_eq_true, if_true, REnv.getBV, REnv.insertBV_bv, REnv.insertBV_sorts,
          List.getElem?_insertIdx_self, hk, if_true, Option.getD_some]
      · simp only [Term.openBVar, if_neg hjk, Term.interp, REnv.getBV,
          REnv.insertBV_bv, REnv.insertBV_sorts]
        by_cases hlt : k < j
        · rw [if_pos hlt, Term.interp, REnv.getBV,
            List.getElem?_insertIdx_of_gt hlt]
        · rw [if_neg hlt, Term.interp, REnv.getBV,
            List.getElem?_insertIdx_of_lt (by omega)]
  | fvar b y =>
      intro γ k _ hx
      simp only [Term.fv, List.mem_singleton] at hx
      simp only [Term.openBVar, Term.interp, REnv.get, REnv.lookup, REnv.write,
        REnv.insertBV_map, REnv.insertBV_sorts, beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true,
        if_false]
  | mbvar m j =>
      intro γ k hk _
      by_cases hjk : j = k
      · subst hjk
        simp only [Term.openBVar, Term.interp, REnv.write, beq_self_eq_true, if_true,
          REnv.insertBV_bv, REnv.insertBV_sorts, List.getElem?_insertIdx_self, hk, if_true,
          Option.getD_some]
      · simp only [Term.openBVar, if_neg hjk]
        by_cases hlt : k < j
        · rw [if_pos hlt]
          simp only [Term.interp, REnv.insertBV_bv, REnv.insertBV_sorts]
          rw [List.getElem?_insertIdx_of_gt hlt]
        · rw [if_neg hlt]
          simp only [Term.interp, REnv.insertBV_bv, REnv.insertBV_sorts]
          rw [List.getElem?_insertIdx_of_lt (by omega)]
  | mfvar m y =>
      intro γ k _ hx
      simp only [Term.fv, List.mem_singleton] at hx
      simp only [Term.openBVar, Term.interp, REnv.write, REnv.insertBV_map, REnv.insertBV_sorts,
        beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true, if_false]
  | ibvar j =>
      intro γ k hk _
      by_cases hjk : j = k
      · subst hjk
        simp only [Term.openBVar, Term.interp, REnv.get, REnv.lookup, REnv.write,
          beq_self_eq_true, if_true, REnv.insertBV_bv, REnv.insertBV_sorts,
          List.getElem?_insertIdx_self, hk, if_true, Option.getD_some, Base.resolve]
      · simp only [Term.openBVar, if_neg hjk]
        by_cases hlt : k < j
        · rw [if_pos hlt]
          simp only [Term.interp, REnv.insertBV_bv, REnv.insertBV_sorts]
          rw [List.getElem?_insertIdx_of_gt hlt]
        · rw [if_neg hlt]
          simp only [Term.interp, REnv.insertBV_bv, REnv.insertBV_sorts]
          rw [List.getElem?_insertIdx_of_lt (by omega)]
  | bbvar j =>
      intro γ k hk _
      by_cases hjk : j = k
      · subst hjk
        simp only [Term.openBVar, Term.interp, REnv.get, REnv.lookup, REnv.write,
          beq_self_eq_true, if_true, REnv.insertBV_bv, REnv.insertBV_sorts,
          List.getElem?_insertIdx_self, hk, if_true, Option.getD_some, Base.resolve]
      · simp only [Term.openBVar, if_neg hjk]
        by_cases hlt : k < j
        · rw [if_pos hlt]
          simp only [Term.interp, REnv.insertBV_bv, REnv.insertBV_sorts]
          rw [List.getElem?_insertIdx_of_gt hlt]
        · rw [if_neg hlt]
          simp only [Term.interp, REnv.insertBV_bv, REnv.insertBV_sorts]
          rw [List.getElem?_insertIdx_of_lt (by omega)]
  | add t₁ t₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Term.fv, List.mem_append, not_or] at hx
      simp only [Term.openBVar, Term.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | leqI t₁ t₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Term.fv, List.mem_append, not_or] at hx
      simp only [Term.openBVar, Term.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | ite _ c t e ihc iht ihe =>
      intro γ k hk hx
      simp only [Term.fv, List.mem_append, not_or] at hx
      simp only [Term.openBVar, Term.interp, ihc γ k hk hx.1.1, iht γ k hk hx.1.2,
        ihe γ k hk hx.2]
      rfl
  | not t ih =>
      intro γ k hk hx
      simp only [Term.fv] at hx
      simp only [Term.openBVar, Term.interp, ih γ k hk hx]
  | and t₁ t₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Term.fv, List.mem_append, not_or] at hx
      simp only [Term.openBVar, Term.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]

theorem Formula.interp_openBVar (x : EVar) (w : Val) :
    ∀ (φ : Formula) (γ : REnv) (k : Nat),
      k ≤ γ.bv.length → x ∉ φ.fv →
      (Formula.interp (γ.write x w) (φ.openBVar k x) ↔ Formula.interp (γ.insertBV k w) φ) := by
  intro φ
  induction φ with
  | tt => intro γ k _ _; simp [Formula.openBVar, Formula.interp]
  | ff => intro γ k _ _; simp [Formula.openBVar, Formula.interp]
  | eq b t₁ t₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp,
        Term.interp_openBVar x w t₁ γ k hk hx.1,
        Term.interp_openBVar x w t₂ γ k hk hx.2]
      exact Iff.rfl
  | leq _ t₁ t₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp,
        Term.interp_openBVar x w t₁ γ k hk hx.1,
        Term.interp_openBVar x w t₂ γ k hk hx.2]
      exact Iff.rfl
  | and φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | or φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | not φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.openBVar, Formula.interp, ih γ k hk hx]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | ex b φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.openBVar, Formula.interp]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [REnv.write_push] at hv
        rw [REnv.push_insertBV_comm]
        exact (ih (γ.push (Val.inj (b.resolve γ.sorts) v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mp hv
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [REnv.write_push]
        rw [REnv.push_insertBV_comm] at hv
        exact (ih (γ.push (Val.inj (b.resolve γ.sorts) v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mpr hv
  | all b φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.openBVar, Formula.interp]
      constructor
      · intro h v
        rw [REnv.push_insertBV_comm]
        have := h v
        rw [REnv.write_push] at this
        exact (ih (γ.push (Val.inj (b.resolve γ.sorts) v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mp this
      · intro h v
        rw [REnv.write_push]
        have := h v
        rw [REnv.push_insertBV_comm] at this
        exact (ih (γ.push (Val.inj (b.resolve γ.sorts) v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mpr this

/-- Model-level bridge (refinement level): interpreting the `openBVar`-opened
    refinement against a `write`-updated name-map slot equals interpreting the
    original against a value `insertBV`-ed into the de Bruijn stack at level `k`.
    Premise-free beyond `k ≤ len` and freshness. The `k = 0` case
    (`insertBV 0 = push`) bridges the generator's named `.all` binder and the
    opened `Subtyp.refine` with the `push`-based denotation. -/
theorem Refinement.interp_openBVar (κ : KEnv) (r : Refinement) (γ : REnv)
    (x : EVar) (w : Val) (k : Nat) (hk : k ≤ γ.bv.length) (hx : x ∉ r.fv) :
    Refinement.interp κ (r.openBVar k x) (γ.write x w) ↔
    Refinement.interp κ r (γ.insertBV k w) := by
  induction r with
  | conj r₁ r₂ ih₁ ih₂ =>
      simp only [Refinement.fv, List.mem_append, not_or] at hx
      simp only [Refinement.openBVar, Refinement.interp]
      exact and_congr (ih₁ hx.1) (ih₂ hx.2)
  | fmla φ =>
      simp only [Refinement.openBVar, Refinement.interp]
      exact Formula.interp_openBVar x w φ γ k hk (by simpa [Refinement.fv] using hx)
  | kapp kn args =>
      have hmap :
          (List.map (fun a => Base.canonArg (γ.write x w).sorts a.1 (Term.interp (γ.write x w) a.2))
            (List.map (fun a => (⟨a.1, Term.openBVar k x a.2⟩ : Σ b : Base, Term b)) args))
          = List.map (fun a => Base.canonArg (γ.insertBV k w).sorts a.1
              (Term.interp (γ.insertBV k w) a.2)) args := by
        rw [List.map_map]
        apply List.map_congr_left
        intro a ha
        have hxa : x ∉ Term.fv a.2 := by
          simp only [Refinement.fv] at hx
          exact fun h => hx (List.mem_flatMap.mpr ⟨a, ha, h⟩)
        have h := Term.interp_openBVar x w a.2 γ k hk hxa
        simp only [Function.comp_apply, h]
        rfl
      simp only [Refinement.openBVar, Refinement.interp, hmap]

theorem DEnv.payload?_lt {de : DEnv} {C : String} {j m : Nat} {P : Ty}
    (hm : de.nCtors C = some m) (hP : de.payload? C j = some P) : j < m := by
  simp only [DEnv.nCtors, DEnv.payload?] at hm hP
  cases hd : de.decl? C with
  | none => simp [hd] at hm
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq, Option.bind_some] at hm hP
    subst hm
    cases h : d.ctors[j]? with
    | none => simp [h] at hP
    | some c => exact (List.getElem?_eq_some_iff.mp h).1

theorem DEnv.payload?_of_lt {de : DEnv} {C : String} {j m : Nat}
    (hm : de.nCtors C = some m) (hj : j < m) : ∃ P, de.payload? C j = some P := by
  simp only [DEnv.nCtors, DEnv.payload?] at hm ⊢
  cases hd : de.decl? C with
  | none => simp [hd] at hm
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq, Option.bind_some] at hm ⊢
    subst hm
    exact ⟨d.ctors[j].2, by simp [List.getElem?_eq_getElem hj]⟩

/-- What `instOK` guarantees. -/
theorem DEnv.instOK_spec {de : DEnv} {C : String} {τs : List Ty} (h : de.instOK C τs = true) :
    ∃ d, de.decl? C = some d ∧ d.params.length = τs.length ∧
      (∀ i (hi : i < τs.length), ∃ k, d.params[i]? = some k ∧ Kind.le τs[i].kindOf k ∧
        τs[i].wfB [] [] = true) ∧
      ∀ c ∈ d.ctors, Ty.instTysOK d.params 0 τs c.2 = true := by
  unfold DEnv.instOK at h
  cases hd : de.decl? C with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hlen, hargs⟩, hctors⟩ := h
    refine ⟨d, rfl, hlen, fun i hi => ?_, hctors⟩
    have hmem : (τs[i], d.params[i]'(by omega)) ∈ List.zip τs d.params := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [List.length_zip]; omega, by simp [List.getElem_zip]⟩
    have := hargs _ hmem
    simp only [decide_eq_true_eq] at this
    exact ⟨_, List.getElem?_eq_getElem (by omega), this⟩

/-- The type arguments of a legal instance are well-formed. -/
theorem Formula.hasBVar_conjAll {b : Base} {k : Nat} : ∀ (φs : List Formula),
    Formula.hasBVar b k (Formula.conjAll φs) → ∃ φ ∈ φs, Formula.hasBVar b k φ
  | [], h => by simp [Formula.conjAll, Formula.hasBVar] at h
  | φ :: φs, h => by
    simp only [Formula.conjAll, Formula.hasBVar] at h
    rcases h with h | h
    · exact ⟨φ, List.mem_cons_self, h⟩
    · obtain ⟨ψ, hψ, h⟩ := Formula.hasBVar_conjAll φs h
      exact ⟨ψ, List.mem_cons_of_mem _ hψ, h⟩

theorem MBody.toTerm_noBVar {fld : Nat → Term .int} {fldB : Nat → Term .bool}
    {msr : String → Nat → Term .int}
    (hf : ∀ i b k, ¬ Term.hasBVar b k (fld i)) (hfB : ∀ i b k, ¬ Term.hasBVar b k (fldB i))
    (hm : ∀ m i b k, ¬ Term.hasBVar b k (msr m i)) :
    ∀ (body : MBody) b k, ¬ Term.hasBVar b k (body.toTerm fld fldB msr)
  | .const _, b, k => by simp [MBody.toTerm, Term.hasBVar]
  | .field i, b, k => hf i b k
  | .meas m i, b, k => hm m i b k
  | .add x y, b, k => by
    simp only [MBody.toTerm, Term.hasBVar, not_or]
    exact ⟨MBody.toTerm_noBVar hf hfB hm x b k, MBody.toTerm_noBVar hf hfB hm y b k⟩
  | .iteLe x y t e, b, k => by
    simp only [MBody.toTerm, Term.hasBVar, not_or]
    exact ⟨⟨MBody.toTerm_noBVar hf hfB hm x b k, MBody.toTerm_noBVar hf hfB hm y b k⟩,
      MBody.toTerm_noBVar hf hfB hm t b k, MBody.toTerm_noBVar hf hfB hm e b k⟩
  | .iteB i t e, b, k => by
    simp only [MBody.toTerm, Term.hasBVar, not_or]
    exact ⟨hfB i b k, MBody.toTerm_noBVar hf hfB hm t b k, MBody.toTerm_noBVar hf hfB hm e b k⟩

/-- A constructor's measure facts mention no sorted bound variable (they read
    ν and the fields only through measures). -/
theorem DEnv.ctorRefine_noBVar (de : DEnv) (C : String) (j : Nat) (e : Exp) :
    ∀ b k, ¬ (de.ctorRefine C j e).hasBVar b k := by
  intro b k h
  unfold DEnv.ctorRefine at h
  split at h
  · simp only [DEnv.ctorFacts, Refinement.hasBVar] at h
    obtain ⟨φ, hφ, h⟩ := Formula.hasBVar_conjAll _ h
    simp only [List.mem_map] at hφ
    obtain ⟨mb, _, rfl⟩ := hφ
    simp only [Formula.hasBVar, Term.hasBVar, false_or] at h
    exact MBody.toTerm_noBVar (fun _ _ _ h => by split at h <;> simp [Term.hasBVar] at h)
      (fun _ _ _ h => by split at h <;> simp [Term.hasBVar] at h)
      (fun _ _ _ _ h => by split at h <;> simp [Term.hasBVar] at h) _ _ _ h
  · simp [Refinement.hasBVar, Formula.hasBVar] at h

theorem DEnv.caseFacts_noBVar (de : DEnv) (C : String) (j n : Nat) (x : EVar) :
    ∀ b k, ¬ (de.caseFacts C j n x).hasBVar b k := by
  intro b k h
  simp only [DEnv.caseFacts, Refinement.hasBVar] at h
  obtain ⟨φ, hφ, h⟩ := Formula.hasBVar_conjAll _ h
  simp only [List.mem_map] at hφ
  obtain ⟨mb, _, rfl⟩ := hφ
  simp only [Formula.hasBVar, Term.hasBVar, false_or] at h
  exact MBody.toTerm_noBVar (fun _ _ _ h => by simp [Term.hasBVar] at h)
    (fun _ _ _ h => by simp [Term.hasBVar] at h)
    (fun _ _ _ _ h => by simp [Term.hasBVar] at h) _ _ _ h

theorem Ty.WFBVarCtx_strengthenUnit {r : Refinement} (hr : ∀ b k, ¬ r.hasBVar b k) :
    ∀ (n : Nat) (t : Ty) (ctx : List (Option Base)), Ty.WFBVarCtx ctx t →
      Ty.WFBVarCtx ctx (t.strengthenUnit n r)
  | 0, .refine b r', ctx, h => by
    simp only [Ty.strengthenUnit, Ty.WFBVarCtx, Refinement.hasBVar] at h ⊢
    rintro b' k (hk | hk)
    · exact h b' k hk
    · exact absurd hk (hr b' k)
  | n + 1, .prod s t, ctx, h => by
    simp only [Ty.strengthenUnit, Ty.WFBVarCtx] at h ⊢
    exact ⟨h.1, Ty.WFBVarCtx_strengthenUnit hr n t _ h.2⟩
  | 0, .arrow _ _, _, h | 0, .forall _ _, _, h | 0, .prod _ _, _, h | 0, .data _ _ _ _, _, h
  | _ + 1, .refine _ _, _, h | _ + 1, .arrow _ _, _, h | _ + 1, .forall _ _, _, h
  | _ + 1, .data _ _ _ _, _, h => by
    simpa [Ty.strengthenUnit] using h

theorem DEnv.altTy_WFBVars (de : DEnv) (C : String) (j : Nat) (x? : Option EVar) {tz : Ty}
    (h : Ty.WFBVars tz) : Ty.WFBVars (de.altTy C j x? tz) := by
  cases x? with
  | none => exact h
  | some x => exact Ty.WFBVarCtx_strengthenUnit (DEnv.caseFacts_noBVar _ _ _ _ _) _ tz [] h

theorem DEnv.instOK_WFBVars {de : DEnv} {C : String} {τs : List Ty} {r : Refinement}
    (h : de.instOK C τs = true) (hr : ∀ b k, ¬ r.hasBVar b k) :
    Ty.WFBVars (Ty.dataL C τs r) := by
  obtain ⟨d, _, _, hargs, _⟩ := DEnv.instOK_spec h
  refine ⟨fun b k h => absurd h (hr b k), fun i => ?_⟩
  obtain ⟨_, _, _, hw⟩ := hargs i.val i.isLt
  exact Ty.wfB_WFBVarCtx _ hw

/-- The first stage checked by `instTysOK` is the full instantiation. -/
theorem Ty.instTysOK_wfB {ks : List Kind} {i : Nat} {τs : List Ty} {P : Ty}
    (h : Ty.instTysOK ks i τs P = true) : (Ty.instTysFrom i τs P).wfB (ks.take i) [] = true := by
  cases τs with
  | nil => simpa [Ty.instTysOK, Ty.instTysFrom] using h
  | cons τ τs =>
    simp only [Ty.instTysOK, Bool.and_eq_true] at h
    exact h.1

/-- A payload at a legal instance is a closed well-formed type. -/
theorem DEnv.instOK_payload_wfB {de : DEnv} {C : String} {τs : List Ty} {j : Nat} {P : Ty}
    (h : de.instOK C τs = true) (hP : de.payload? C j = some P) :
    (Ty.instTys τs P).wfB [] [] = true := by
  obtain ⟨d, hd, _, _, hctors⟩ := DEnv.instOK_spec h
  simp only [DEnv.payload?, hd, Option.bind_some, Option.map_eq_some_iff] at hP
  obtain ⟨c, hc, rfl⟩ := hP
  have := Ty.instTysOK_wfB (hctors c (List.mem_of_getElem? hc))
  simpa using this

theorem List.mem_of_lookup_eq_some' {β : Type} :
    ∀ {l : List (String × β)} {a : String} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (a', b') :: tl, a, b, h => by
    simp only [List.lookup] at h
    by_cases ha : a = a'
    · subst ha
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h; simp
    · have hne : (a == a') = false := by simp [ha]
      simp only [hne] at h
      exact List.mem_cons_of_mem _ (List.mem_of_lookup_eq_some' h)

/-- The declaration and payload behind a successful `payload?` lookup. -/
theorem DEnv.payload?_mem {de : DEnv} {C : String} {j : Nat} {P : Ty}
    (hP : de.payload? C j = some P) :
    ∃ d c, de.decl? C = some d ∧ (C, d) ∈ de ∧ c ∈ d.ctors ∧ c.2 = P := by
  simp only [DEnv.payload?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hP
  obtain ⟨d, hd, c, hc, rfl⟩ := hP
  exact ⟨d, c, hd, List.mem_of_lookup_eq_some' hd, List.mem_of_getElem? hc, rfl⟩

theorem DEnv.wfB_payload_all {de : DEnv} (h : de.wfB = true) {C : String} {j : Nat} {P : Ty}
    (hP : de.payload? C j = some P) :
    ∃ d, de.decl? C = some d ∧ P.fv = [] ∧ P.ftv = [] ∧ Ty.varOK de d.variances 0 .pos P = true := by
  obtain ⟨d, c, hd, hmem, hc, rfl⟩ := DEnv.payload?_mem hP
  simp only [DEnv.wfB, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 (C, d) hmem c hc
  simp only [Bool.and_eq_true, List.isEmpty_iff] at this
  exact ⟨d, hd, this.1.1, this.1.2, this.2⟩

/-- Payloads of well-formed declarations have no free term or type variables. -/
theorem DEnv.wfB_payload {de : DEnv} (h : de.wfB = true) {C : String} {j : Nat} {P : Ty}
    (hP : de.payload? C j = some P) : P.fv = [] ∧ P.ftv = [] := by
  obtain ⟨_, _, h1, h2, _⟩ := DEnv.wfB_payload_all h hP
  exact ⟨h1, h2⟩

/-- The facts a legal instance gives about one constructor's payload. -/
theorem DEnv.instOK_payload_ok {de : DEnv} {C : String} {τs : List Ty} {j : Nat} {P : Ty}
    (h : de.instOK C τs = true) (hP : de.payload? C j = some P) :
    ∃ ks : List Kind, ks.length = τs.length ∧
      (∀ l (hl : l < τs.length), ∃ kd, ks[l]? = some kd ∧ Kind.le τs[l].kindOf kd ∧
        τs[l].wfB [] [] = true) ∧
      Ty.instTysOK ks 0 τs P = true := by
  obtain ⟨d, hd, hlen, hargs, hctors⟩ := DEnv.instOK_spec h
  simp only [DEnv.payload?, hd, Option.bind_some, Option.map_eq_some_iff] at hP
  obtain ⟨c, hc, rfl⟩ := hP
  exact ⟨d.params, hlen, hargs, hctors c (List.mem_of_getElem? hc)⟩

/-- The last stage checked by `instTysOK` is the payload itself. -/
theorem Ty.instTysOK_last {ks : List Kind} {P : Ty} :
    ∀ {i : Nat} {τs : List Ty}, Ty.instTysOK ks i τs P = true →
      P.wfB (ks.take (i + τs.length)) [] = true
  | i, [], h => by simpa [Ty.instTysOK] using h
  | i, τ :: τs, h => by
    simp only [Ty.instTysOK, Bool.and_eq_true] at h
    have := Ty.instTysOK_last h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

end STLC
