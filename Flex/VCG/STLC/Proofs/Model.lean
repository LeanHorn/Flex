import Flex.VCG.STLC.Spec.Denotation
import Flex.VCG.STLC.Proofs.Semantics
import Flex.VCG.STLC.Checker.Operations

open STLC

/-! # Basic lemmas about the denotation -/

namespace STLC

theorem SemTy.ints_fits (k : Kind) : SemTy.ints.Fits k := by
  cases k with
  | B => exact fun _ v ⟨n, h⟩ => by subst h; rfl
  | star => trivial

/-- Well-kindedness: every free type variable is interpreted by a semantic type
    fitting its kind (the kind is carried on the name). -/
def TyEnvSem.WK (δ : TyEnvSem) : Prop := ∀ a : TVar, (δ.fv a).Fits a.2

theorem TyEnvSem.empty_WK (de : DEnv := []) : (TyEnvSem.empty de).WK := by
  intro a
  rcases a with ⟨n, _ | _⟩
  · exact SemTy.ints_fits _
  · trivial

/-- Expression relation: with exactly `k` fuel, `e` does not get stuck, and any
    value it returns with `m` fuel left is good at index `m`. -/
def ExpDenote (κ : KEnv) (δ : TyEnvSem) (k : Nat) (t : Ty) (γ : REnv) (e : Exp) : Prop :=
  ∃ o, Eval k e o ∧ ∀ v m, o = .val v m → TyDenote κ δ m t γ v

/-- Downward closure of base denotations. -/
theorem BaseDen.mono {δ : TyEnvSem} {j k : Nat} {b : Base} {v : Val}
    (hjk : j ≤ k) (h : BaseDen δ k b v) : BaseDen δ j b v := by
  cases b with
  | int | bool => exact h
  | tbvar i => exact SemTy.mono _ hjk h
  | tfvar a => exact SemTy.mono _ hjk h

/-- Downward closure: a value good for `k` steps is good for fewer. -/
theorem TyDenote.mono {κ : KEnv} {δ : TyEnvSem} {j k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (hjk : j ≤ k) (h : TyDenote κ δ k t γ v) : TyDenote κ δ j t γ v := by
  induction t generalizing δ γ v with
  | refine b r =>
    simp only [TyDenote] at h ⊢
    exact ⟨BaseDen.mono hjk h.1, h.2⟩
  | arrow s t =>
    simp only [TyDenote] at h ⊢
    obtain ⟨hf, hlc, hcl, her, hLR⟩ := h
    exact ⟨hf, hlc, hcl, her, fun i hi => hLR i (by omega)⟩
  | «forall» kd t ih =>
    simp only [TyDenote] at h ⊢
    exact fun R hR => ih (h R hR)
  | prod s t ihs iht =>
    simp only [TyDenote] at h ⊢
    obtain ⟨v₁, v₂, rfl, h₁, h₂⟩ := h
    exact ⟨v₁, v₂, rfl, ihs h₁, iht h₂⟩
  | data C n args r =>
    simp only [TyDenote] at h ⊢
    obtain ⟨hlc, hcl, her, hr, j, w, P, hv, hP, hpay⟩ := h
    exact ⟨hlc, hcl, her, hr, j, w, P, hv, hP, fun i hi => hpay i (by omega)⟩

end STLC
