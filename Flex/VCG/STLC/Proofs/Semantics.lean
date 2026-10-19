import Flex.VCG.STLC.Spec.Semantics

open STLC

/-! # Lemmas about evaluation -/

namespace STLC

/-- Evaluation never creates fuel. -/
theorem Eval.fuel_le {n : Nat} {e : Exp} {v : Val} {m : Nat}
    (h : Eval n e (.val v m)) : m ≤ n := by
  generalize ho : Outcome.val v m = o at h
  induction h generalizing v m <;> cases ho <;> grind

/-- A value's syntax evaluates to itself, consuming no fuel. -/
theorem Eval.toExp (n : Nat) (v : Val) : Eval n v.toExp (.val v n) := by
  induction v with
  | pair v₁ v₂ ih₁ ih₂ => exact .pair ih₁ ih₂
  | ctor C j w ih => exact .ctor ih
  | _ => constructor

/-- ...and that is the only thing it evaluates to. -/
theorem Eval.toExp_inv {n : Nat} {v : Val} {o : Outcome}
    (h : Eval n v.toExp o) : o = .val v n := by
  induction v generalizing n o with
  | pair v₁ v₂ ih₁ ih₂ =>
    cases h with
    | pair h₁ h₂ => cases ih₁ h₁; cases ih₂ h₂; rfl
    | pair_to₁ h₁ => cases ih₁ h₁
    | pair_to₂ h₁ h₂ => cases ih₁ h₁; cases ih₂ h₂
  | ctor C j w ih =>
    cases h with
    | ctor h => cases ih h; rfl
    | ctor_to h => cases ih h
  | _ => cases h <;> rfl

/-- Fuel-indexed evaluation is deterministic. -/
theorem Eval.det {n : Nat} {e : Exp} {o₁ o₂ : Outcome}
    (h₁ : Eval n e o₁) (h₂ : Eval n e o₂) : o₁ = o₂ := by
  induction h₁ generalizing o₂ with
  | ann _ ih => cases h₂ with | ann h => exact ih h
  | tabs _ ih => cases h₂ with | tabs h => exact ih h
  | tapp _ ih => cases h₂ with | tapp h => exact ih h
  | letin _ _ ih₁ ih₂ =>
    cases h₂ with
    | letin h₁' h₂' => cases ih₁ h₁'; exact ih₂ h₂'
    | letin_to h => cases ih₁ h
  | letin_to _ ih =>
    cases h₂ with
    | letin h _ => cases ih h
    | letin_to => rfl
  | app _ _ hap _ ih₁ ih₂ ih₃ =>
    cases h₂ with
    | app h₁' h₂' hap' h₃' =>
      cases ih₁ h₁'; cases ih₂ h₂'; rw [hap] at hap'; cases hap'; exact ih₃ h₃'
    | app_tick h₁' h₂' _ => cases ih₁ h₁'; cases ih₂ h₂'
    | app_to₁ h => cases ih₁ h
    | app_to₂ h₁' h₂' => cases ih₁ h₁'; cases ih₂ h₂'
  | app_tick _ _ _ ih₁ ih₂ =>
    cases h₂ with
    | app h₁' h₂' _ _ => cases ih₁ h₁'; cases ih₂ h₂'
    | app_tick => rfl
    | app_to₁ h => cases ih₁ h
    | app_to₂ h₁' h₂' => cases ih₁ h₁'; cases ih₂ h₂'
  | app_to₁ _ ih =>
    cases h₂ with
    | app h _ _ _ | app_tick h _ _ | app_to₂ h _ => cases ih h
    | app_to₁ => rfl
  | app_to₂ _ _ ih₁ ih₂ =>
    cases h₂ with
    | app h₁' h₂' _ _ | app_tick h₁' h₂' _ => cases ih₁ h₁'; cases ih₂ h₂'
    | app_to₁ h => cases ih₁ h
    | app_to₂ => rfl
  | leq _ _ hc ih₁ ih₂ =>
    cases h₂ with
    | leq h₁' h₂' hc' => cases ih₁ h₁'; cases ih₂ h₂'; rw [hc] at hc'; cases hc'; rfl
    | leq_to₁ h => cases ih₁ h
    | leq_to₂ h₁' h₂' => cases ih₁ h₁'; cases ih₂ h₂'
  | add _ _ ih₁ ih₂ | and_ _ _ ih₁ ih₂ =>
    cases h₂ <;> rename_i h₁' h₂' <;> first
      | (cases ih₁ h₁'; cases ih₂ h₂'; rfl)
      | (cases ih₁ h₁'; cases ih₂ h₂')
      | cases ih₁ h₂'
  | add_to₁ _ ih | leq_to₁ _ ih | and_to₁ _ ih =>
    cases h₂ <;> first | rfl | (rename_i h _; cases ih h)
  | add_to₂ _ _ ih₁ ih₂ | leq_to₂ _ _ ih₁ ih₂ | and_to₂ _ _ ih₁ ih₂ =>
    cases h₂ <;> first
      | rfl
      | (rename_i h₁' h₂'; cases ih₁ h₁'; cases ih₂ h₂')
      | (rename_i h; cases ih₁ h)
  | not_ _ ih =>
    cases h₂ with
    | not_ h => cases ih h; rfl
    | not_to h => cases ih h
  | not_to _ ih =>
    cases h₂ with
    | not_ h => cases ih h
    | not_to => rfl
  | ite_t _ _ ih₀ ih₁ =>
    cases h₂ with
    | ite_t h₀' h₁' => cases ih₀ h₀'; exact ih₁ h₁'
    | ite_f h₀' _ => cases ih₀ h₀'
    | ite_to h => cases ih₀ h
  | ite_f _ _ ih₀ ih₂ =>
    cases h₂ with
    | ite_t h₀' _ => cases ih₀ h₀'
    | ite_f h₀' h₂' => cases ih₀ h₀'; exact ih₂ h₂'
    | ite_to h => cases ih₀ h
  | ite_to _ ih =>
    cases h₂ with
    | ite_t h _ | ite_f h _ => cases ih h
    | ite_to => rfl
  | pair _ _ ih₁ ih₂ =>
    cases h₂ with
    | pair h₁' h₂' => cases ih₁ h₁'; cases ih₂ h₂'; rfl
    | pair_to₁ h => cases ih₁ h
    | pair_to₂ h₁' h₂' => cases ih₁ h₁'; cases ih₂ h₂'
  | pair_to₁ _ ih =>
    cases h₂ with
    | pair h _ | pair_to₂ h _ => cases ih h
    | pair_to₁ => rfl
  | pair_to₂ _ _ ih₁ ih₂ =>
    cases h₂ with
    | pair h₁' h₂' => cases ih₁ h₁'; cases ih₂ h₂'
    | pair_to₁ h => cases ih₁ h
    | pair_to₂ => rfl
  | split _ _ ih₁ ih₂ =>
    cases h₂ with
    | split h₁' h₂' => cases ih₁ h₁'; exact ih₂ h₂'
    | split_to h => cases ih₁ h
  | split_to _ ih =>
    cases h₂ with
    | split h _ => cases ih h
    | split_to => rfl
  | ctor _ ih =>
    cases h₂ with
    | ctor h => cases ih h; rfl
    | ctor_to h => cases ih h
  | ctor_to _ ih =>
    cases h₂ with
    | ctor h => cases ih h
    | ctor_to => rfl
  | case _ _ _ ih₁ ih₂ =>
    cases h₂ with
    | case _ h₁' h₂' => cases ih₁ h₁'; exact ih₂ h₂'
    | case_tick _ h => cases ih₁ h
    | case_to h => cases ih₁ h
  | case_tick _ _ ih =>
    cases h₂ with
    | case _ h _ => cases ih h
    | case_tick => rfl
    | case_to h => cases ih h
  | case_to _ ih =>
    cases h₂ with
    | case _ h _ | case_tick _ h => cases ih h
    | case_to => rfl
  | iconst | bconst | lam | fix => cases h₂; rfl

end STLC
