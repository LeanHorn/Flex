import Flex.VCG.STLC.Syntax

open STLC

/-! # Fuel-indexed Big-Step Operational Semantics for STLC (locally nameless)

  Call-by-value big-step semantics over locally-nameless terms, with an explicit
  *fuel* budget so that diverging programs (via `Exp.fix`) have a meaning.

  `Eval n e o` says: running `e` with `n` units of fuel produces outcome `o`,
  which is either `.val v m` (a value `v`, with `m ≤ n` fuel left over) or
  `.timeout` (the budget ran out). Fuel is threaded *cumulatively* through
  sub-evaluations and only consumed by β-steps (function application), which is
  what makes the step-indexed logical relation in `Model.lean` work.

  Stuck states — free variables, `unreach`, applying a non-function, primitive
  operations on ill-typed values — have *no* rule. Type safety (Safety.lean)
  says a well-typed closed program has a derivation for every amount of fuel,
  i.e. it never gets stuck.
-/

namespace STLC

/-- Apply a function value to an argument: the body with the parameter (and,
    for a recursive closure, the self-reference) plugged in. `none` for non-functions. -/
def Val.apply : Val → Val → Option Exp
  | .clos body,  va => some (body.openVal 0 va)
  | .fclos body, va => some ((Exp.openExp 1 (.fix body) body).openVal 0 va)
  | _,           _  => none

/-- Result of a fuel-bounded evaluation. -/
inductive Outcome where
  | val     : Val → Nat → Outcome   -- value, remaining fuel
  | timeout : Outcome

/-- Fuel-indexed big-step evaluation `e ⇓ₙ o` (call-by-value). -/
inductive Eval : Nat → Exp → Outcome → Prop
  | iconst {n i}    : Eval n (.iconst i) (.val (.iconst i) n)
  | bconst {n b}    : Eval n (.bconst b) (.val (.bconst b) n)
  | lam   {n body}  : Eval n (.lam body) (.val (.clos body) n)
  | fix   {n body}  : Eval n (.fix body) (.val (.fclos body) n)
  | ann   {n e t o} : Eval n e o → Eval n (.ann e t) o
  /-- Types are erased: type abstraction and application evaluate their body. -/
  | tabs  {n κ e o} : Eval n e o → Eval n (.tabs κ e) o
  | tapp  {n e t o} : Eval n e o → Eval n (.tapp e t) o
  | letin {n e₁ e₂ v₁ n₁ o} :
      Eval n e₁ (.val v₁ n₁) →
      Eval n₁ (e₂.openVal 0 v₁) o →
      Eval n (.letin e₁ e₂) o
  | letin_to {n e₁ e₂} :
      Eval n e₁ .timeout → Eval n (.letin e₁ e₂) .timeout
  /-- β-step: costs one unit of fuel. -/
  | app {n e₁ e₂ f n₁ va n₂ body o} :
      Eval n e₁ (.val f n₁) →
      Eval n₁ e₂ (.val va (n₂ + 1)) →
      Val.apply f va = some body →
      Eval n₂ body o →
      Eval n (.app e₁ e₂) o
  /-- β-step with no fuel left. -/
  | app_tick {n e₁ e₂ f n₁ va body} :
      Eval n e₁ (.val f n₁) →
      Eval n₁ e₂ (.val va 0) →
      Val.apply f va = some body →
      Eval n (.app e₁ e₂) .timeout
  | app_to₁ {n e₁ e₂} :
      Eval n e₁ .timeout → Eval n (.app e₁ e₂) .timeout
  | app_to₂ {n e₁ e₂ f n₁} :
      Eval n e₁ (.val f n₁) → Eval n₁ e₂ .timeout → Eval n (.app e₁ e₂) .timeout
  | add {n e₁ e₂ a n₁ b n₂} :
      Eval n e₁ (.val (.iconst a) n₁) → Eval n₁ e₂ (.val (.iconst b) n₂) →
      Eval n (.add e₁ e₂) (.val (.iconst (a + b)) n₂)
  | add_to₁ {n e₁ e₂} :
      Eval n e₁ .timeout → Eval n (.add e₁ e₂) .timeout
  | add_to₂ {n e₁ e₂ v n₁} :
      Eval n e₁ (.val v n₁) → Eval n₁ e₂ .timeout → Eval n (.add e₁ e₂) .timeout
  | leq {n e₁ e₂ a n₁ b n₂} :
      Eval n e₁ (.val (.iconst a) n₁) → Eval n₁ e₂ (.val (.iconst b) n₂) →
      Eval n (.leq e₁ e₂) (.val (.bconst (decide (a ≤ b))) n₂)
  | leq_to₁ {n e₁ e₂} :
      Eval n e₁ .timeout → Eval n (.leq e₁ e₂) .timeout
  | leq_to₂ {n e₁ e₂ v n₁} :
      Eval n e₁ (.val v n₁) → Eval n₁ e₂ .timeout → Eval n (.leq e₁ e₂) .timeout
  | not_ {n e b n₁} :
      Eval n e (.val (.bconst b) n₁) → Eval n (.not e) (.val (.bconst (!b)) n₁)
  | not_to {n e} :
      Eval n e .timeout → Eval n (.not e) .timeout
  | and_ {n e₁ e₂ a n₁ b n₂} :
      Eval n e₁ (.val (.bconst a) n₁) → Eval n₁ e₂ (.val (.bconst b) n₂) →
      Eval n (.and e₁ e₂) (.val (.bconst (a && b)) n₂)
  | and_to₁ {n e₁ e₂} :
      Eval n e₁ .timeout → Eval n (.and e₁ e₂) .timeout
  | and_to₂ {n e₁ e₂ v n₁} :
      Eval n e₁ (.val v n₁) → Eval n₁ e₂ .timeout → Eval n (.and e₁ e₂) .timeout
  | ite_t {n e₀ e₁ e₂ n₁ o} :
      Eval n e₀ (.val (.bconst true) n₁) → Eval n₁ e₁ o → Eval n (.ite e₀ e₁ e₂) o
  | ite_f {n e₀ e₁ e₂ n₁ o} :
      Eval n e₀ (.val (.bconst false) n₁) → Eval n₁ e₂ o → Eval n (.ite e₀ e₁ e₂) o
  | ite_to {n e₀ e₁ e₂} :
      Eval n e₀ .timeout → Eval n (.ite e₀ e₁ e₂) .timeout
  | pair {n e₁ e₂ v₁ n₁ v₂ n₂} :
      Eval n e₁ (.val v₁ n₁) → Eval n₁ e₂ (.val v₂ n₂) →
      Eval n (.pair e₁ e₂) (.val (.pair v₁ v₂) n₂)
  | pair_to₁ {n e₁ e₂} :
      Eval n e₁ .timeout → Eval n (.pair e₁ e₂) .timeout
  | pair_to₂ {n e₁ e₂ v n₁} :
      Eval n e₁ (.val v n₁) → Eval n₁ e₂ .timeout → Eval n (.pair e₁ e₂) .timeout
  | split {n e₁ e₂ v₁ v₂ n₁ o} :
      Eval n e₁ (.val (.pair v₁ v₂) n₁) →
      Eval n₁ (Exp.openVal 0 v₂ (Exp.openVal 1 v₁ e₂)) o →
      Eval n (.split e₁ e₂) o
  | split_to {n e₁ e₂} :
      Eval n e₁ .timeout → Eval n (.split e₁ e₂) .timeout
  | ctor {n C j τs e w n₁} :
      Eval n e (.val w n₁) → Eval n (.ctor C j τs e) (.val (.ctor C j w) n₁)
  | ctor_to {n C j τs e} :
      Eval n e .timeout → Eval n (.ctor C j τs e) .timeout
  /-- Matching unfolds a datatype value: costs one unit of fuel. -/
  | case {n e m alts C j w n₁ o} (hj : j < m) :
      Eval n e (.val (.ctor C j w) (n₁ + 1)) →
      Eval n₁ (Exp.openVal 0 w (alts ⟨j, hj⟩)) o →
      Eval n (.case e m alts) o
  | case_tick {n e m alts C j w} :
      j < m → Eval n e (.val (.ctor C j w) 0) → Eval n (.case e m alts) .timeout
  | case_to {n e m alts} :
      Eval n e .timeout → Eval n (.case e m alts) .timeout

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
  | add _ _ ih₁ ih₂ | leq _ _ ih₁ ih₂ | and_ _ _ ih₁ ih₂ =>
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
