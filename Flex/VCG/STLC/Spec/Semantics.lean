import Flex.VCG.STLC.Spec.Syntax

open STLC

/-! # Fuel-indexed Big-Step Operational Semantics for STLC (locally nameless)

  Call-by-value big-step semantics over locally-nameless terms, with an explicit
  *fuel* budget so that diverging programs (via `Exp.fix`) have a meaning.

  `Eval n e o` says: running `e` with `n` units of fuel produces outcome `o`,
  which is either `.val v m` (a value `v`, with `m ≤ n` fuel left over) or
  `.timeout` (the budget ran out). Fuel is threaded *cumulatively* through
  sub-evaluations and only consumed by β-steps (function application), which is
  what makes the step-indexed logical relation in `Spec/Denotation.lean` work.

  Stuck states — free variables, `unreach`, applying a non-function, primitive
  operations on ill-typed values — have *no* rule. Type safety (`Spec/Theorems.lean`)
  says a well-typed closed program has a derivation for every amount of fuel,
  i.e. it never gets stuck.
-/

namespace STLC

/-- The runtime comparison: defined on two base values of the same sort (it
    reads only their runtime tags, so it needs no type information), stuck on
    anything else. -/
def Val.leb? : Val → Val → Option Bool
  | .iconst a, .iconst b => some (decide (a ≤ b))
  | .bconst a, .bconst b => some (decide (a ≤ b))
  | _, _ => none

end STLC




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
  /-- Comparison is polymorphic: any two base values of the same sort. -/
  | leq {n e₁ e₂ v₁ n₁ v₂ n₂ c} :
      Eval n e₁ (.val v₁ n₁) → Eval n₁ e₂ (.val v₂ n₂) → Val.leb? v₁ v₂ = some c →
      Eval n (.leq e₁ e₂) (.val (.bconst c) n₂)
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

/-- The operational semantics of a program: run its type erasure. (Types never
    influence evaluation; erasing them first is what makes type abstraction and
    application, and the opening of type binders during checking, invisible at
    runtime.) -/
def Run (n : Nat) (e : Exp) (o : Outcome) : Prop := Eval n e.erase o

end STLC
