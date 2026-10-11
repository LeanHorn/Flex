import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Semantics

namespace STLC

/-- Interpret a term under the single environment `γ`. `fvar` resolves through
    the name map (`REnv.get`); `bvar` resolves through the de Bruijn stack
    (`REnv.getBV`) — the values of ν and the enclosing quantifier/arrow binders
    live there.. -/
def Term.interp (γ : REnv) : {b : Base} → Term b → b.interp
  | _, .const _ c   => c
  | _, .bvar b k    => REnv.getBV b γ k
  | _, .fvar b x    => REnv.get b γ x
  | _, .add t₁ t₂   => Term.interp γ t₁ + Term.interp γ t₂
  | _, .not t       => !Term.interp γ t
  | _, .and t₁ t₂   => Term.interp γ t₁ && Term.interp γ t₂

/-- Interpret a (now κ-free) formula under `γ`. Each quantifier binds `BVar 0`,
    so it `push`es its witness value as the new innermost de Bruijn slot of `γ`
    and recurses. -/
def Formula.interp (γ : REnv) : Formula → Prop
  | .tt           => True
  | .ff           => False
  | .eq _ t₁ t₂   => Term.interp γ t₁ = Term.interp γ t₂
  | .leqI t₁ t₂   => Term.interp γ t₁ ≤ Term.interp γ t₂
  | .and φ₁ φ₂    => Formula.interp γ φ₁ ∧ Formula.interp γ φ₂
  | .or φ₁ φ₂     => Formula.interp γ φ₁ ∨ Formula.interp γ φ₂
  | .not φ        => ¬ Formula.interp γ φ
  | .imp φ₁ φ₂    => Formula.interp γ φ₁ → Formula.interp γ φ₂
  | .ex b φ       => ∃ x : b.interp,  Formula.interp (γ.push (Val.inj b x)) φ
  | .all b φ      => ∀ x : b.interp,  Formula.interp (γ.push (Val.inj b x)) φ

/-- Interpret a refinement under `γ`. This is the *only* interpretation
    that consults the κ-assignment. -/
def Refinement.interp (κ : KEnv) (r : Refinement) (γ : REnv) : Prop :=
  match r with
  | .fmla φ       => Formula.interp γ φ
  | .kapp kn args =>
      κ kn (args.map (fun a => ⟨a.1, Term.interp γ a.2⟩))

/-- Interpret a syntactic constraint as a `κ`-indexed `REnv` predicate. -/
def Cstr.interp : Cstr → KEnv → REnv → Prop
  | .head r,     κ, γ => Refinement.interp κ r γ
  | .imp r c,    κ, γ => Refinement.interp κ r γ → c.interp κ γ
  | .all x b c,  κ, γ => ∀ v : b.interp, c.interp κ (REnv.update b γ x v)
  | .conj c₁ c₂, κ, γ => c₁.interp κ γ ∧ c₂.interp κ γ

/-! ## Step-indexed logical relation

  `TyDenote κ k t γ v` — `v` is a value of type `t` (under the closing environment
  `γ`), *good for `k` more units of fuel*. Base types ignore the index. A
  function is good at index `k` if, for every `j < k` and argument good at `j`,
  running the body with fuel `j` never gets stuck and any value it returns
  (with `m` fuel left) is good at `m`. Since a β-step costs one unit of fuel,
  `j < k` is exactly what lets the `fix` case go through by induction on `k`. -/
def TyDenote : KEnv → Nat → Ty → REnv → Val → Prop
  | κ, _, .refine b r, γ, v => ∃ ν : b.interp, v = Val.inj b ν ∧
                                 Refinement.interp κ r (γ.push (Val.inj b ν))
  | κ, k, .arrow s t,  γ, v =>
      (∃ body, v = .clos body ∨ v = .fclos body) ∧
        Val.lc v ∧ Val.closed v ∧
        ∀ j < k, ∀ va, TyDenote κ j s γ va →
          ∃ body o, Val.apply v va = some body ∧ Eval j body o ∧
            ∀ vr m, o = .val vr m → TyDenote κ m t (γ.push va) vr
termination_by _ _ t _ _ => t.skel
decreasing_by
  all_goals simp_wf
  · omega
  · omega

/-- Expression relation: with exactly `k` fuel, `e` does not get stuck, and any
    value it returns with `m` fuel left is good at index `m`. -/
def ExpDenote (κ : KEnv) (k : Nat) (t : Ty) (γ : REnv) (e : Exp) : Prop :=
  ∃ o, Eval k e o ∧ ∀ v m, o = .val v m → TyDenote κ m t γ v

/-- Downward closure: a value good for `k` steps is good for fewer. -/
theorem TyDenote.mono {κ : KEnv} {j k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (hjk : j ≤ k) (h : TyDenote κ k t γ v) : TyDenote κ j t γ v := by
  cases t with
  | refine b r => simpa only [TyDenote] using h
  | arrow s t =>
    simp only [TyDenote] at h ⊢
    obtain ⟨hf, hlc, hcl, hLR⟩ := h
    exact ⟨hf, hlc, hcl, fun i hi => hLR i (by omega)⟩

end STLC
