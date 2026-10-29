import Flex

/-!
  Reproducer: VC with κ-vars taking `Prop`-typed arguments alongside `Int`s.

  Shape:
    k0 : Int → Int → Prop
    k1 : Int → Int → Prop → Prop      ← Prop-typed arg (a'₁ : Prop)
    k2 : Int → Int → Int → Prop → Prop ← Prop-typed arg (a'₁ : Prop)

  The Prop slot can't be filled by any of the standard Int-typed qualifiers,
  so qualifier instantiation correctly skips it. PA proceeds on the Int slots
  and zap eliminates `k1` (acyclic). Originated from a pre-mvar-migration
  issue with κ-args of mixed sorts.
-/

@[qualif] def KPA.q_le (a b : Int) : Prop := a ≤ b
@[qualif] def KPA.q_lt (a b : Int) : Prop := a < b
@[qualif] def KPA.q_eq (a b : Int) : Prop := a = b
@[qualif] def KPA.q_ge_zero (a : Int) : Prop := a ≥ 0
@[qualif] def KPA.q_eq_zero (a : Int) : Prop := a = 0

def KappaPropArg : Prop :=
  ∃ k0 : (a0 : Int) → (a1 : Int) → Prop,
  ∃ k1 : (a0 : Int) → (a1 : Int) → (a2 : Prop) → Prop,
  ∃ k2 : (a0 : Int) → (a1 : Int) → (a2 : Int) → (a3 : Prop) → Prop,
    ∀ (k₀ : Int),
      0 ≤ k₀ →
        k0 k₀ k₀ ∧
        (∀ (k₁ : Int),
          k0 k₁ k₀ →
            ∀ (a'₁ : Prop),
              (¬a'₁ → k1 k₀ k₁ a'₁) ∧
              (a'₁ →
                (¬(k₁ < (2147483647 - 1)) → k1 k₀ k₁ True) ∧
                (k₁ < (2147483647 - 1) → k0 (k₁ + 1) k₀)) ∧
              (k1 k₀ k₁ a'₁ →
                k2 k₁ k₀ k₁ a'₁ ∧
                (∀ (k₂ : Int),
                  k2 k₂ k₀ k₁ a'₁ →
                    (¬(k₂ > 0) → k₂ = 0) ∧
                    (k₂ > 0 → k2 (k₂ - 1) k₀ k₁ a'₁))))

theorem KappaPropArg_proof : KappaPropArg := by
  solve_fixpoint

theorem KappaPropArg_proof' : KappaPropArg := by
  zap
  fixpoint
  all_goals grind
  