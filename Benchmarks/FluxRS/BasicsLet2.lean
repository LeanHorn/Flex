import Flex

/-!
  Reproducer / regression for the **scope-fold over-approximation**
  (`BasicsLet2`).  One acyclic κ (`k0`) whose scope binders are a mix of `Int`
  and `Prop`, each pinned by a guard:

    ∀ n₀.  ∀ a'₀:Prop. a'₀ = True →  ∀ a'₁:Int. n₀ < a'₁ →
           ∀ a'₂:Prop. a'₂ = True →  ∀ a'₃:Int. a'₁ < a'₃ →  …k0…

  Every one of `n₀, a'₀, a'₁, a'₂, a'₃` is a *universal* κ-argument, so the
  strongest solution folds them all into κ-params:

    σ̂ = λ z0 z1 z2 z3 z4 z5. z0 = z5 ∧ z2 = True ∧ z4 = True ∧ z3 < z5 ∧ z1 < z3

  Before the fold fix the `dom.isSort` gate refused the `Prop`-typed binders
  `a'₀, a'₂`, which *stopped* the scope descent and cascaded `a'₁, a'₃`
  (foldable `Int`s) into the solution as existentials — yielding the bloated
  `∃a'₀ ∃a'₁ ∃a'₂ ∃a'₃ …`.  `zap` now folds the universal `Prop`
  slots, so the leak is gone.  See `Fusion/StripPres.lean` (2a).
-/

def BasicsLet2 : Prop :=
  ∃ k0 : (a0 : Int) → (a1 : Int) → (a2 : Prop) → (a3 : Int) → (a4 : Prop) → (a5 : Int) → Prop,
    ∀ (n₀ : Int),
      ∀ (a'₀ : Prop), a'₀ = True →
        ∀ (a'₁ : Int), n₀ < a'₁ →
          ∀ (a'₂ : Prop), a'₂ = True →
            ∀ (a'₃ : Int), a'₁ < a'₃ →
              k0 a'₃ n₀ a'₀ a'₁ a'₂ a'₃ ∧
              (∀ (a'₄ : Int), k0 a'₄ n₀ a'₀ a'₁ a'₂ a'₃ → n₀ < a'₄)

theorem BasicsLet2_proof : BasicsLet2 := by
  zap
  all_goals grind
