import Flex

/-
  Liquid-fixpoint test — ground set property:
    ∀ xs : List ℤ,
      (xs = [] → xs = [])                 -- trivial
    ∧ (∀ a0 a1, xs = a0 :: a1 → xs ≠ [])  -- nonempty if it has an element

  Sets are modeled mathlib-free as core `List`: ∅ ↦ [] , {a0} ∪ a1 ↦ a0 :: a1.
-/

def lhSetProp : Prop :=
  ∀ xs : List Int, True →
    (∀ _x : Int, xs = [] → xs = [])
    ∧ (∀ a0 : Int, True → ∀ a1 : List Int, True →
        ∀ _x : Int, xs = a0 :: a1 → xs ≠ [])

set_option flex.benchPhases true
theorem lhSetProof : lhSetProp := by
<<<<<<< HEAD
  unfold lhSetProp
=======
>>>>>>> main
  solve_fixpoint
