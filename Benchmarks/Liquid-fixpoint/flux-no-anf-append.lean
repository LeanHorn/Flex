import Flex
/-
  Liquid-fixpoint test — list append.
  Source: Rust tests/pos/enums/list01.rs:51.

  Sets are modeled mathlib-free as core `List`:
    ∅ ↦ [] , {a} ∪ rest ↦ a :: rest , s ∪ t ↦ s ++ t.

  2 acyclic κs:
    $k0 (List List List)             — "output = xs1 ++ xs2"
    $k1 (List List List Int List)    — "output = tail ++ xs2"

  Scope: ∀ xs1, xs2 : List Int
    • Empty case:  xs1 = [] ⇒ k0 xs2 xs1 xs2
    • Cons case:   xs1 = a0 :: a1 ⇒
                     k1 (a1 ++ xs2) xs1 xs2 a0 a1
                   ∧ (∀ a2, k1 a2 xs1 xs2 a0 a1 ⇒ k0 (a0 :: a2) xs1 xs2)
    • Consumer:    ∀ a3, k0 a3 xs1 xs2 ⇒ a3 = xs1 ++ xs2

  No self-loops → ACYCLIC → `zap`.
-/

def lhListAppendSet : Prop :=
  -- k1 has no κ-dependencies (sink); order it before k0 so existentials
  -- match the solver's topological elimination order.
  ∃ k1 : List Int → List Int → List Int → Int → List Int → Prop,
  ∃ k0 : List Int → List Int → List Int → Prop,
    ∀ xs1 : List Int, ∀ xs2 : List Int,
        (xs1 = [] → k0 xs2 xs1 xs2)
      ∧ (∀ a0 : Int, ∀ a1 : List Int,
            xs1 = a0 :: a1 →
              k1 (a1 ++ xs2) xs1 xs2 a0 a1
            ∧ (∀ a2 : List Int, k1 a2 xs1 xs2 a0 a1 → k0 (a0 :: a2) xs1 xs2))
      ∧ (∀ a3 : List Int, k0 a3 xs1 xs2 → a3 = xs1 ++ xs2)

theorem lhListAppendSetProof : lhListAppendSet := by
  solve_fixpoint
