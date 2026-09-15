import Flex
/-
  Liquid-fixpoint test — restrictable-variants dispatch (Rust enum over 6 cases).
  Source: tests/pos/surface/restrictable_variants.rs:34.

  Sets are modeled mathlib-free as core `List`:
    ∅ ∪ {c} ↦ [c] , s ∪ {c} ↦ s ++ [c].

  2 acyclic κs:
    $k0 (List List)              — "output = s"
    $k1 (List List List)         — "first_arg = s"

  Scope: ∀ s : List Adt0
    • 6 constructor-branch seeds (one per variant) populate k0 with values
      that equal `s` (by the branch hypothesis).
    • Consumer: ∀ a9, k0 a9 s ⇒ k1 a9 s a9 ∧ (∀ a10, k1 a10 s a9 ⇒ a10 = s).

  Dep (k0, k1) — k0 in k1's body. Topo-sort: k0 first, k1 last.
-/

@[grind]
inductive Adt0 : Type
  | mk0 | mk1 | mk2 | mk3 | mk4 | mk5

def fluxNoAnfDup : Prop :=
  ∃ k0 : List Adt0 → List Adt0 → Prop,
  ∃ k1 : List Adt0 → List Adt0 → List Adt0 → Prop,
    ∀ s : List Adt0,
        (s = [Adt0.mk0] → k0 [Adt0.mk0] s)
      ∧ (s = [Adt0.mk1] → k0 [Adt0.mk1] s)
      ∧ (∀ a2 : List Adt0,
            s = a2 ++ [Adt0.mk2] →
              k0 (a2 ++ [Adt0.mk2]) s)
      ∧ (∀ a3 a4 : List Adt0,
            s = (a3 ++ a4) ++ [Adt0.mk3] →
              k0 ((a3 ++ a4) ++ [Adt0.mk3]) s)
      ∧ (∀ a5 a6 : List Adt0,
            s = (a5 ++ a6) ++ [Adt0.mk4] →
              k0 ((a5 ++ a6) ++ [Adt0.mk4]) s)
      ∧ (∀ a7 a8 : List Adt0,
            s = (a7 ++ a8) ++ [Adt0.mk5] →
              k0 ((a7 ++ a8) ++ [Adt0.mk5]) s)
      ∧ (∀ a9 : List Adt0, k0 a9 s →
            k1 a9 s a9
          ∧ (∀ a10 : List Adt0, k1 a10 s a9 → a10 = s))

set_option flex.benchPhases true
theorem fluxNoAnfDup_proof : fluxNoAnfDup := by
  solve_fixpoint
