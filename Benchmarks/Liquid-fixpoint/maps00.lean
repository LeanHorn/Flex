import Flex

/-
  Liquid-fixpoint test — pointwise map update.
  Maps are `Int → Int`; update is mathlib-free (local `upd`, no `Function.update`).
-/

def upd (f : Int → Int) (k v : Int) : Int → Int :=
  fun x => if x = k then v else f x

def maps00Prop : Prop :=
  ∀ m1 : Int → Int, m1 = (fun _ => 0) →
    (∀ v : Int, v = m1 100 → v = 0)
    ∧ (∀ m2 : Int → Int,
        m2 = upd (upd m1 10 1) 20 2 →
          (∀ v : Int, v = m2 10 → v = 1)
          ∧ (∀ v : Int, v = m2 20 → v = 2)
          ∧ (∀ v : Int, v = m2 30 → v = 0))

set_option flex.benchPhases true
theorem maps00Proof : maps00Prop := by
  solve_fixpoint
