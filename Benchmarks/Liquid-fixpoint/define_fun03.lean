import Flex
/-
  Liquid-fixpoint test — ground constraint over an Int→Int map:
    define_fun foo m := (m 0 = 99)
    ∀ moo, foo moo →
        (moo 10 = moo (1 + 9))      -- follows from `10 = 1 + 9`
      ∧ foo moo                     -- trivially by hypothesis
-/

def foo (m : Int → Int) : Prop := m 0 = 99

def lhMapProp : Prop :=
  ∀ moo : Int → Int, foo moo →
      moo 10 = moo (1 + 9)
    ∧ foo moo

set_option flex.benchPhases true
theorem lhMapProof : lhMapProp := by
  solve_fixpoint
