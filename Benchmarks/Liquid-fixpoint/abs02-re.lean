import Flex
/-
  Liquid Haskell test
  `https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/abs02-re.smt2`

  Ground constraint (no κ-vars):
    ∀x. true ⇒ ∀VV. VV=10 ⇒ VV≥0
  ∧ ∀z. true ⇒ ∀r. r≥0 ⇒ ∀v. v=r ∧ v≥0 ⇒ v≥0
  ∧ ∀z. true ⇒ ∀t1. t1≥0 ⇒ ∀v. v≥0 ⇒ v≥0
-/

def lhGroundProp : Prop :=
  (∀ _x : Int, True →
    ∀ VV : Int, VV = 10 →
      0 ≤ VV)
  ∧ (∀ _z : Int, True →
      (∀ r : Int, 0 ≤ r →
        ∀ v : Int, v = r ∧ 0 ≤ v →
          0 ≤ v)
      ∧ (∀ t1 : Int, 0 ≤ t1 →
          ∀ v : Int, 0 ≤ v →
            0 ≤ v))

set_option flex.benchPhases true
theorem lhGroundProof : lhGroundProp := by
  solve_fixpoint
