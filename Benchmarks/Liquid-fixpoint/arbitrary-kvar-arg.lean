import Flex
/-
  Liquid-fixpoint test — acyclic κ-vars with Bool last arg
  https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/arbitrary-kvar-arg.smt2

  Original SMT: 2 κs ($k0 over int×int×int×int×bool, $k1 over int×int×int×bool)
  Two seed branches split by Bool `a0`, plus a consumer that asserts
  `fld00 a1 = fld00 p0` whenever k0 and k1 hold at a1's fields.

    Branch ¬a0: k0 p00 p01 p00 p01 a0       ∧ k1 p01 p00 p01 a0
    Branch  a0: k0 p00 (p01+1) p00 p01 true ∧ k1 (p01+1) p00 p01 true
    Consumer:   ∀ a1, k0 a10 a11 p00 p01 a0 ∧ k1 a11 p00 p01 a0 ⇒ a10 = p00

  ANF: introduce `p00 = p0.fld00`, `p01 = p0.fld01` (and likewise for a1) so
  the κ-args are all bare scope vars — no compound expressions like
  `Adt0.fld00 p0` that the fusion substitution can't place.
-/

structure Adt0 where
  fld00 : Int
  fld01 : Int

def arbitraryKvarArg : Prop :=
  ∃ k0 : Int → Int → Int → Int → Bool → Prop,
  ∃ k1 : Int → Int → Int → Bool → Prop,
    ∀ p0 : Adt0,
    ∀ p00 : Int, p00 = p0.fld00 →
    ∀ p01 : Int, p01 = p0.fld01 →
    ∀ a0 : Bool,
      -- branch: ¬a0
      (a0 = false →
          k0 p00 p01 p00 p01 a0
        ∧ k1 p01 p00 p01 a0)
      -- branch: a0
    ∧ (a0 = true →
          k0 p00 (p01 + 1) p00 p01 true
        ∧ k1 (p01 + 1) p00 p01 true)
      -- consumer
    ∧ (∀ a1 : Adt0,
       ∀ a10 : Int, a10 = a1.fld00 →
       ∀ a11 : Int, a11 = a1.fld01 →
         k0 a10 a11 p00 p01 a0 ∧ k1 a11 p00 p01 a0 →
           a10 = p00)

set_option flex.benchPhases true
theorem arbitraryKvarArg_proof : arbitraryKvarArg := by
  solve_fixpoint
