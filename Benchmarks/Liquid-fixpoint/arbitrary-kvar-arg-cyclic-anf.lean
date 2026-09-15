import Flex
/-
  Liquid-fixpoint test — ANF form
  https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/arbitrary-kvar-arg-cyclic-anf.smt2

  Original SMT (cyclic):
    (datatype (Adt0 0) ((mkadt0$0 ((fld00 int) (fld01 int)))))
    (var $k0 (int int int int int))
    (var $k1 (int int int int))
    (var $k2 (int int int))

    Seed: $k0 0 p00 p01 p00 p01 ∧ $k1 p00 p01 p00 p01 ∧ $k2 p01 p00 p01
    Loop: $k0 a0 a10 a11 p00 p01 ∧ $k1 a10 a11 p00 p01 ∧ $k2 a11 p00 p01 ⇒
          (¬(a0 < 10) ⇒ a10 = p00)                       -- exit assertion
        ∧ (a0 < 10    ⇒ $k0 (a0+1) a10 (a11+1) p00 p01
                       ∧ $k1 a10 (a11+1) p00 p01
                       ∧ $k2 (a11+1) p00 p01)

  Key invariant: (2nd arg) = (4th arg) for k0, (1st) = (3rd) for k1, so
  when the exit condition fires we can conclude a10 = p00.
-/

@[qualif] def q1  (a b : Int) : Prop := a = b
@[qualif] def q2  (a b : Int) : Prop := a ≥ b
@[qualif] def q3  (a b : Int) : Prop := a > b
@[qualif] def q4  (a b : Int) : Prop := a ≤ b
@[qualif] def q5  (a b : Int) : Prop := a != b

structure Adt0 where
  fld00 : Int
  fld01 : Int

def arbitraryKvarArgCyclicAnf : Prop :=
  ∃ k0 : Int → Int → Int → Int → Int → Prop,
  ∃ k1 : Int → Int → Int → Int → Prop,
  ∃ k2 : Int → Int → Int → Prop,
    ∀ p0 : Adt0,
    ∀ p00 : Int, p00 = p0.fld00 →
    ∀ p01 : Int, p01 = p0.fld01 →
      -- seed
      (k0 0 p00 p01 p00 p01)
    ∧ (k1 p00 p01 p00 p01)
    ∧ (k2 p01 p00 p01)
      -- body
    ∧ (∀ a0 : Int,
       ∀ a1 : Adt0,
       ∀ a10 : Int, a10 = a1.fld00 →
       ∀ a11 : Int, a11 = a1.fld01 →
         k0 a0 a10 a11 p00 p01 ∧ k1 a10 a11 p00 p01 ∧ k2 a11 p00 p01 →
           -- exit: a10 = p00
           ((¬(a0 < 10)) → a10 = p00)
         ∧ -- loop
           ((a0 < 10) →
              ∀ a0_plus : Int, a0_plus = a0 + 1 →
              ∀ a11_plus : Int, a11_plus = a11 + 1 →
                (k0 a0_plus a10 a11_plus p00 p01)
              ∧ (k1 a10 a11_plus p00 p01)
              ∧ (k2 a11_plus p00 p01)))

set_option flex.benchPhases true
theorem arbitraryKvarArgCyclicAnf_proof : arbitraryKvarArgCyclicAnf := by
  solve_fixpoint
