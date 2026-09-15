import Flex
/-
  Liquid-fixpoint test — non-ANF form (field projections inlined)
  https://github.com/ucsd-progsys/liquid-fixpoint/blob/develop/tests/horn/pos/arbitrary-kvar-arg-cyclic.smt2

  Same constraint as the ANF variant but without intermediate `let`-bindings
  for the ADT projections.
-/

@[grind]
structure Adt0 where
  fld00 : Int
  fld01 : Int

@[qualif] def q_eq (a b : Int) : Prop := a = b

def arbitraryKvarArgCyclic : Prop :=
  ∃ k0 : Int → Int → Int → Int → Int → Prop,
  ∃ k1 : Int → Int → Int → Int → Prop,
  ∃ k2 : Int → Int → Int → Prop,
    ∀ p0 : Adt0,
      -- seed
      (k0 0 p0.fld00 p0.fld01 p0.fld00 p0.fld01)
    ∧ (k1 p0.fld00 p0.fld01 p0.fld00 p0.fld01)
    ∧ (k2 p0.fld01 p0.fld00 p0.fld01)
      -- body
    ∧ (∀ a0 : Int,
       ∀ a1 : Adt0,
         k0 a0 a1.fld00 a1.fld01 p0.fld00 p0.fld01
         ∧ k1 a1.fld00 a1.fld01 p0.fld00 p0.fld01
         ∧ k2 a1.fld01 p0.fld00 p0.fld01 →
           -- exit
           ((¬(a0 < 10)) → a1.fld00 = p0.fld00)
         ∧ -- loop
           ((a0 < 10) →
              (k0 (a0 + 1) a1.fld00 (a1.fld01 + 1) p0.fld00 p0.fld01)
            ∧ (k1 a1.fld00 (a1.fld01 + 1) p0.fld00 p0.fld01)
            ∧ (k2 (a1.fld01 + 1) p0.fld00 p0.fld01)))

set_option flex.benchPhases true
theorem arbitraryKvarArgCyclic_proof : arbitraryKvarArgCyclic := by
  solve_fixpoint
