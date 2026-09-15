import Flex

-- (datatype (Adt0 0) ((mkadt0$0 ()) (mkadt0$1 ())))
@[grind]
inductive Adt0 : Type where
  | mkadt0_0
  | mkadt0_1
  deriving Nonempty


-- (datatype (Adt1 0) ((mkadt1$0 ((fld1$0 int) (fld1$1 int)))))
@[grind]
structure Adt1 : Type where
  mk ::
  fld1_0 : Int
  fld1_1 : Int

-- (constant f$get_mode$0 (func 0 ((BitVec Size32) int) (Adt0)))
-- (constant f$get_mode$0 (func 0 ((BitVec Size32) int) (Adt0)))
@[simp]
def f_get_mode (_m : BitVec 32) (_a : Int) : Adt0 := Adt0.mkadt0_0

@[qualif] def q_zero (a : Int) : Prop := a = 0
@[qualif] def q_eq_mode (a : Int) (m : BitVec 32) : Prop :=
  f_get_mode m a = Adt0.mkadt0_0

def scrape02 : Prop :=
  ∃ k0 : Int → BitVec 32 → Int → Prop,
  ∃ k1 : Int → Int → Int → BitVec 32 → Int → Prop,
  ∃ k2 : Int → Int → BitVec 32 → Int → Prop,
  ∃ k3 : Int → BitVec 32 → Int → Prop,
  ∃ k4 : Int → Int → Int → Int → BitVec 32 → Int → Prop,
  ∃ k5 : Int → BitVec 32 → Int → Int → Int → Int → Prop,
    ∀ reftgen : BitVec 32, ∀ a0 : Int,
      -- Seed:  f_get_mode reftgen a1 = mkadt0_0  →  k0 a1 reftgen a0
      (∀ a1 : Int,
          f_get_mode reftgen a1 = Adt0.mkadt0_0 → k0 a1 reftgen a0)
    ∧ -- k0 → k4
      (∀ a4 : Int, k0 a4 reftgen a0 →
          ∀ a5 a6 : Int, k4 a4 a5 a6 a0 reftgen a0)
    ∧ -- Main consumer
      (∀ a7 : Int, ∀ _a8 : Adt1, ∀ a9 a10 : Int,
          (k1 a7 a9 a10 reftgen a0 ∧ k2 a9 a10 reftgen a0 ∧ k3 a10 reftgen a0) →
            -- Sub-A: k4 → k5
            (∀ a11 a12 a13 : Int, k4 a11 a7 a12 a13 reftgen a0 →
                ∀ a14 a15 : Int, k5 a11 reftgen a0 a7 a14 a15)
          ∧
            -- Sub-B: k5 → (check ∧ bool branching)
            (∀ _a16 : Adt1, ∀ a17 a18 a19 : Int,
                k5 a17 reftgen a0 a7 a18 a19 →
                  -- Check (the (tag …) clause)
                  f_get_mode reftgen a17 = Adt0.mkadt0_0
                ∧
                  (∀ _a20 : Bool,
                      -- Re-seed k1, k2, k3
                      (∀ a21 a22 a23 : Int,
                          k1 a21 a22 a23 reftgen a0
                        ∧ k2 a22 a23 reftgen a0
                        ∧ k3 a23 reftgen a0)
                    ∧
                      -- k5 → k4
                      (∀ a24 a25 a26 : Int, k5 a24 reftgen a0 a7 a25 a26 →
                          ∀ a27 a28 a29 : Int, k4 a24 a27 a28 a29 reftgen a0))))

-- set_option maxHeartbeats 6400000 in
set_option flex.benchPhases true
theorem scrape02_proof : scrape02 := by
  solve_fixpoint
