import Flex

-- Adt0 maps to Bool: mkadt0$0 = false, mkadt0$1 = true
-- κ0 : Bool → Prop
--
-- The constraint builds an intermediate bitvector from a1 by:
--   1. Setting bit 0:  a1 | (1 << 0)
--   2. Setting bit 1:  ... | (1 << 1)
--   3. Clearing bit 5: ... & ~(1 << 5)
-- Then checks: bit 0 = 1, bit 1 = 1, bit 5 = 0
--
-- mkadt0$1 ≠ mkadt0$0 (true ≠ false) is always true,
-- so all if-branches take the else path (set, not clear).

-- Helper: extract single bit as Bool
@[simp]
def extractBit (v : BitVec 32) (pos : BitVec 32) : Bool :=
  ((v >>> pos.toNat) &&& 1) != 0

-- The intermediate value computed by the nested lets/ifs
-- (since mkadt0$1 ≠ mkadt0$0, all ifs take else branch)
@[simp]
def computeV (a1 : BitVec 32) : BitVec 32 :=
  let one : BitVec 32 := 1
  let step1 := a1 ||| (one <<< 0)          -- set bit 0
  let step2 := step1 ||| (one <<< 1)       -- set bit 1
  step2 &&& ~~~(one <<< 5)                  -- clear bit 5

def scrape03 : Prop :=
  ∃ κ : Bool → Prop,
    (∀ a0 : Bool, κ a0)
  ∧ (∀ a0 : Bool, κ a0 →
      ∀ a1 : BitVec 32,
        ∀ a2 : BitVec 32,
          ∀ a3 : BitVec 32,
              extractBit (computeV a1) 0 = true
            ∧ extractBit (computeV a1) 1 = true
            ∧ extractBit (computeV a1) 5 = false)

set_option flex.benchPhases true
theorem scrape03_proof : scrape03 := by
  solve_fixpoint
  -- all_goals bv_decide
