import Flex
/-
(constraint
  (and
    (forall ((one_ (BitVec Size32)) ((= one_ (int_to_bv32 1))))
      (forall ((zero_ (BitVec Size32)) ((= zero_ (int_to_bv32 0))))
        (forall ((size Int) ((<= 1 size)))
          (forall ((index Int) ((<= 0 index)))
            (forall ((size_ (BitVec Size32)) (and
                                              ((= size_ (int_to_bv32 size)))
                                              ((= zero_ ((bvand size_) ((bvsub size_) one_))))))
              (forall ((index_ (BitVec Size32)) ((= index_ (int_to_bv32 index))))
                (forall ((mask_ (BitVec Size32)) ((= mask_ ((bvsub size_) one_))))
                  (forall ((res_ (BitVec Size32)) ((= res_ ((bvand index_) mask_))))
                    (forall ((res Int) ((= res (bv32_to_int res_))))
                      ((< res size)))))))))))))
-/

-- No κ-variables — pure VC about bit masking
-- This is a complex bitvector constraint: index & (size - 1) < size
-- when size is a power of 2 (size & (size - 1) == 0)
-- Expr passthrough: BitVec 32 is a native Lean type

-- NOTE: This VC is hard — it requires reasoning about bitvector
-- masking properties. The old system couldn't even EXPRESS this.
-- With Expr passthrough, at least we can state it.

def bitv_vc : Prop :=
  ∀ one_ : BitVec 32, one_ = BitVec.ofInt 32 1 →
  ∀ zero_ : BitVec 32, zero_ = BitVec.ofInt 32 0 →
  ∀ size : Int, 1 ≤ size →
  ∀ index : Int, 0 ≤ index →
  ∀ size_ : BitVec 32, size_ = BitVec.ofInt 32 size ∧ zero_ = size_ &&& (size_ - one_) →
  ∀ index_ : BitVec 32, index_ = BitVec.ofInt 32 index →
  ∀ mask_ : BitVec 32, mask_ = size_ - one_ →
  ∀ res_ : BitVec 32, res_ = index_ &&& mask_ →
  ∀ res : Int, res = res_.toInt →
    res < size

set_option flex.benchPhases true
theorem bitv_proof : bitv_vc := by
  solve_fixpoint
