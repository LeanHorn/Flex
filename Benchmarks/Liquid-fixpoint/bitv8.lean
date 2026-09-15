import Flex
/-
(constraint
  (and
    (forall ((x Int) ((= x 1)))
      (forall ((y Int) ((= y 2)))
        (forall ((x_ (BitVec Size8)) ((= x_ (int_to_bv8 x))))
          (forall ((y_ (BitVec Size8)) ((= y_ (int_to_bv8 y))))
            (forall ((res_ (BitVec Size8)) ((= res_ (bvadd x_ y_))))
              ((= (bv8_to_int res_) 3)))))))

    (forall ((x Int) ((= x 1)))
      (forall ((y Int) ((= y 2)))
        (forall ((x_ (BitVec Size16)) ((= x_ (int_to_bv16 x))))
          (forall ((y_ (BitVec Size16)) ((= y_ (int_to_bv16 y))))
            (forall ((res_ (BitVec Size16)) ((= res_ (bvadd x_ y_))))
              ((= (bv16_to_int res_) 3)))))))
  )
)
-/

-- No κ-variables — these are pure VCs (ground truth checks on bitvectors)
-- Expr passthrough: BitVec 8 and BitVec 16 are native Lean types

def bitv8_vc : Prop :=
    (∀ x : Int, x = 1 →
      ∀ y : Int, y = 2 →
        ∀ x_ : BitVec 8, x_ = BitVec.ofInt 8 x →
          ∀ y_ : BitVec 8, y_ = BitVec.ofInt 8 y →
            ∀ res_ : BitVec 8, res_ = x_ + y_ →
              res_.toInt = 3)
  ∧ (∀ x : Int, x = 1 →
      ∀ y : Int, y = 2 →
        ∀ x_ : BitVec 16, x_ = BitVec.ofInt 16 x →
          ∀ y_ : BitVec 16, y_ = BitVec.ofInt 16 y →
            ∀ res_ : BitVec 16, res_ = x_ + y_ →
              res_.toInt = 3)

set_option flex.benchPhases true
theorem bitv8_proof : bitv8_vc := by
  solve_fixpoint
