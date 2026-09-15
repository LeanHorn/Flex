import Flex

def bitvec_ii_vc : Prop :=
    -- rotate_right 8 (#b1000) by 7 = #b0001
    (∀ x_ : BitVec 4, x_ = 0b1000#4 →
      ∀ y_ : BitVec 4, y_ = x_.rotateRight 7 →
        ∀ z_ : BitVec 4, z_ = 0b0001#4 →
          y_ = z_)
  ∧ -- sign_extend preserves equality
    (∀ x : BitVec 32,
      ∀ y : BitVec 32, x = y →
        x.signExtend 64 = y.signExtend 64)

set_option flex.benchPhases true
theorem bitvec_ii_proof : bitvec_ii_vc := by
  solve_fixpoint
