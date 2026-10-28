import Flex

@[qualif] def MinIdx.q_lt      (a b : Int) : Prop := a < b
@[qualif] def MinIdx.q_le      (a b : Int) : Prop := a ≤ b
@[qualif] def MinIdx.q_ge_zero (a : Int)   : Prop := a ≥ 0
@[qualif] def MinIdx.q_eq_zero (a : Int)   : Prop := a = 0

def SimpleLoop := ∃ k0 : Int -> Prop, ∃ k1 : Int -> Prop,
  (k0 0) ∧
  (∀ (i : Int),
    (k0 i) ->
      ((k1 i) ∧
       ((k1 (i + 1)) -> (k0 (i + 1)))))

def SimpleLoop1 :=
  ∃ k0 : Int -> Prop,
  ∃ k1 : Int -> Prop,
  (k0 0) ∧
  (∀ (i : Int),
    (k0 i) ->
      (((i > 0) -> (k1 i)) ∧
        ((i < 0) -> (k1 (i + 1)) -> (k0 (i + 1)))))


theorem SimpleLoopProof : SimpleLoop1 := by
  unfold SimpleLoop1
  zap
  fixpoint

theorem SimpleLoopProof' : SimpleLoop := by
  unfold SimpleLoop
  zap
  solve_fixpoint
  -- zap
  -- fixpoint
