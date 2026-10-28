import Flex

/-!
  Reproducer: Pop2 — acyclic κ-vars (k0..k3), but `solve_fixpoint` leaves a
  residual goal of `False`.

  Issue: the dependency graph is acyclic, so zap eliminates each κ and the
  remaining VC should be checkable by SMT/grind. Yet the residual proof
  obligation reduces to `False`, suggesting either:
    1. A κ-sol was assigned too strong, making a downstream clause unsatisfiable.
    2. The constraint really is unsatisfiable (a precondition mismatch in the
       `if n₀>0 then n₀-1 else 0` chains), in which case the original VC was
       a bug in the upstream source.

  Either way, `solve_fixpoint` should either close it or flag it cleanly,
  not leave `False` exposed.
-/

def Pop2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop,
            ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop,
            ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop,
            ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop,
 ∀ (n₀ : Int),
  (n₀ > 2) ->
   (0 ≤ n₀) ->
    (∀ (a'₀ : Int),
     ((k0 a'₀ n₀))) ∧
    ((0 ≤ (if (n₀ > 0) then (n₀ - 1) else 0)) ->
     (∀ (a'₁ : Int),
      ((k0 a'₁ n₀)) ->
       ((k1 a'₁ n₀))) ∧
     (((n₀ > 0) = True)) ∧
     (∀ (v1₀ : Int),
      ((k1 v1₀ n₀)) ->
       (∀ (a'₃ : Int),
        ((k0 a'₃ n₀)) ->
         ((k2 a'₃ n₀ v1₀))) ∧
       ((0 ≤ (if ((if (n₀ > 0) then (n₀ - 1) else 0) > 0) then ((if (n₀ > 0) then (n₀ - 1) else 0) - 1) else 0)) ->
        (∀ (a'₄ : Int),
         ((k2 a'₄ n₀ v1₀)) ->
          ((k3 a'₄ n₀ v1₀))) ∧
        ((((if (n₀ > 0) then (n₀ - 1) else 0) > 0) = True)) ∧
        (∀ (v2₀ : Int),
         ((k3 v2₀ n₀ v1₀)) ->
          ((if ((if (n₀ > 0) then (n₀ - 1) else 0) > 0) then ((if (n₀ > 0) then (n₀ - 1) else 0) - 1) else 0) = (n₀ - 2)))
        )
       )
     )

theorem Pop2_proof : Pop2 := by
  solve_fixpoint
