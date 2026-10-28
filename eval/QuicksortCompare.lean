import Flex
set_option Elab.async false
set_option maxHeartbeats 6400000
open Lean Elab Command

elab "bench " name:str " in" cmd:command : command => do
  let errsBefore := ((← get).messages.toList.filter (·.severity == .error)).length
  let t0 ← IO.monoMsNow
  let h0 ← IO.getNumHeartbeats
  try elabCommand (← `(command| set_option maxHeartbeats 6400000 in $cmd)) catch _ => pure ()
  let h1 ← IO.getNumHeartbeats
  let t1 ← IO.monoMsNow
  let errsAfter := ((← get).messages.toList.filter (·.severity == .error)).length
  let status := if errsAfter > errsBefore then "FAIL" else "ok"
  logInfo m!"BENCHLINE {name.getString} status={status} hb={(h1-h0)/1000} ms={t1-t0}"

-- ===== defs replayed from Benchmarks/FluxRS/Quicksort.lean =====
open Classical

-- Inlined definitions (standalone, no imports needed)
abbrev Arr (t0 : Type) [Inhabited t0] : Type := Int -> t0

@[ext]
structure VectorsAVec (t0 : Type) [Inhabited t0] where
  mkVectorsAVec₀ ::
    elems : (Arr t0)
    len : Int

@[simp, reducible]
def sort_is_sorted_between (a: Arr Int) (lo hi: Int) : Prop :=
  forall i j, (lo <= i /\ i < j /\ j < hi) -> (a i <= a j)

@[simp]
noncomputable def sort_is_bigger (arr: Arr Int) (lo hi p: Int) : Prop :=
  forall ix, (lo <= ix /\ ix < hi) -> (arr ix <= arr p)

@[simp]
noncomputable def sort_is_smaller (arr: Arr Int) (lo hi p: Int) : Prop :=
  forall ix, (lo <= ix /\ ix < hi) -> (arr p <= arr ix)

@[simp]
noncomputable def sort_is_partitioned_by (arr: Arr Int) (lo mid hi pivot: Int) : Prop :=
  sort_is_bigger arr lo mid pivot /\ sort_is_smaller arr mid hi pivot

@[simp]
noncomputable def is_perm (old new : Arr Int) (lo hi : Int) : Prop :=
  (∀ i, (lo <= i && i <= hi) -> (∃ j, lo <= j /\ j <= hi /\ new i = old j))

@[simp]
noncomputable def is_frame (old new : Arr Int) (lo hi : Int) : Prop :=
  (∀ i, i < lo -> new i = old i) /\ (∀ i, (hi < i) -> new i = old i)

@[simp]
noncomputable def sort_is_perm (old new : Arr Int) (lo hi : Int) : Prop :=
  is_perm old new lo hi /\ is_frame old new lo hi

def SortQuicksortRange := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : Int) -> (a4 : (VectorsAVec Int)) -> (a5 : (Arr Int)) -> (a6 : Int) -> (a7 : (Arr Int)) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : (Arr Int)) -> (a13 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : (VectorsAVec Int)) -> (a3 : (VectorsAVec Int)) -> (a4 : Int) -> (a5 : (VectorsAVec Int)) -> (a6 : (Arr Int)) -> (a7 : Int) -> (a8 : (Arr Int)) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : (Arr Int)) -> (a14 : Int) -> (a15 : (Arr Int)) -> (a16 : Int) -> Prop,
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (lo₀ : Int),
   ∀ (hi₀ : Int),
    (lo₀ < (VectorsAVec.len old₀)) ->
     (hi₀ < (VectorsAVec.len old₀)) ->
      ((VectorsAVec.len old₀) ≥ 0) ->
       (lo₀ ≥ 0) ->
        (hi₀ ≥ 0) ->
         ((¬(lo₀ < hi₀)) ->
          (((VectorsAVec.len old₀) = (VectorsAVec.len old₀))) ∧
          ((sort_is_sorted_between (VectorsAVec.elems old₀) lo₀ (hi₀ + 1))) ∧
          ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems old₀) lo₀ hi₀))
          ) ∧
         ((lo₀ < hi₀) ->
          ∀ (p₀ : Int),
           ∀ (v₀ : (VectorsAVec Int)),
            (((VectorsAVec.len v₀) = (VectorsAVec.len old₀)) ∧ (sort_is_partitioned_by (VectorsAVec.elems v₀) lo₀ p₀ (hi₀ + 1) p₀) ∧ (sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems v₀) lo₀ hi₀) ∧ (lo₀ ≤ p₀) ∧ (p₀ ≤ hi₀)) ->
             ((VectorsAVec.len v₀) ≥ 0) ->
              (p₀ ≥ 0) ->
               ((¬(lo₀ < p₀)) ->
                ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀)))) ∧
               ((lo₀ < p₀) ->
                (((p₀ - 1) ≥ 0)) ∧
                ((lo₀ < (VectorsAVec.len v₀))) ∧
                (((p₀ - 1) < (VectorsAVec.len v₀))) ∧
                (∀ (v₁ : (VectorsAVec Int)),
                 (((VectorsAVec.len v₁) = (VectorsAVec.len v₀)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₁) lo₀ ((p₀ - 1) + 1)) ∧ (sort_is_perm (VectorsAVec.elems v₀) (VectorsAVec.elems v₁) lo₀ (p₀ - 1))) ->
                  ((VectorsAVec.len v₁) ≥ 0) ->
                   ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems v₁) (VectorsAVec.len v₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))))
                ) ∧
               (∀ (a'₃ : (VectorsAVec Int)),
                ((k0 lo₀ p₀ v₀ hi₀ old₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀))) ->
                 ((¬(p₀ < hi₀)) ->
                  ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃)))) ∧
                 ((p₀ < hi₀) ->
                  (((p₀ + 1) < (VectorsAVec.len a'₃))) ∧
                  ((hi₀ < (VectorsAVec.len a'₃))) ∧
                  (∀ (v₂ : (VectorsAVec Int)),
                   (((VectorsAVec.len v₂) = (VectorsAVec.len a'₃)) ∧ (sort_is_sorted_between (VectorsAVec.elems v₂) (p₀ + 1) (hi₀ + 1)) ∧ (sort_is_perm (VectorsAVec.elems a'₃) (VectorsAVec.elems v₂) (p₀ + 1) hi₀)) ->
                    ((VectorsAVec.len v₂) ≥ 0) ->
                     ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems v₂) (VectorsAVec.len v₂) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))))
                  ) ∧
                 (∀ (a'₅ : (VectorsAVec Int)),
                  ((k1 p₀ hi₀ a'₃ v₀ lo₀ old₀ (VectorsAVec.elems a'₅) (VectorsAVec.len a'₅) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) lo₀ hi₀ p₀ (VectorsAVec.elems v₀) (VectorsAVec.len v₀) (VectorsAVec.elems a'₃) (VectorsAVec.len a'₃))) ->
                   (((VectorsAVec.len a'₅) = (VectorsAVec.len old₀))) ∧
                   ((sort_is_sorted_between (VectorsAVec.elems a'₅) lo₀ (hi₀ + 1))) ∧
                   ((sort_is_perm (VectorsAVec.elems old₀) (VectorsAVec.elems a'₅) lo₀ hi₀))
                   )
                 )
               )

-- ===== B first (known-good), then A =====
bench "quicksort_B" in
theorem quicksort_B_bench : SortQuicksortRange := by
  unfold SortQuicksortRange
  zap
  all_goals solve_fixpoint

bench "quicksort_A" in
theorem quicksort_A_bench : SortQuicksortRange := by
  unfold SortQuicksortRange
  solve_fixpoint
