import Lean

/-! SortInsert and its dependencies, copied from flex-benchmarks/flux_to_lean_demo. -/


namespace LeanProofs.Lib.Lemmas

abbrev Arr (t0 : Type) [Inhabited t0] : Type := Int -> t0

@[simp, grind =]
def arr_get {t0 : Type} [Inhabited t0] (arr: Arr t0) (idx: Int) : t0 :=
  arr idx

@[simp]
def arr_set {t0 : Type} [Inhabited t0] (arr: Arr t0) (idx: Int) (v: t0): Arr t0 :=
  fun i => if i = idx then v else arr i

@[grind =]
theorem set_get_neq {t0 : Type} [Inhabited t0] : ∀ (a: Arr t0) (i: Int) (v: t0) (j: Int),
   i != j -> (arr_get (arr_set a i v) j) = arr_get a j
   := by grind [arr_set]

@[grind =]
theorem set_get_eq {t0 : Type} [Inhabited t0] : ∀ (a : Arr t0) (i : Int) (v : t0),
   (arr_get (arr_set a i v) i) = v := by grind [arr_set]

@[grind =]
theorem set_get_neq' {t0 : Type} [Inhabited t0] : ∀ (a: Arr t0) (i: Int) (v: t0) (j: Int),
   i != j -> (arr_set a i v) j = a j
   := by grind [arr_set]

@[grind =]
theorem set_get_eq' {t0 : Type} [Inhabited t0] : ∀ (a : Arr t0) (i : Int) (v : t0),
   (arr_set a i v) i = v := by grind [arr_set]

end LeanProofs.Lib.Lemmas

open Classical

set_option linter.unusedVariables false

namespace F

abbrev Arr := LeanProofs.Lib.Lemmas.Arr

@[ext]
structure VectorsAVec (t0 : Type) [Inhabited t0] where
  mkVectorsAVec₀ ::
    elems : (Arr t0) 
    len : Int 
  deriving Inhabited
attribute [grind .] VectorsAVec.ext

@[simp]
def sort_is_sorted_between (a: Arr Int) (lo hi: Int) : Prop :=
  forall i j, (lo <= i /\ i < j /\ j < hi) -> (a i <= a j)

@[simp]
def sort_is_sorted_between_exc (a: Arr Int) (lo hi mid: Int) : Prop :=
  forall i j, (lo <= i /\ i < j /\ j < hi /\ j != mid) -> (a i <= a j)

@[simp]
def vectors_arr_get {t0 : Type} [Inhabited t0] (arr: Arr t0) (idx: Int) : t0 :=
  LeanProofs.Lib.Lemmas.arr_get arr idx

@[simp]
def vectors_arr_set {t0 : Type} [Inhabited t0] (arr: Arr t0) (idx: Int) (v: t0) : Arr t0 :=
  LeanProofs.Lib.Lemmas.arr_set arr idx v

-- The generated VC is unchanged.

def SortInsert := ∃ k0 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : (Arr Int)) -> (a4 : Int) -> (a5 : Int) -> Prop, ∃ k1 : (a0 : (Arr Int)) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : (Arr Int)) -> (a5 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : (Arr Int)) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : (Arr Int)) -> (a6 : Int) -> Prop, 
 ∀ (old₀ : (VectorsAVec Int)),
  ∀ (n₀ : Int),
   (sort_is_sorted_between_exc (VectorsAVec.elems old₀) 0 (n₀ + 1) n₀) ->
    ((1 ≤ n₀) ∧ (n₀ < (VectorsAVec.len old₀))) ->
     ((VectorsAVec.len old₀) ≥ 0) ->
      (n₀ ≥ 0) ->
       (((k0 n₀ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀))) ∧
       (∀ (k₀ : Int),
        ∀ (a'₁ : (VectorsAVec Int)),
         ((k0 k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)) ->
          ((¬(0 < k₀)) ->
           ((k1 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
          ((0 < k₀) ->
           ((k₀ < (VectorsAVec.len a'₁))) ∧
           (∀ (a'₂ : Int),
            ((k2 a'₂ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
           (((k2 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
            (((k₀ - 1) ≥ 0)) ∧
            (((k₀ - 1) < (VectorsAVec.len a'₁))) ∧
            (∀ (a'₃ : Int),
             ((k3 a'₃ (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
            (((k3 (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
             ((¬((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)))) ->
              ((k1 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁)))) ∧
             (((vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀) < (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1))) ->
              (((k₀ - 1) ≥ 0)) ∧
              (((k₀ - 1) < (VectorsAVec.len a'₁))) ∧
              ((k₀ < (VectorsAVec.len a'₁))) ∧
              (((VectorsAVec.len a'₁) ≥ 0) ->
               (((k₀ - 1) ≥ 0)) ∧
               (((k0 (k₀ - 1) (let a'₄ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1)); (let a'₅ := (vectors_arr_get (t0 := Int) (VectorsAVec.elems a'₁) k₀); (vectors_arr_set (t0 := Int) (vectors_arr_set (t0 := Int) (VectorsAVec.elems a'₁) (k₀ - 1) a'₅) k₀ a'₄))) (VectorsAVec.len a'₁) (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀)))
               )
              )
             )
            )
           ) ∧
          (((k1 (VectorsAVec.elems old₀) (VectorsAVec.len old₀) n₀ k₀ (VectorsAVec.elems a'₁) (VectorsAVec.len a'₁))) ->
           (((VectorsAVec.len a'₁) = (VectorsAVec.len old₀))) ∧
           ((sort_is_sorted_between (VectorsAVec.elems a'₁) 0 (n₀ + 1)))
           )
          )

end F
