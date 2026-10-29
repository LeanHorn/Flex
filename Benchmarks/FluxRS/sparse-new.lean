import Flex
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure OpsRangeRange (t0 : Type) [Inhabited t0] where
  mkOpsRangeRange₀ ::
    start : t0
    end_ : t0
  deriving Inhabited
attribute [grind .] OpsRangeRange.ext



def SparseImpl__0__New := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> Prop, ∃ k5 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> Prop, ∃ k6 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> Prop, ∃ k7 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> Prop, ∃ k8 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> Prop, ∃ k9 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Prop) -> Prop, ∃ k10 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Prop) -> Prop, ∃ k11 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Int) -> (a22 : Int) -> (a23 : Int) -> (a24 : Prop) -> Prop, ∃ k12 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> (a4 : Int) -> (a5 : Int) -> (a6 : Int) -> (a7 : Int) -> (a8 : Int) -> (a9 : Int) -> (a10 : Int) -> (a11 : Int) -> (a12 : Int) -> (a13 : Int) -> (a14 : Int) -> (a15 : Int) -> (a16 : Int) -> (a17 : Int) -> (a18 : Int) -> (a19 : Int) -> (a20 : Int) -> (a21 : Prop) -> Prop,
 ∀ (rows₀ : Int),
  ∀ (cols₀ : Int),
   (rows₀ ≥ 0) ->
    (cols₀ ≥ 0) ->
     (0 ≤ rows₀) ->
      (((k0 0 0 0 0 0 rows₀ rows₀ cols₀))) ∧
      (∀ (nnz₀ : Int),
       ∀ (col_index₀ : Int),
        ∀ (row_index₀ : Int),
         ∀ (values₀ : Int),
          ∀ (iter₀ : (OpsRangeRange Int)),
           ((k0 nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) rows₀ cols₀)) ->
            ∀ (r₀ : (OpsRangeRange Int)),
             ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) -> ((OpsRangeRange.start r₀) = ((OpsRangeRange.start iter₀) + 1))) ∧ ((OpsRangeRange.end_ r₀) = (OpsRangeRange.end_ iter₀))) ->
              ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = False) ->
               (∀ (a'₆ : Int),
                ((k1 a'₆ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) rows₀ cols₀)) ->
                 ((k2 a'₆ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀)))) ∧
               (((k2 nnz₀ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀)))) ∧
               ((0 ≤ (row_index₀ + 1)) ->
                (∀ (a'₇ : Int),
                 ((k3 a'₇ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) rows₀ cols₀)) ->
                  (a'₇ < cols₀)) ∧
                ((col_index₀ = values₀)) ∧
                (∀ (a'₈ : Int),
                 ((k2 a'₈ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀))) ->
                  (a'₈ ≤ values₀)) ∧
                (((row_index₀ + 1) = (rows₀ + 1)))
                )
               ) ∧
              ((((OpsRangeRange.start iter₀) < (OpsRangeRange.end_ iter₀)) = True) ->
               ∀ (a'₉ : Int),
                (a'₉ = (OpsRangeRange.start iter₀)) ->
                 (a'₉ ≥ 0) ->
                  (∀ (a'₁₀ : Int),
                   ((k1 a'₁₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) rows₀ cols₀)) ->
                    ((k4 a'₁₀ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉))) ∧
                  (((k4 nnz₀ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉))) ∧
                  ((0 ≤ (row_index₀ + 1)) ->
                   (((k5 nnz₀ col_index₀ values₀ 0 cols₀ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉))) ∧
                   (∀ (a'₁₁ : Int),
                    ((k3 a'₁₁ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) rows₀ cols₀)) ->
                     ((k6 a'₁₁ nnz₀ col_index₀ values₀ 0 cols₀ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉))) ∧
                   (∀ (a'₁₂ : Int),
                    ((k4 a'₁₂ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)) ->
                     ((k7 a'₁₂ nnz₀ col_index₀ values₀ 0 cols₀ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉))) ∧
                   (∀ (nnz₁ : Int),
                    ∀ (col_index₁ : Int),
                     ∀ (values₁ : Int),
                      ∀ (iter₁ : (OpsRangeRange Int)),
                       ((k5 nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)) ->
                        ∀ (r₁ : (OpsRangeRange Int)),
                         ((((OpsRangeRange.start iter₁) < (OpsRangeRange.end_ iter₁)) -> ((OpsRangeRange.start r₁) = ((OpsRangeRange.start iter₁) + 1))) ∧ ((OpsRangeRange.end_ r₁) = (OpsRangeRange.end_ iter₁))) ->
                          ((((OpsRangeRange.start iter₁) < (OpsRangeRange.end_ iter₁)) = False) ->
                           (((k0 nnz₁ col_index₁ (row_index₀ + 1) values₁ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) rows₀ cols₀))) ∧
                           (∀ (a'₁₈ : Int),
                            ((k6 a'₁₈ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)) ->
                             ((k3 a'₁₈ nnz₁ col_index₁ (row_index₀ + 1) values₁ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) rows₀ cols₀))) ∧
                           (∀ (a'₁₉ : Int),
                            ((k7 a'₁₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)) ->
                             ((k1 a'₁₉ nnz₁ col_index₁ (row_index₀ + 1) values₁ (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) rows₀ cols₀)))
                           ) ∧
                          ((((OpsRangeRange.start iter₁) < (OpsRangeRange.end_ iter₁)) = True) ->
                           ∀ (a'₂₀ : Int),
                            (a'₂₀ = (OpsRangeRange.start iter₁)) ->
                             (a'₂₀ ≥ 0) ->
                              ((a'₉ < rows₀)) ∧
                              (∀ (a'₂₁ : Int),
                               (a'₂₁ = cols₀) ->
                                ((k8 a'₂₁ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀))) ∧
                              (∀ (a'₂₂ : Int),
                               ((k8 a'₂₂ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀)) ->
                                (0 ≤ a'₂₂) ->
                                 ((a'₂₀ < a'₂₂)) ∧
                                 (∀ (a'₂₃ : Prop),
                                  ((¬a'₂₃) ->
                                   (((k9 nnz₁ col_index₁ values₁ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ a'₂₃))) ∧
                                   (∀ (a'₂₄ : Int),
                                    ((k6 a'₂₄ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)) ->
                                     ((k10 a'₂₄ nnz₁ col_index₁ values₁ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ a'₂₃))) ∧
                                   (∀ (a'₂₅ : Int),
                                    ((k7 a'₂₅ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)) ->
                                     ((k11 a'₂₅ nnz₁ col_index₁ values₁ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ a'₂₃)))
                                   ) ∧
                                  (a'₂₃ ->
                                   (∀ (a'₂₆ : Int),
                                    ((k6 a'₂₆ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)) ->
                                     ((k12 a'₂₆ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ True))) ∧
                                   (((k12 a'₂₀ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ True))) ∧
                                   ((0 ≤ (col_index₁ + 1)) ->
                                    (0 ≤ (values₁ + 1)) ->
                                     (((k9 (nnz₁ + 1) (col_index₁ + 1) (values₁ + 1) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ True))) ∧
                                     (∀ (a'₂₇ : Int),
                                      ((k12 a'₂₇ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ True)) ->
                                       ((k10 a'₂₇ (nnz₁ + 1) (col_index₁ + 1) (values₁ + 1) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ True))) ∧
                                     (∀ (a'₂₈ : Int),
                                      ((k7 a'₂₈ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)) ->
                                       ((k11 a'₂₈ (nnz₁ + 1) (col_index₁ + 1) (values₁ + 1) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ True)))
                                     )
                                   ) ∧
                                  (∀ (nnz₂ : Int),
                                   ∀ (col_index₂ : Int),
                                    ∀ (values₂ : Int),
                                     ((k9 nnz₂ col_index₂ values₂ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ a'₂₃)) ->
                                      (((k5 nnz₂ col_index₂ values₂ (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉))) ∧
                                      (∀ (a'₃₂ : Int),
                                       ((k10 a'₃₂ nnz₂ col_index₂ values₂ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ a'₂₃)) ->
                                        ((k6 a'₃₂ nnz₂ col_index₂ values₂ (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉))) ∧
                                      (∀ (a'₃₃ : Int),
                                       ((k11 a'₃₃ nnz₂ col_index₂ values₂ rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉ nnz₁ col_index₁ values₁ (OpsRangeRange.start iter₁) (OpsRangeRange.end_ iter₁) (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) a'₂₀ a'₂₂ a'₂₃)) ->
                                        ((k7 a'₃₃ nnz₂ col_index₂ values₂ (OpsRangeRange.start r₁) (OpsRangeRange.end_ r₁) rows₀ cols₀ nnz₀ col_index₀ row_index₀ values₀ (OpsRangeRange.start iter₀) (OpsRangeRange.end_ iter₀) (OpsRangeRange.start r₀) (OpsRangeRange.end_ r₀) a'₉)))
                                      )
                                  )
                                 )
                              )
                          )
                   )
                  )
              )


def pf : SparseImpl__0__New := by
  unfold SparseImpl__0__New
  zap
  refine ⟨fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => a0 = a2 ∧ a1 = a2 ∧ a4 = a6,
          fun a0 a1 a2 a3 a4 a5 a6 a7 => a0 = a3 ∧ a1 = a3 ∧ a2 = a4 ∧ a5 = a6 ∧ 0 ≤ a4 ∧ a4 ≤ a6,
          fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 => b0 < b7,
          fun b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 => b0 ≤ b3, ?_⟩
  intro rows cols hrows hcols hrows2
  refine ⟨by grind, ?_⟩
  intro nnz col row val iter hk0 r0 hr0
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := hk0
  obtain ⟨hr0a, hr0b⟩ := hr0
  refine ⟨?_, ?_⟩
  · intro hexit hrowpos
    refine ⟨?_, e1, ?_, ?_⟩
    · intro a7 h7; grind
    · intro a8 h8; grind
    · grind
  · intro hcont a9 ha9 ha9pos hrowpos
    refine ⟨⟨e0, e1, rfl⟩, ?_, ?_, ?_⟩
    · intro a11 h11; grind
    · intro a12 h12; grind
    · intro nnz1 col1 val1 iter1 hk5 r1 hr1
      obtain ⟨f0, f1, f2⟩ := hk5
      obtain ⟨hr1a, hr1b⟩ := hr1
      refine ⟨?_, ?_⟩
      · intro hiexit; grind
      · intro hicont a20 ha20 ha20pos
        refine ⟨by grind, ?_⟩
        intro a22 hr22 ha22pos
        refine ⟨by grind, ?_⟩
        intro a23 nnz2 col2 val2 hri
        refine ⟨?_, ?_, ?_⟩
        · grind
        · intro a32 h32; grind
        · intro a33 h33; grind
end F
