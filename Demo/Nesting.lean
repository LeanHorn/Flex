import Flex

/-! Ten acyclic, SAT-validated CHC-COMP queries. Inspect the goals after
`nest_chc` and `zap` to see factoring and predicate elimination separately. -/

namespace NestingDemo

-- Source: lean-noquals/hopv/lia/mochi/intro2_000.lean
theorem intro2 :
  ∃ f_unknown_2 : Int → Int → Prop,
  ∃ f_unknown_1 : Int → Prop,
  ∃ h_unknown_5 : Int → Prop,
  (∀ A : Int, ∀ B : Int, ((f_unknown_1 A) ∧ (B = (1 + A)) → (f_unknown_2 B A)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((f_unknown_2 A B) ∧ (¬(0 = C)) ∧ (¬((0 = C) = (B ≥ 0))) → (h_unknown_5 A)))
  ∧ (∀ A : Int, ∀ B : Int, ((¬(0 = B)) ∧ (¬((0 = B) = (A ≥ 0))) → (f_unknown_1 A)))
  ∧ (∀ A : Int, ∀ B : Int, ((h_unknown_5 A) ∧ (0 = B) ∧ ((0 = B) = (A ≤ 0)) → False)) := by
  nest_chc
  zap
  all_goals grind

-- Source: lean-noquals/hopv/lia/mochi/intro3_000.lean
theorem intro3 :
  ∃ f_unknown_2 : Int → Int → Prop,
  ∃ f_unknown_1 : Int → Prop,
  ∃ h_unknown_6 : Int → Int → Prop,
  (∀ A : Int, ∀ B : Int, ((f_unknown_1 A) ∧ (B = (1 + A)) → (f_unknown_2 B A)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((f_unknown_2 A B) ∧ (¬(0 = C)) ∧ (¬((0 = C) = (B ≥ 0))) → (h_unknown_6 A B)))
  ∧ (∀ A : Int, ∀ B : Int, ((¬(0 = B)) ∧ (¬((0 = B) = (A ≥ 0))) → (f_unknown_1 A)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((h_unknown_6 B A) ∧ (0 = C) ∧ ((0 = C) = (B ≤ A)) → False)) := by
  nest_chc
  zap
  all_goals grind

-- Source: lean-noquals/hopv/lia/termination/alias_partial01_000.lean
theorem alias_partial01 :
  ∃ f_1030_unknown_5 : Int → Int → Int → Prop,
  ∃ main_1035_unknown_25 : Int → Int → Int → Prop,
  ∃ fail_unknown_17 : Int → Prop,
  (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ((f_1030_unknown_5 C B A) ∧ (D = 1) ∧ (¬(0 = A)) → (fail_unknown_17 D)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ∀ E : Int, ∀ F : Int, ((main_1035_unknown_25 C B A) ∧ (E = 0) ∧ (D = 0) ∧ (F = 1) → (f_1030_unknown_5 F E D)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((B = 0) ∧ (A = 0) ∧ (C = 1) → (main_1035_unknown_25 C B A)))
  ∧ (∀ A : Int, ((fail_unknown_17 A) → False)) := by
  nest_chc
  zap
  all_goals grind

-- Source: lean-noquals/hopv/lia/termination/zip00_000.lean
theorem zip00 :
  ∃ fail_unknown_3 : Int → Prop,
  ∃ zip_1030_unknown_12 : Int → Int → Int → Int → Int → Int → Int → Int → Prop,
  (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ∀ E : Int, ∀ F : Int, ∀ G : Int, ∀ H : Int, ∀ I : Int, ((zip_1030_unknown_12 H G F E D C B A) ∧ (I = 1) ∧ (¬(0 = E)) → (fail_unknown_3 I)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ∀ E : Int, ∀ v_5 : Int, ∀ v_6 : Int, ∀ v_7 : Int, ((D = 0) ∧ (C = 0) ∧ (E = 0) ∧ (v_5 = E) ∧ (v_6 = D) ∧ (v_7 = C) → (zip_1030_unknown_12 B E D C A v_5 v_6 v_7)))
  ∧ (∀ A : Int, ((fail_unknown_3 A) → False)) := by
  nest_chc
  zap
  all_goals grind

-- Source: lean-noquals/hopv/lia/mochi/twice_000.lean
theorem twice :
  ∃ f_unknown_2 : Int → Int → Prop,
  ∃ twice_unknown_4 : Int → Int → Prop,
  ∃ twice_unknown_6 : Int → Int → Prop,
  (∀ A : Int, ∀ B : Int, ((A = (2 * B)) → (f_unknown_2 A B)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ((f_unknown_2 A D) ∧ (¬(0 = C)) ∧ ((0 = C) = (B ≤ 0)) → (twice_unknown_4 A D)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ((twice_unknown_4 C B) ∧ (twice_unknown_4 D C) ∧ (A = D) → (twice_unknown_6 A B)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ((twice_unknown_6 C A) ∧ ((0 = D) = (C ≤ A)) ∧ (¬(0 = B)) ∧ (0 = D) ∧ ((0 = B) = (A ≤ 0)) → False)) := by
  nest_chc
  zap
  all_goals grind

/-
⊢ ∀ (A B C D : Int),
  (∃ A_1 B C_1 D,
        ((∃ A B_1 C D, ((∃ A_2 B, A_2 = 2 * B ∧ A = A_2 ∧ D = B) ∧ ¬0 = C ∧ (0 = C) = (B_1 ≤ 0)) ∧ C_1 = A ∧ B = D) ∧
            (∃ A B C D_1,
                ((∃ A_2 B, A_2 = 2 * B ∧ A = A_2 ∧ D_1 = B) ∧ ¬0 = C ∧ (0 = C) = (B ≤ 0)) ∧ D = A ∧ C_1 = D_1) ∧
              A_1 = D) ∧
          C = A_1 ∧ A = B) ∧
      (0 = D) = (C ≤ A) ∧ ¬0 = B ∧ 0 = D ∧ (0 = B) = (A ≤ 0) →
    False

  ⊢ ∀ (A B C D : Int),
  (∃ A_1 B C_1 D,
      (∃ A B_1 C D, (∃ B, A = 2 * B ∧ A = A ∧ D = B) ∧ ¬0 = C ∧ (0 = C) = (B_1 ≤ 0) ∧ C_1 = A ∧ B = D) ∧
        (∃ A B C D_1, (∃ B, A = 2 * B ∧ A = A ∧ D_1 = B) ∧ ¬0 = C ∧ (0 = C) = (B ≤ 0) ∧ D = A ∧ C_1 = D_1) ∧
          A_1 = D ∧ C = A_1 ∧ A = B) →
    (0 = D) = (C ≤ A) → ¬0 = B → 0 = D → (0 = B) = (A ≤ 0) → False

-/
-- Source: lean-noquals/hopv/lia/fpice/inductive6_000.lean
theorem inductive6 :
  ∃ f_unknown_4 : Int → Int → Prop,
  ∃ decr_unknown_2 : Int → Int → Prop,
  ∃ f_unknown_6 : Int → Int → Prop,
  (∀ A : Int, ∀ B : Int, ((A = ((-1) + B)) → (decr_unknown_2 A B)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((decr_unknown_2 A C) ∧ (B = 3) → (f_unknown_4 A C)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ((f_unknown_4 D B) ∧ (¬(0 = C)) ∧ (A = D) ∧ ((0 = C) = (B ≤ 0)) → (f_unknown_6 A B)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((0 = C) ∧ (A = 1) ∧ ((0 = C) = (B ≤ 0)) → (f_unknown_6 A B)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((f_unknown_6 B A) ∧ (0 = C) ∧ (A = 3) ∧ ((0 = C) = (B ≤ 0)) → False)) := by
  nest_chc
  zap
  all_goals grind

-- Source: lean-noquals/hopv/lia/termination/Fibonacci00_000.lean
theorem Fibonacci00 :
  ∃ fib_1030_unknown_7 : Int → Int → Int → Prop,
  ∃ fail_unknown_3 : Int → Prop,
  (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ((fib_1030_unknown_7 A C B) ∧ (D = 1) ∧ (¬(0 = B)) → (fail_unknown_3 D)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((B = 0) ∧ (C = 0) → (fib_1030_unknown_7 A C B)))
  ∧ (∀ A : Int, ((fail_unknown_3 A) → False)) := by
  nest_chc
  zap
  all_goals grind

-- Source: lean-noquals/hopv/lia/mochi/exception_000.lean
theorem exception :
  ∃ f_unknown_2 : Int → Int → Prop,
  ∃ f_unknown_1 : Int → Prop,
  ∃ g_unknown_5 : Int → Prop,
  (∀ A : Int, (f_unknown_1 A))
  ∧ (∀ A : Int, ∀ B : Int, ((f_unknown_2 A B) → (g_unknown_5 A)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((f_unknown_1 A) ∧ (0 = B) ∧ (C = 0) ∧ (¬((0 = B) = (A ≥ 0))) → (f_unknown_2 C A)))
  ∧ (∀ A : Int, ∀ B : Int, ((g_unknown_5 A) ∧ (0 = B) ∧ (¬((0 = B) = (A = 0))) → False)) := by
  nest_chc
  zap
  all_goals grind

-- Source: lean-noquals/hopv/lia/mochi/intro1_000.lean
theorem intro1 :
  ∃ f_unknown_2 : Int → Int → Prop,
  ∃ f_unknown_1 : Int → Prop,
  ∃ h_unknown_5 : Int → Prop,
  (∀ A : Int, ∀ B : Int, ((f_unknown_1 A) ∧ (B = (1 + A)) → (f_unknown_2 B A)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((f_unknown_2 A B) ∧ (¬(0 = C)) ∧ ((0 = C) = (B ≤ 0)) → (h_unknown_5 A)))
  ∧ (∀ A : Int, ∀ B : Int, ((¬(0 = B)) ∧ ((0 = B) = (A ≤ 0)) → (f_unknown_1 A)))
  ∧ (∀ A : Int, ∀ B : Int, ((h_unknown_5 A) ∧ (0 = B) ∧ ((0 = B) = (A ≤ 0)) → False)) := by
  nest_chc
  zap
  all_goals grind

-- Source: lean-noquals/hopv/lia/mochi/max_000.lean
theorem max :
  ∃ f_unknown_3 : Int → Int → Int → Prop,
  ∃ max_unknown_6 : Int → Int → Int → Prop,
  ∃ max_unknown_10 : Int → Int → Int → Int → Prop,
  (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ((¬(0 = D)) ∧ (A = B) ∧ (¬((0 = D) = (B ≥ C))) → (f_unknown_3 A C B)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ((0 = D) ∧ (A = C) ∧ (¬((0 = D) = (B ≥ C))) → (f_unknown_3 A C B)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ((f_unknown_3 B A C) → (max_unknown_6 B A C)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ∀ E : Int, ∀ F : Int, ((max_unknown_6 E C B) ∧ (max_unknown_6 F D E) ∧ (A = F) → (max_unknown_10 A D C B)))
  ∧ (∀ A : Int, ∀ B : Int, ∀ C : Int, ∀ D : Int, ∀ E : Int, ∀ F : Int, ((max_unknown_10 F C B A) ∧ (f_unknown_3 D F A) ∧ (0 = E) ∧ (¬((0 = E) = (D = F))) → False)) := by
  nest_chc
  zap
  all_goals grind

end NestingDemo
