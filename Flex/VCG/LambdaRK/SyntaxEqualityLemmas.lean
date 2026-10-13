import Flex.VCG.LambdaRK.Syntax

/-! The kernel-reducible syntax comparisons are exact syntactic equality.
In particular, the list comparisons check lengths before zipping fields. -/
namespace LambdaRK

theorem LTerm.equal_eq_true (left right : LTerm) : left.equal right = true ↔ left = right := by
  induction left using LTerm.rec
    (motive_2 := fun fields => ∀ others,
      (fields.length == others.length &&
        ((fields.map fun field => field.equal).zip others).all
          (fun (compare, other) => compare other)) = true ↔ fields = others)
    generalizing right with
  | var name => cases right <;> simp [LTerm.equal]
  | int n => cases right <;> simp [LTerm.equal]
  | bool b => cases right <;> simp [LTerm.equal]
  | add a b ia ib => cases right <;> simp [LTerm.equal, ia, ib]
  | measure name a ia => cases right <;> simp [LTerm.equal, ia]
  | ctor name fields ih =>
    cases right with
    | ctor other others =>
      simp only [LTerm.equal, Bool.and_eq_true, beq_iff_eq, LTerm.ctor.injEq]
      have fieldsEq := ih others
      simp only [Bool.and_eq_true, beq_iff_eq] at fieldsEq
      exact (and_assoc).trans (and_congr Iff.rfl fieldsEq)
    | _ => simp [LTerm.equal]
  | nil => rename_i others; cases others <;> simp
  | cons a as ia ib =>
    rename_i others
    cases others with
    | nil => simp
    | cons b bs =>
      simp only [List.length_cons, beq_iff_eq, Nat.add_right_cancel_iff,
        List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true, ia, List.cons.injEq]
      have tail := ib bs
      simp only [Bool.and_eq_true, beq_iff_eq] at tail
      constructor
      · rintro ⟨len, eq, rest⟩
        exact ⟨eq, tail.mp ⟨len, rest⟩⟩
      · rintro ⟨eq, rest⟩
        obtain ⟨len, comp⟩ := tail.mpr rest
        exact ⟨len, eq, comp⟩

instance : LawfulBEq LTerm where
  eq_of_beq := fun h => LTerm.equal_eq_true _ _ |>.mp h
  rfl := fun {a} => LTerm.equal_eq_true a a |>.mpr rfl

deriving instance ReflBEq, LawfulBEq for Formula

deriving instance ReflBEq, LawfulBEq for Atom

theorem Ty.equal_eq_true (left right : Ty) : left.equal right = true ↔ left = right := by
  induction left using Ty.rec
    (motive_2 := fun args => ∀ others,
      (args.length == others.length &&
        ((args.map fun arg => arg.equal).zip others).all
          (fun (compare, other) => compare other)) = true ↔ args = others)
    generalizing right with
  | var index => cases right <;> simp [Ty.equal]
  | int => cases right <;> simp [Ty.equal]
  | bool => cases right <;> simp [Ty.equal]
  | arrow name a b ia ib => cases right <;> simp [Ty.equal, ia, ib, and_assoc]
  | all a ia => cases right <;> simp [Ty.equal, ia]
  | refine a p ia => cases right <;> simp [Ty.equal, ia]
  | data name args ih =>
    cases right with
    | data other others =>
      simp only [Ty.equal, Bool.and_eq_true, beq_iff_eq, Ty.data.injEq]
      have argsEq := ih others
      simp only [Bool.and_eq_true, beq_iff_eq] at argsEq
      exact (and_assoc).trans (and_congr Iff.rfl argsEq)
    | _ => simp [Ty.equal]
  | nil => rename_i others; cases others <;> simp
  | cons a as ia ib =>
    rename_i others
    cases others with
    | nil => simp
    | cons b bs =>
      simp only [List.length_cons, beq_iff_eq, Nat.add_right_cancel_iff,
        List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true, ia, List.cons.injEq]
      have tail := ib bs
      simp only [Bool.and_eq_true, beq_iff_eq] at tail
      constructor
      · rintro ⟨len, eq, rest⟩
        exact ⟨eq, tail.mp ⟨len, rest⟩⟩
      · rintro ⟨eq, rest⟩
        obtain ⟨len, comp⟩ := tail.mpr rest
        exact ⟨len, eq, comp⟩

instance : LawfulBEq Ty where
  eq_of_beq := fun h => Ty.equal_eq_true _ _ |>.mp h
  rfl := fun {a} => Ty.equal_eq_true a a |>.mpr rfl

end LambdaRK
