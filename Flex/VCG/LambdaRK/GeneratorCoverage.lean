import Flex.VCG.LambdaRK.GeneratorSpecification

/-! Successful executable coverage checks imply declarative coverage. -/
namespace LambdaRK
private theorem eraseDups_length_properties (names : List String) : names.eraseDups.length ≤ names.length ∧
    (names.eraseDups.length = names.length → names.Nodup) := by
  generalize size : names.length = n
  induction n using Nat.strongRecOn generalizing names with
  | ind n ih =>
    cases names with
    | nil => simp
    | cons name names =>
      let rest := names.filter (fun b => !b == name)
      have bounded : rest.length ≤ names.length := List.length_filter_le _ _
      have smaller : rest.length < n := by simp only [List.length_cons] at size; omega
      obtain ⟨lengthBound, noDups⟩ := ih rest.length smaller rest rfl
      rw [List.eraseDups_cons, ← size]
      change rest.eraseDups.length + 1 ≤ names.length + 1 ∧ _
      constructor
      · omega
      · intro equal
        change rest.eraseDups.length + 1 = names.length + 1 at equal
        have eqLength : rest.length = names.length := by omega
        have same : rest = names := (List.filter_sublist (p := fun b => !b == name) (l := names)).eq_of_length eqLength
        have nodup := noDups (by omega)
        rw [same] at nodup
        apply List.nodup_cons.mpr
        refine ⟨?_, nodup⟩
        intro member
        have bad : name ∈ rest := same.symm ▸ member
        simp [rest] at bad


theorem nodup_of_eraseDups_length (names : List String)
    (same : names.eraseDups.length = names.length) : names.Nodup :=
  (eraseDups_length_properties names).2 same

theorem match_coverage_sound (data : DataDecl) (branches : List (String × List String × Expr))
    (covered : ((branches.map (·.1)).length == data.ctors.length &&
      (branches.map (·.1)).eraseDups.length == (branches.map (·.1)).length &&
      data.ctors.all (fun ctor => (branches.map (·.1)).contains ctor.name)) = true) :
    (branches.map (·.1)).length = data.ctors.length ∧
    (branches.map (·.1)).Nodup ∧
    (∀ ctor ∈ data.ctors, ctor.name ∈ branches.map (·.1)) := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem] at covered
  exact ⟨covered.1.1, nodup_of_eraseDups_length _ covered.1.2, covered.2⟩

end LambdaRK
