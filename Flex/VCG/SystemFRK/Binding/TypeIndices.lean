import Flex.VCG.SystemFRK.Binding.Environment
import Flex.VCG.SystemFRK.Binding.Lemmas

/-! Renaming and weakening of semantic type indices, including under `all`. -/
namespace SystemFRK

theorem Ty.mapTypes_scoped (type : Ty) (f : Nat → Nat → Ty)
    (crossed source target : Nat)
    (indices : ∀ d i, i < source + d → (f (crossed + d) i).TypeScoped (target + d))
    (hasScope : type.TypeScoped source) :
    (type.mapTypes f crossed).TypeScoped target := by
  induction type using Ty.rec
      (motive_2 := fun ts => ∀ crossed source target,
        (∀ d i, i < source + d → (f (crossed + d) i).TypeScoped (target + d)) →
        (∀ t ∈ ts, t.TypeScoped source) →
        ∀ t ∈ ts.map (·.mapTypes f crossed), t.TypeScoped target)
      generalizing crossed source target with
  | var i => simpa [Ty.mapTypes, Ty.TypeScoped] using indices 0 i (by simpa [Ty.TypeScoped] using hasScope)
  | int => simp [Ty.mapTypes, Ty.TypeScoped]
  | bool => simp [Ty.mapTypes, Ty.TypeScoped]
  | data name args ih =>
    simp only [Ty.mapTypes, Ty.TypeScoped] at *
    exact ih crossed source target indices hasScope
  | arrow name a b ia ib =>
    simp only [Ty.mapTypes, Ty.TypeScoped] at hasScope ⊢
    exact ⟨ia crossed source target indices hasScope.1, ib crossed source target indices hasScope.2⟩
  | all body ih =>
    simp only [Ty.mapTypes, Ty.TypeScoped] at hasScope ⊢
    apply ih (crossed + 1) (source + 1) (target + 1) _ hasScope
    intro d i hi
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      indices (d + 1) i (by omega)
  | refine base pred ih =>
    simp only [Ty.mapTypes, Ty.TypeScoped] at hasScope ⊢
    exact ih crossed source target indices hasScope
  | nil => simp_all
  | cons t ts ih it =>
    rename_i crossed source target indices hasScope t' member
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with rfl | member
    · exact ih crossed source target indices (hasScope _ (by simp))
    · exact it crossed source target indices (fun t ht => hasScope t (by simp [ht])) t' member

theorem Ty.shiftTypes_scoped (type : Ty) (depth amount cutoff : Nat)
    (hasScope : type.TypeScoped depth) :
    (type.shiftTypes amount cutoff).TypeScoped (depth + amount) := by
  apply type.mapTypes_scoped _ 0 depth (depth + amount) _ hasScope
  intro d i hi
  simp only [Nat.zero_add, Ty.TypeScoped]
  split <;> omega

theorem Ty.substType_scoped (body replacement : Ty) (depth index : Nat)
    (indexInScope : index ≤ depth)
    (bodyScoped : body.TypeScoped (depth + 1))
    (replacementScoped : replacement.TypeScoped depth) :
    (Ty.substType replacement index body).TypeScoped depth := by
  unfold Ty.substType
  apply Ty.mapTypes_scoped _ _ 0 (depth + 1) depth
  · intro d i hi
    simp only [Nat.zero_add]
    split
    · apply Ty.shiftTypes_scoped
      exact (replacement.freshenBinders_scoped depth _).mpr replacementScoped
    · rename_i different
      simp only [Ty.TypeScoped]
      have ne : i ≠ index + d := by simpa using different
      split <;> omega
  · exact (body.freshenBinders_scoped (depth + 1) _).mpr bodyScoped

theorem Ty.instantiateParams_scoped (arguments : List Ty) (field : Ty) (depth : Nat)
    (fieldScoped : field.TypeScoped arguments.length)
    (argumentsScoped : ∀ argument ∈ arguments, argument.TypeScoped depth) :
    (Ty.instantiateParams arguments field).TypeScoped depth := by
  let args := arguments.map (·.freshenBinders field.allTermNames)
  have argsScoped : ∀ a ∈ args, a.TypeScoped depth := by
    intro a ha
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp ha
    exact (old.freshenBinders_scoped depth _).mpr (argumentsScoped old member)
  unfold Ty.instantiateParams
  apply Ty.mapTypes_scoped _ _ 0 arguments.length depth
  · intro d i hi
    simp only [Nat.zero_add]
    split
    · simp only [Ty.TypeScoped]; omega
    · rename_i hge
      change (match args[i - d]? with
        | some a => a.shiftTypes d 0
        | none => Ty.var (i - args.length)).TypeScoped (depth + d)
      cases found : args[i - d]? with
      | some a =>
        exact a.shiftTypes_scoped depth d 0 (argsScoped a (List.mem_of_getElem? found))
      | none =>
        have bound := List.getElem?_eq_none_iff.mp found
        have length : args.length = arguments.length := by simp [args]
        omega
  · exact (field.freshenBinders_scoped arguments.length _).mpr fieldScoped

/-- A simultaneous reindexing respects the interpretation when its lookup
law remains true after any number of polymorphic binders. -/
theorem Ty.reindex_denote (type : Ty) (indices : Nat → Nat → Nat)
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (crossed : Nat) (source target : TypeEnvironment) (environment : Environment)
    (lookup : ∀ (boundTypes : TypeEnvironment) i,
      (boundTypes ++ target)[indices (crossed + boundTypes.length) i]?.getD (fun _ => False) =
        (boundTypes ++ source)[i]?.getD (fun _ => False)) :
    (type.mapTypes (fun d i => .var (indices d i)) crossed).denote
        signature model assignment target environment =
      type.denote signature model assignment source environment := by
  induction type using Ty.rec
      (motive_2 := fun ts => ∀ crossed source target environment,
        (∀ (boundTypes : TypeEnvironment) i,
          (boundTypes ++ target)[indices (crossed + boundTypes.length) i]?.getD (fun _ => False) =
            (boundTypes ++ source)[i]?.getD (fun _ => False)) →
        (ts.map (·.mapTypes (fun d i => .var (indices d i)) crossed)).map
            (Ty.denote signature model assignment target environment) =
          ts.map (Ty.denote signature model assignment source environment))
      generalizing crossed source target environment with
  | var i => simpa [Ty.mapTypes, Ty.denote] using lookup [] i
  | int => simp [Ty.mapTypes, Ty.denote]
  | bool => simp [Ty.mapTypes, Ty.denote]
  | data name args ih => simp only [Ty.mapTypes, Ty.denote, ih _ _ _ _ lookup]
  | arrow name a b ia ib => simp only [Ty.mapTypes, Ty.denote, ia _ _ _ _ lookup, ib _ _ _ _ lookup]
  | all body ih =>
    have next (candidate : Candidate) := ih (crossed + 1) (candidate :: source)
      (candidate :: target) environment (by
        intro boundTypes i
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          lookup (boundTypes ++ [candidate]) i)
    simp only [Ty.mapTypes, Ty.denote, next]
  | refine base pred ih => simp only [Ty.mapTypes, Ty.denote, ih _ _ _ _ lookup]
  | nil => simp
  | cons t ts ih it =>
    rename_i crossed source target environment lookup
    simp only [List.map_cons, ih _ _ _ _ lookup, it _ _ _ _ lookup]

theorem Ty.shiftTypes_denote
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types extraTypes : TypeEnvironment) (environment : Environment) (body : Ty) :
    (body.shiftTypes extraTypes.length 0).denote
        signature model assignment (extraTypes ++ types) environment =
      body.denote signature model assignment types environment := by
  apply body.reindex_denote _ signature model assignment 0 types (extraTypes ++ types) environment
  intro boundTypes i
  simp only [Nat.zero_add]
  split
  · rename_i hi
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right hi,
      List.getElem?_append_right (by omega)]
    congr 2
    omega
  · rename_i hi
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

theorem Ty.denote_types_congr
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (type : Ty) (depth : Nat) (left right : TypeEnvironment) (environment : Environment)
    (hasScope : type.TypeScoped depth)
    (agree : ∀ index, index < depth → left[index]? = right[index]?) :
    type.denote signature model assignment left environment =
      type.denote signature model assignment right environment := by
  induction type using Ty.rec
    (motive_2 := fun ts => ∀ depth left right environment,
      (∀ type ∈ ts, type.TypeScoped depth) →
      (∀ index, index < depth → left[index]? = right[index]?) →
      ts.map (Ty.denote signature model assignment left environment) =
        ts.map (Ty.denote signature model assignment right environment))
    generalizing depth left right environment with
  | var index =>
    simp only [Ty.TypeScoped] at hasScope
    simp only [Ty.denote, agree index hasScope]
  | int => simp only [Ty.denote]
  | bool => simp only [Ty.denote]
  | data name args ih =>
    simp only [Ty.TypeScoped] at hasScope
    simp only [Ty.denote]
    rw [ih depth left right environment hasScope agree]
  | arrow name a b ia ib =>
    simp only [Ty.TypeScoped] at hasScope
    have leftEq := ia depth left right environment hasScope.1 agree
    have rightEq (value : Value) := ib depth left right (environment.bind name value) hasScope.2 agree
    simp only [Ty.denote, leftEq, rightEq]
  | all body ih =>
    simp only [Ty.TypeScoped] at hasScope
    have inner (candidate : Candidate) :
        body.denote signature model assignment (candidate :: left) environment =
          body.denote signature model assignment (candidate :: right) environment := by
      apply ih (depth + 1) (candidate :: left) (candidate :: right) environment hasScope
      intro index bound
      cases index with
      | zero => rfl
      | succ index => simpa using agree index (by omega)
    simp only [Ty.denote, inner]
  | refine base predicate ih =>
    simp only [Ty.TypeScoped] at hasScope
    simp only [Ty.denote, ih depth left right environment hasScope agree]
  | nil => rfl
  | cons type types ih it =>
    rename_i depth left right environment hasScope agree
    simp only [List.map_cons]
    rw [ih depth left right environment (hasScope type (by simp)) agree,
      it depth left right environment (fun type member => hasScope type (by simp [member])) agree]

end SystemFRK
