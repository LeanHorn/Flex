import Flex.VCG.LambdaRK.DatatypeModel
import Flex.VCG.LambdaRK.SubstitutionLemmas

/-! Relating raw declaration interpretations to instantiated source types.
Raw declaration fields cannot mention ambient logical variables or trailing
type candidates. Instantiation may introduce both, so the bridge retains the
actual candidate interpretation of each source argument. -/
namespace LambdaRK

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

theorem Ty.denote_raw_environment
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (type : Ty) (types : TypeEnvironment) (left right : Environment)
    (raw : type.isRaw = true) :
    type.denote signature model assignment types left =
      type.denote signature model assignment types right := by
  apply type.environment_congr signature model assignment types left right
  simp [type.freeVars_nil_of_raw raw]

/-- Declaration fields see their declared parameters only; arbitrary ambient
type candidates and logical slots are irrelevant until substitution. -/
theorem Ty.denote_raw_parameters
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (field : Ty) (parameters ambient : TypeEnvironment) (environment : Environment)
    (raw : field.isRaw = true) (hasScope : field.TypeScoped parameters.length) :
    field.denote signature model assignment (parameters ++ ambient) environment =
      field.denote signature model assignment parameters [] := by
  rw [field.denote_types_congr signature model assignment parameters.length
    (parameters ++ ambient) parameters environment hasScope
    (fun _ bound => List.getElem?_append_left bound)]
  exact field.denote_raw_environment signature model assignment parameters environment [] raw

/-- Source arguments are interpreted in the caller's context, while raw
declaration fields are interpreted with those candidates as their whole type
environment. This is the sole substitution interface used by model adequacy. -/
theorem Ty.instantiateParams_raw_denote
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment) (arguments : List Ty)
    (field : Ty) (raw : field.isRaw = true) (hasScope : field.TypeScoped arguments.length)
    (value : Value) :
    (Ty.instantiateParams arguments field).denote signature model assignment types environment value ↔
      field.denote signature model assignment
        (arguments.map (Ty.denote signature model assignment types environment)) [] value := by
  rw [field.instantiateParams_denote arguments signature model assignment types environment]
  rw [field.denote_raw_parameters signature model assignment _ types environment raw
    (by simpa using hasScope)]

private theorem findDataDecl_of_mem
    (declarations : List DataDecl) (unique : (declarations.map DataDecl.name).Nodup)
    (decl : DataDecl) (member : decl ∈ declarations) :
    declarations.find? (·.name == decl.name) = some decl := by
  induction declarations with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | member
    · subst decl
      simp
    · have different : head.name ≠ decl.name := by
        intro equal
        exact unique.1 (List.mem_map.mpr ⟨decl, member, equal.symm⟩)
      simp only [List.find?_cons, beq_eq_false_iff_ne.mpr different]
      exact ih unique.2 member

theorem Signature.findData_eq_some_iff
    (signature : Signature) (unique : (signature.datatypes.map DataDecl.name).Nodup)
    (name : String) (decl : DataDecl) :
    signature.findData name = some decl ↔ decl ∈ signature.datatypes ∧ decl.name = name := by
  constructor
  · intro found
    exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩
  · rintro ⟨member, rfl⟩
    exact findDataDecl_of_mem signature.datatypes unique decl member

/-- Convert the constructor laws of the positive fixed-point model into the
source-type adequacy interface used by semantic typing. -/
theorem datatypeAdequate_of_constructor_laws
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (unique : (signature.datatypes.map DataDecl.name).Nodup)
    (fieldsScoped : ∀ declaration ∈ signature.datatypes, ∀ constructor ∈ declaration.ctors,
      ∀ field ∈ constructor.fields, field.isRaw = true ∧ field.TypeScoped declaration.params)
    (laws : DataModel.Laws signature assignment signature.datatypes model) :
    DatatypeAdequate signature model assignment := by
  intro types environment name arguments value
  simp only [Ty.denote]
  rw [laws]
  constructor
  · rintro ⟨declaration, member, nameEqual, arity, constructor, constructorMem,
      fields, shape, typed⟩
    have length : declaration.params = arguments.length := by simpa using arity.symm
    refine ⟨declaration, constructor, fields,
      (signature.findData_eq_some_iff unique name declaration).mpr ⟨member, nameEqual⟩,
      length, constructorMem, shape, ?_⟩
    apply typed.mono_mem
    intro field fieldMem fieldValue fieldTyped
    obtain ⟨raw, hasScope⟩ := fieldsScoped declaration member constructor constructorMem field fieldMem
    exact (field.instantiateParams_raw_denote signature model assignment types environment arguments
      raw (length ▸ hasScope) fieldValue).mpr fieldTyped
  · rintro ⟨declaration, constructor, fields, found, length, constructorMem, shape, typed⟩
    obtain ⟨member, nameEqual⟩ := (signature.findData_eq_some_iff unique name declaration).mp found
    refine ⟨declaration, member, nameEqual, by simpa using length.symm,
      constructor, constructorMem, fields, shape, ?_⟩
    apply typed.mono_mem
    intro field fieldMem fieldValue fieldTyped
    obtain ⟨raw, hasScope⟩ := fieldsScoped declaration member constructor constructorMem field fieldMem
    exact (field.instantiateParams_raw_denote signature model assignment types environment arguments
      raw (length ▸ hasScope) fieldValue).mp fieldTyped

end LambdaRK
