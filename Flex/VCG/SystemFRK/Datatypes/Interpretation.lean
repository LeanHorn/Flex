import Flex.VCG.SystemFRK.Datatypes.Model
import Flex.VCG.SystemFRK.Binding.Substitution

/-! Relating raw datatype fields to instantiated source types. -/
namespace SystemFRK

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

/-- Interpret source arguments in the caller context before substituting into raw declaration fields. -/
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

end SystemFRK
