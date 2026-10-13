import Flex.VCG.SystemFRK.Semantics.StructuralOrder
import Flex.VCG.SystemFRK.Semantics.Determinism

/-! Validated measures are total on typed datatype values. -/
namespace SystemFRK

theorem All₂.getElem?_left {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (related : All₂ relation left right)
    {index : Nat} {entry : α} (found : left[index]? = some entry) :
    ∃ value, right[index]? = some value ∧ relation entry value := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst entry
      exact ⟨_, rfl, head⟩
    | succ index => exact ih (by simpa using found)

private theorem instantiateParams_int (arguments : List Ty) :
    Ty.instantiateParams arguments .int = .int := by
  simp [Ty.instantiateParams, Ty.freshenBinders, Ty.freshenBindersAux, Ty.mapTypes]

private theorem instantiateParams_data (arguments parameters : List Ty) (name : String) :
    ∃ instantiated, Ty.instantiateParams arguments (.data name parameters) = .data name instantiated := by
  simp only [Ty.instantiateParams, Ty.freshenBinders, Ty.freshenBindersAux, Ty.mapTypes]
  exact ⟨_, rfl⟩

/-- Validation gives the exact branch that the operational semantics selects. -/
theorem Signature.measure_case_ready (signature : Signature)
    (accepted : signature.validate = .ok ())
    {name : String} {measure : MeasureDecl}
    (declared : signature.findMeasure name = some measure)
    {datatype : DataDecl} (dataFound : signature.findData measure.datatype = some datatype)
    {constructor : CtorDecl} (member : constructor ∈ datatype.ctors) :
    ∃ branch, measure.cases.find? (fun c => c.ctor == constructor.name) = some branch ∧
      branch.body.ready measure.datatype constructor.fields = true := by
  have measures := signature.validate_measuresReady 256 accepted
  have measureMember : measure ∈ signature.measures := List.mem_of_find?_eq_some declared
  have ready := List.all_eq_true.mp measures measure measureMember
  simp only [dataFound] at ready
  have constructorReady := List.all_eq_true.mp ready constructor member
  split at constructorReady
  · contradiction
  · exact ⟨_, ‹_ = some _›, constructorReady⟩

theorem measure_total
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (types : TypeEnvironment) (environment : Environment)
    (name : String) (declaration : MeasureDecl) (arguments : List Ty) (value : Value)
    (declared : signature.findMeasure name = some declaration)
    (typed : (Ty.data declaration.datatype arguments).denote
      signature model assignment types environment value) :
    ∃ result, MeasureEval signature name value result := by
  induction value using Smaller.induction generalizing arguments with
  | step value ih =>
    obtain ⟨datatype, constructor, fields, dataFound, _, member, rfl, fieldsTyped⟩ :=
      (adequate types environment declaration.datatype arguments value).mp typed
    obtain ⟨branch, branchFound, branchReady⟩ :=
      signature.measure_case_ready validSignature declared dataFound member
    suffices bodyTotal : ∀ body, body.ready declaration.datatype constructor.fields = true →
        ∃ result, MeasureBodyEval signature name fields body result by
      obtain ⟨result, evaluates⟩ := bodyTotal branch.body branchReady
      exact ⟨result, .constructor declared branchFound evaluates⟩
    intro body ready
    induction body with
    | literal integer => exact ⟨integer, .literal⟩
    | field index =>
      simp only [MeasureBody.ready] at ready
      split at ready <;> try contradiction
      obtain ⟨value, found, valueTyped⟩ := fieldsTyped.getElem?_left ‹_ = some .int›
      rw [instantiateParams_int] at valueTyped
      simp only [Ty.denote, LSort.contains] at valueTyped
      obtain ⟨integer, rfl⟩ := valueTyped
      exact ⟨integer, .field found⟩
    | recur index =>
      simp only [MeasureBody.ready] at ready
      split at ready <;> try contradiction
      rename_i fieldName parameters fieldFound
      have names : fieldName = declaration.datatype := by simpa using ready
      subst fieldName
      obtain ⟨smaller, smallerFound, smallerTyped⟩ := fieldsTyped.getElem?_left fieldFound
      obtain ⟨instantiated, instantiatedEq⟩ :=
        instantiateParams_data arguments parameters declaration.datatype
      rw [instantiatedEq] at smallerTyped
      obtain ⟨result, evaluates⟩ := ih smaller
        (.field (List.mem_of_getElem? smallerFound)) instantiated smallerTyped
      exact ⟨result, .recur smallerFound evaluates⟩
    | add left right leftIH rightIH =>
      have parts := Bool.and_eq_true_iff.mp ready
      obtain ⟨leftResult, leftEval⟩ := leftIH parts.1
      obtain ⟨rightResult, rightEval⟩ := rightIH parts.2
      exact ⟨leftResult + rightResult, .add leftEval rightEval⟩

/-- The selected measure equation supports both construction and rewriting. -/
theorem MeasureEval.defining_equation
    (declared : signature.findMeasure name = some declaration)
    (selected : declaration.cases.find? (fun c => c.ctor == ctor) = some branch) :
    MeasureEval signature name (.ctor ctor fields) result ↔
      MeasureBodyEval signature name fields branch.body result := by
  constructor
  · intro evaluation
    cases evaluation with
    | constructor declarationFound branchFound body =>
      have declarations := Option.some.inj (declared.symm.trans declarationFound)
      subst_vars
      have branches := Option.some.inj (selected.symm.trans branchFound)
      subst_vars
      exact body
  · exact MeasureEval.constructor declared selected

theorem MeasureBodyEval.literal_iff :
    MeasureBodyEval signature name fields (.literal integer) result ↔ result = integer := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · rintro rfl; exact .literal

theorem MeasureBodyEval.field_iff :
    MeasureBodyEval signature name fields (.field index) result ↔
      fields[index]? = some (.int result) := by
  constructor
  · intro evaluation; cases evaluation with | field found => exact found
  · exact MeasureBodyEval.field

theorem MeasureBodyEval.recur_iff :
    MeasureBodyEval signature name fields (.recur index) result ↔
      ∃ value, fields[index]? = some value ∧ MeasureEval signature name value result := by
  constructor
  · intro evaluation; cases evaluation with | recur found recursive => exact ⟨_, found, recursive⟩
  · rintro ⟨_, found, recursive⟩; exact .recur found recursive

theorem MeasureBodyEval.add_iff :
    MeasureBodyEval signature name fields (.add left right) result ↔
      ∃ leftResult rightResult,
        MeasureBodyEval signature name fields left leftResult ∧
        MeasureBodyEval signature name fields right rightResult ∧
        result = leftResult + rightResult := by
  constructor
  · intro evaluation; cases evaluation with | add left right => exact ⟨_, _, left, right, rfl⟩
  · rintro ⟨_, _, left, right, rfl⟩; exact .add left right

/-- Measures have unique results on values of their declared datatype. -/
theorem measure_unique
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (types : TypeEnvironment) (environment : Environment)
    (name : String) (declaration : MeasureDecl) (arguments : List Ty) (value : Value)
    (declared : signature.findMeasure name = some declaration)
    (typed : (Ty.data declaration.datatype arguments).denote
      signature model assignment types environment value) :
    ∃ result, MeasureEval signature name value result ∧
      ∀ other, MeasureEval signature name value other → other = result := by
  obtain ⟨result, evaluates⟩ := measure_total signature model assignment validSignature adequate
    types environment name declaration arguments value declared typed
  exact ⟨result, evaluates, fun _ other => other.deterministic evaluates⟩

end SystemFRK
