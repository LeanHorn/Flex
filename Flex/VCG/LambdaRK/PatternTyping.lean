import Flex.VCG.LambdaRK.DatatypeTyping
import Flex.VCG.LambdaRK.BranchRecursion
import Flex.VCG.LambdaRK.SignatureLemmas

/-! Pattern elimination preserves typing, branch facts, and structural descent. -/
namespace LambdaRK

private theorem paired_named_fields {signature : Signature} {model : DataModel}
    {assignment : KAssignment} {types : TypeEnvironment} {environment : Environment}
    (arguments : List Ty) {fieldTypes : List Ty} {values : List Value}
    (typed : All₂ (fun type value => (Ty.instantiateParams arguments type).denote
      signature model assignment types environment value) fieldTypes values)
    (names : List String) (lengths : names.length = fieldTypes.length) :
    All₂ (fun field value => field.2.denote signature model assignment types environment value)
      (names.zip (fieldTypes.map (Ty.instantiateParams arguments))) values := by
  induction typed generalizing names with
  | nil => cases names <;> simp_all; exact .nil
  | cons head tail ih =>
    cases names with
    | nil => simp at lengths
    | cons name names => exact .cons head (ih names (by simpa using lengths))

theorem semTyped_match
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    (valid : signature.validate = .ok ()) (adequate : DatatypeAdequate signature model assignment)
    {context : Context} {assumptions : List Atom} {scrutinee name : String} {arguments : List Ty}
    {data : DataDecl} {branches : List (String × List String × Expr)} {result : Ty}
    (resultScope : result.InScope context)
    (argumentsScope : ∀ argument ∈ arguments, argument.InScope context)
    (typed : HasType signature model assignment context assumptions (.var scrutinee) (.data name arguments))
    (scrutineeTyped : SemTyped signature model assignment context assumptions (.var scrutinee) (.data name arguments))
    (declared : signature.findData name = some data)
    (coverage : ∀ constructor ∈ data.ctors, constructor.name ∈ branches.map Prod.fst)
    (branchesTyped : SemBranches signature model assignment context assumptions scrutinee data arguments branches result) :
    SemTyped signature model assignment context assumptions (.matchE (.var scrutinee) branches) result := by
  intro scope facts types environment frame realizes
  obtain ⟨value, evaluated, valueTyped⟩ := scrutineeTyped scope facts types environment frame realizes
  obtain ⟨declaration, constructor, values, declarationFound, arity, ctorMember, valueEqual, fieldsTyped⟩ :=
    (adequate types environment name arguments value).mp valueTyped
  have declarationEqual := Option.some.inj (declared.symm.trans declarationFound)
  subst declaration
  subst value
  have scrutineeLookup : environment.lookup scrutinee = some (.ctor constructor.name values) := by
    cases evaluated with
    | var lookup => exact lookup
  have scrutineeMember : scrutinee ∈ context.names :=
    typed.observation_scoped (.var scrutinee) rfl scrutinee (by simp [LTerm.freeVars])
  obtain ⟨names, body, branchFound⟩ := findBranch_exists branches constructor.name (coverage constructor ctorMember)
  have branchMember := List.mem_of_find?_eq_some branchFound
  obtain ⟨branchConstructor, next, branchCtorMember, ctorEqual, namesLength, added, bodyTyped⟩ :=
    branchesTyped constructor.name names body branchMember
  have sameConstructor := signature.ctor_eq_of_name_eq valid
    (List.mem_of_find?_eq_some declared) branchCtorMember ctorMember ctorEqual
  subst branchConstructor
  let fields := names.zip (constructor.fields.map (Ty.instantiateParams arguments))
  have fieldNames : fields.map Prod.fst = names :=
    List.map_fst_zip (by simpa using Nat.le_of_eq namesLength)
  have fieldsFormed (n : String) (type : Ty) (member : (n,type) ∈ fields) : type.InScope context := by
    have inMap := List.of_mem_zip member |>.2
    obtain ⟨field, originalMember, rfl⟩ := List.mem_map.mp inMap
    exact signature.fields_formed valid declared ctorMember arity.symm argumentsScope originalMember
  have paired := paired_named_fields arguments fieldsTyped names namesLength
  have fieldLengths : fields.length = values.length := paired.length_eq
  have nextScope := extendFields_scoped context next fields scope fieldsFormed added
  have nextFacts := extendFields_assumptionsScoped context next fields assumptions facts added
  have nextRealizes := extendFields_realizes signature model assignment context next fields assumptions
    types environment frame values scope facts fieldsFormed added realizes paired
  have agrees := extendFields_bindMany_agrees context next fields scope fieldsFormed added environment values fieldLengths
  have observations := extendFields_values_observed signature context next fields scope fieldsFormed added
    environment values fieldLengths
  rw [fieldNames] at nextRealizes agrees observations
  have nextScrutinee : (environment.bindMany names values).lookup scrutinee = some (.ctor constructor.name values) :=
    (agrees scrutinee scrutineeMember).trans scrutineeLookup
  have fieldMembers (n : String) (type : Ty) (member : (n,type) ∈ fields) : n ∈ next.names := by
    rw [extendFields_shape context next fields added]
    simp only [Context.names, List.map_append, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨(n,type), by simpa using member, rfl⟩)
  have markedScope := next.scoped_markSmaller scrutinee fields nextScope fieldMembers
  have markedRealizes := Context.realizes_markSmaller signature model assignment next assumptions types
    (environment.bindMany names values) frame scrutinee constructor.name fields values nextRealizes nextScrutinee
    (fun n type member => observations.variables_member (by rw [← fieldNames]; exact List.mem_map.mpr ⟨(n,type),member,rfl⟩))
  let equation : Atom := .theory (.eq (.var scrutinee) (.ctor constructor.name (names.map LTerm.var)))
  have equationHolds : equation.denote signature assignment (environment.bindMany names values) :=
    ⟨.ctor constructor.name values, .var nextScrutinee, .ctor observations⟩
  have equationScope : ∀ n ∈ equation.freeVars, n ∈ (markSmaller next scrutinee fields).names := by
    intro n member
    simp only [equation, Atom.freeVars, Formula.freeVars, LTerm.freeVars, List.mem_append,
      List.mem_singleton, List.mem_flatMap, List.mem_map] at member
    rw [markSmaller_names]
    rcases member with same | ⟨term, ⟨fieldName, nameMember, termEqual⟩, free⟩
    · subst n
      rw [extendFields_shape context next fields added]
      simpa [Context.names] using Or.inr scrutineeMember
    · subst term
      simp only [LTerm.freeVars, List.mem_singleton] at free
      subst n
      rw [← fieldNames] at nameMember
      obtain ⟨⟨n,type⟩, member, equal⟩ := List.mem_map.mp nameMember
      exact equal ▸ fieldMembers n type member
  have branchFacts : AssumptionsScoped (markSmaller next scrutinee fields) (equation :: assumptions) := by
    intro atom member n free
    rcases List.mem_cons.mp member with rfl | member
    · exact equationScope n free
    · simpa using nextFacts atom member n free
  have branchRealizes : (markSmaller next scrutinee fields).Realizes signature model assignment types
      (environment.bindMany names values) frame (equation :: assumptions) := by
    constructor
    · exact markedRealizes.typeDepth
    · exact markedRealizes.variables
    · intro atom member
      rcases List.mem_cons.mp member with rfl | member
      · exact equationHolds
      · exact markedRealizes.assumptions atom member
    · exact markedRealizes.recursion
  obtain ⟨output, bodyEvaluation, outputTyped⟩ := bodyTyped markedScope branchFacts types
    (environment.bindMany names values) frame branchRealizes
  refine ⟨output, .matchE evaluated branchFound (namesLength.trans fieldsTyped.length_eq) bodyEvaluation, ?_⟩
  rw [result.environment_congr signature model assignment types (environment.bindMany names values) environment
    (fun n free => agrees n (resultScope.2 n free))] at outputTyped
  exact outputTyped

end LambdaRK
