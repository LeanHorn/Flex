import Flex.VCG.SystemFRK.SemanticTyping

/-! Pattern matching preserves strict descent from the recursive root. -/
namespace SystemFRK

private theorem smallerFold_mem (fields : List (String × Ty)) (domain : Ty)
    (previous : List String) {name : String}
    (member : name ∈ fields.foldl (fun smaller (name, type) =>
      if type.outerBase == domain.outerBase then name :: smaller else smaller) previous) :
    name ∈ previous ∨ ∃ type, (name, type) ∈ fields := by
  induction fields generalizing previous with
  | nil => exact .inl member
  | cons field fields ih =>
    simp only [List.foldl_cons] at member
    rcases ih _ member with member | ⟨type, member⟩
    · split at member
      · rcases List.mem_cons.mp member with same | member
        · exact .inr ⟨field.2, by simp [same]⟩
        · exact .inl member
      · exact .inl member
    · exact .inr ⟨type, List.mem_cons_of_mem _ member⟩

@[simp] theorem markSmaller_vars (context : Context) (scrutinee : String)
    (fields : List (String × Ty)) : (markSmaller context scrutinee fields).vars = context.vars := by
  unfold markSmaller
  split <;> first | rfl | split <;> rfl

@[simp] theorem markSmaller_typeDepth (context : Context) (scrutinee : String)
    (fields : List (String × Ty)) :
    (markSmaller context scrutinee fields).typeDepth = context.typeDepth := by
  unfold markSmaller
  split <;> first | rfl | split <;> rfl

@[simp] theorem markSmaller_recursion (context : Context) (scrutinee : String)
    (fields : List (String × Ty)) :
    (markSmaller context scrutinee fields).recursion = context.recursion := by
  unfold markSmaller
  split <;> first | rfl | split <;> rfl

@[simp] theorem markSmaller_names (context : Context) (scrutinee : String)
    (fields : List (String × Ty)) : (markSmaller context scrutinee fields).names = context.names := by
  simp [Context.names]

private theorem markSmaller_member (context : Context) (scrutinee : String)
    (fields : List (String × Ty)) {scope : RecScope}
    (recursion : context.recursion = some scope) {name : String}
    (member : name ∈ (markSmaller context scrutinee fields).smaller) :
    name ∈ context.smaller ∨
      ((scrutinee = scope.binder ∨ scrutinee ∈ context.smaller) ∧
        ∃ type, (name, type) ∈ fields) := by
  simp only [markSmaller, recursion] at member
  split at member
  · rename_i trigger
    rcases smallerFold_mem fields scope.domain context.smaller member with old | field
    · exact .inl old
    · exact .inr ⟨by simpa using trigger, field⟩
  · exact .inl member

theorem Context.scoped_markSmaller (context : Context) (scrutinee : String)
    (fields : List (String × Ty)) (hasScope : context.Scoped)
    (names : ∀ name type, (name, type) ∈ fields → name ∈ context.names) :
    (markSmaller context scrutinee fields).Scoped := by
  constructor
  · simpa using hasScope.unique
  · simpa using hasScope.sourceNames
  · simpa [Ty.InScope] using hasScope.types
  · simpa [Ty.InScope] using hasScope.recursion
  · intro name member
    rw [markSmaller_names]
    cases recursion : context.recursion with
    | none =>
      simp only [markSmaller, recursion] at member
      exact hasScope.smaller name member
    | some scope =>
      rcases markSmaller_member context scrutinee fields recursion member with old | ⟨_, type, field⟩
      · exact hasScope.smaller name old
      · exact names name type field

theorem Context.realizes_markSmaller (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (context : Context) (assumptions : List Atom)
    (types : TypeEnvironment) (environment : Environment) (frame : RecursionFrame)
    (scrutinee ctor : String) (fields : List (String × Ty)) (values : List Value)
    (realizes : context.Realizes signature model assignment types environment frame assumptions)
    (scrutineeValue : environment.lookup scrutinee = some (.ctor ctor values))
    (fieldValues : ∀ name type, (name, type) ∈ fields →
      ∃ value, environment.lookup name = some value ∧ value ∈ values) :
    (markSmaller context scrutinee fields).Realizes
      signature model assignment types environment frame assumptions := by
  constructor
  · simpa using realizes.typeDepth
  · simpa using realizes.variables
  · exact realizes.assumptions
  · have previous := realizes.recursion
    simp only [FrameRealizes, markSmaller_recursion]
    cases recursion : context.recursion with
    | none => trivial
    | some scope =>
      simp only [FrameRealizes, recursion] at previous
      obtain ⟨function, root, frameEq, rootLookup, rootTyped, smaller, calls⟩ := previous
      refine ⟨function, root, frameEq, rootLookup, rootTyped, ?_, calls⟩
      intro name member
      rcases markSmaller_member context scrutinee fields recursion member with old | ⟨trigger, type, field⟩
      · exact smaller name old
      · obtain ⟨value, found, inValues⟩ := fieldValues name type field
        refine ⟨value, found, ?_⟩
        rcases trigger with equal | oldScrutinee
        · subst scrutinee
          have rootEq := Option.some.inj (rootLookup.symm.trans scrutineeValue)
          rw [rootEq]
          exact .field inValues
        · obtain ⟨value', found', decrease⟩ := smaller scrutinee oldScrutinee
          have equal := Option.some.inj (found'.symm.trans scrutineeValue)
          subst value'
          exact .trans (.field inValues) decrease

end SystemFRK
