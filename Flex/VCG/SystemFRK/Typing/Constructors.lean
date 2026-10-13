import Flex.VCG.SystemFRK.Typing.BranchContext
import Flex.VCG.SystemFRK.Datatypes.Adequacy
import Flex.VCG.SystemFRK.Typing.Core

/-! Constructor and pattern-match cases of the logical relation. -/
namespace SystemFRK

theorem HasType.observation_scoped
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {expression : Expr} {type : Ty}
    (typed : HasType signature model assignment context assumptions expression type) :
    ∀ observed, observe expression = .ok observed →
      ∀ name ∈ observed.freeVars, name ∈ context.names := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True) with
  | var lookup =>
    intro observed observation name member
    simp only [observe, Except.ok.injEq] at observation
    subst observed
    simp only [LTerm.freeVars, List.mem_singleton] at member
    subst name
    obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp lookup
    simp [Context.names, entries]
  | int | bool =>
    intro observed observation name member
    simp only [observe, Except.ok.injEq] at observation
    subst observed
    simp [LTerm.freeVars] at member
  | subsumption _ _ ih => exact ih
  | ctor | matchE | structRec | recur | measure | lam | app | tyLam | tyApp | letE | ann =>
    intro observed observation
    simp [observe] at observation
  | _ => intros; trivial

def SemTypes (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (context : Context) (assumptions : List Atom) (expressions : List Expr) (fieldTypes : List Ty) : Prop :=
  context.Scoped → AssumptionsScoped context assumptions →
    ∀ types environment frame,
      context.Realizes signature model assignment types environment frame assumptions →
      ∃ values, EvalList signature environment frame expressions values ∧
        All₂ (fun type value => type.denote signature model assignment types environment value)
          fieldTypes values

theorem semTypes_nil {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} :
    SemTypes signature model assignment context assumptions [] [] := by
  intro scope facts types environment frame realizes
  exact ⟨[], .nil, .nil⟩

theorem semTypes_cons {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {expression : Expr} {expressions : List Expr}
    {type : Ty} {fieldTypes : List Ty}
    (head : SemTyped signature model assignment context assumptions expression type)
    (tail : SemTypes signature model assignment context assumptions expressions fieldTypes) :
    SemTypes signature model assignment context assumptions (expression :: expressions) (type :: fieldTypes) := by
  intro scope facts types environment frame realizes
  obtain ⟨value, evaluation, typed⟩ := head scope facts types environment frame realizes
  obtain ⟨values, evaluations, typings⟩ := tail scope facts types environment frame realizes
  exact ⟨value :: values, .cons evaluation evaluations, .cons typed typings⟩

theorem Signature.findCtor_members (signature : Signature) {name : String}
    {data : DataDecl} {ctor : CtorDecl} (found : signature.findCtor name = some (data, ctor)) :
    data ∈ signature.datatypes ∧ ctor ∈ data.ctors ∧ ctor.name = name := by
  obtain ⟨d, member, found⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨c, ctorMember, found⟩ := List.exists_of_findSome?_eq_some found
  split at found
  · simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨member, ctorMember, by simpa using ‹(c.name == name) = true›⟩
  · contradiction

theorem HasTypes.observed_evaluation
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {expressions : List Expr} {fieldTypes : List Ty}
    (typed : HasTypes signature model assignment context assumptions expressions fieldTypes)
    (scope : context.Scoped)
    {environment : Environment} {frame : RecursionFrame} {observed : List LTerm} {values : List Value}
    (observations : expressions.mapM observe = .ok observed)
    (evaluations : EvalList signature environment frame expressions values) (witness : Value) :
    LogicalListEval signature (environment.bind valueName witness) observed values := by
  induction expressions generalizing fieldTypes observed values with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at observations
    subst observed
    cases evaluations
    exact .nil
  | cons expression expressions ih =>
    cases typed with
    | cons head tail =>
      cases evaluations with
      | cons evaluated evaluatedTail =>
        cases observation : observe expression with
        | error message => simp [List.mapM_cons, observation, bind, Except.bind] at observations
        | ok term =>
          cases tailObservation : expressions.mapM observe with
          | error message => simp [List.mapM_cons, observation, tailObservation, bind, Except.bind] at observations
          | ok terms =>
            simp only [List.mapM_cons, observation, tailObservation, bind, Except.bind, pure, Except.pure,
              Except.ok.injEq] at observations
            subst observed
            refine .cons ?_ (ih tail tailObservation evaluatedTail)
            apply (LogicalEval.environment_congr signature environment (environment.bind valueName witness) term _ ?_).mp
            · exact SystemFRK.observed_evaluation observation evaluated
            · intro name member
              have inContext := head.observation_scoped term observation name member
              obtain ⟨⟨n,t⟩, entry, equal⟩ := List.mem_map.mp inContext
              have fresh : name ≠ valueName := by simpa only [← equal] using scope.witness_fresh entry
              simp [Environment.bind, List.lookup_cons, beq_eq_false_iff_ne.mpr fresh]

theorem semTyped_ctor
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    (valid : signature.validate = .ok ()) (adequate : DatatypeAdequate signature model assignment)
    {context : Context} {assumptions : List Atom} {name : String} {arguments : List Ty}
    {fields : List Expr} {data : DataDecl} {constructor : CtorDecl} {observed : List LTerm}
    (found : signature.findCtor name = some (data, constructor))
    (arity : arguments.length = data.params)
    (typed : HasTypes signature model assignment context assumptions fields
      (constructor.fields.map (Ty.instantiateParams arguments)))
    (semantics : SemTypes signature model assignment context assumptions fields
      (constructor.fields.map (Ty.instantiateParams arguments)))
    (observations : fields.mapM observe = .ok observed) :
    SemTyped signature model assignment context assumptions (.ctor name arguments fields)
      (.refine (.data data.name arguments) (.theory (.eq (.var valueName) (.ctor name observed)))) := by
  intro scope facts types environment frame realizes
  obtain ⟨values, evaluations, typedValues⟩ := semantics scope facts types environment frame realizes
  obtain ⟨dataMember, ctorMember, nameEqual⟩ := signature.findCtor_members found
  have unique := (Signature.modelReadyFrom_names [] signature.datatypes (signature.validate_modelReady 256 valid)).1
  have declared := (signature.findData_eq_some_iff unique data.name data).mpr ⟨dataMember, rfl⟩
  refine ⟨.ctor name values, .ctor evaluations, ?_⟩
  simp only [Ty.denote, Atom.denote, Formula.denote]
  constructor
  · have dataTyped : (Ty.data data.name arguments).denote signature model assignment types environment (.ctor name values) := by
      apply (adequate types environment data.name arguments (.ctor name values)).mpr
      refine ⟨data, constructor, values, declared, arity.symm, ctorMember, ?_, ?_⟩
      · rw [nameEqual]
      · clear evaluations
        generalize equation : constructor.fields = fieldTypes at typedValues ⊢
        clear equation
        induction fieldTypes generalizing values with
        | nil => cases typedValues; exact .nil
        | cons field fields ih =>
          cases typedValues with
          | cons head tail => exact .cons head (ih _ tail)
    simpa only [Ty.denote] using dataTyped
  · refine ⟨.ctor name values, .var ?_, .ctor (typed.observed_evaluation scope observations evaluations _)⟩
    simp [Environment.bind]

/-- Branch induction hypotheses retain their checked contexts. -/
def SemBranches (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (context : Context) (assumptions : List Atom) (scrutinee : String) (data : DataDecl)
    (arguments : List Ty) (branches : List (String × List String × Expr)) (result : Ty) : Prop :=
  ∀ name names body, (name, names, body) ∈ branches →
    ∃ constructor next,
      constructor ∈ data.ctors ∧ constructor.name = name ∧
      names.length = constructor.fields.length ∧
      extendFields context (names.zip (constructor.fields.map (Ty.instantiateParams arguments))) = .ok next ∧
      SemTyped signature model assignment
        (markSmaller next scrutinee (names.zip (constructor.fields.map (Ty.instantiateParams arguments))))
        (.theory (.eq (.var scrutinee) (.ctor name (names.map LTerm.var))) :: assumptions)
        body result

theorem semBranches_nil {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {scrutinee : String} {data : DataDecl}
    {arguments : List Ty} {result : Ty} :
    SemBranches signature model assignment context assumptions scrutinee data arguments [] result := by
  intro name names body member
  simp at member

theorem semBranches_cons {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context next : Context} {assumptions : List Atom} {scrutinee : String} {data : DataDecl}
    {arguments : List Ty} {result : Ty} {name : String} {names : List String} {body : Expr}
    {branches : List (String × List String × Expr)} {constructor : CtorDecl}
    (member : constructor ∈ data.ctors) (sameName : constructor.name = name)
    (lengths : names.length = constructor.fields.length)
    (added : extendFields context (names.zip (constructor.fields.map (Ty.instantiateParams arguments))) = .ok next)
    (head : SemTyped signature model assignment
      (markSmaller next scrutinee (names.zip (constructor.fields.map (Ty.instantiateParams arguments))))
      (.theory (.eq (.var scrutinee) (.ctor name (names.map LTerm.var))) :: assumptions) body result)
    (tail : SemBranches signature model assignment context assumptions scrutinee data arguments branches result) :
    SemBranches signature model assignment context assumptions scrutinee data arguments
      ((name, names, body) :: branches) result := by
  intro n ns b inBranches
  rcases List.mem_cons.mp inBranches with equal | inTail
  · cases equal
    exact ⟨constructor, next, member, sameName, lengths, added, head⟩
  · exact tail n ns b inTail

theorem findBranch_exists (branches : List (String × List String × Expr)) (name : String)
    (member : name ∈ branches.map Prod.fst) :
    ∃ names body, findBranch branches name = some (name, names, body) := by
  induction branches with
  | nil => simp at member
  | cons branch branches ih =>
    rcases branch with ⟨n, names, body⟩
    by_cases equal : n = name
    · subst n
      exact ⟨names, body, by simp [findBranch]⟩
    · have tail : name ∈ branches.map Prod.fst := by simpa [Ne.symm equal] using member
      obtain ⟨ns, b, found⟩ := ih tail
      exact ⟨ns, b, by simpa [findBranch, beq_eq_false_iff_ne.mpr equal] using found⟩

end SystemFRK
