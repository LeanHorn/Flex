import Flex.VCG.SystemFRK.Typing.Patterns
import Flex.VCG.SystemFRK.Semantics.Measures
import Flex.VCG.SystemFRK.Typing.Recursion

/-! The fundamental theorem for all declarative typing rules. -/
namespace SystemFRK

theorem semTyped_measure
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    (valid : signature.validate = .ok ()) (adequate : DatatypeAdequate signature model assignment)
    {context : Context} {assumptions : List Atom} {name data : String} {arguments : List Ty}
    {declaration : MeasureDecl} {argument : Expr} {observed : LTerm}
    (declared : signature.findMeasure name = some declaration) (family : declaration.datatype = data)
    (typed : HasType signature model assignment context assumptions argument (.data data arguments))
    (semantics : SemTyped signature model assignment context assumptions argument (.data data arguments))
    (observation : observe argument = .ok observed) :
    SemTyped signature model assignment context assumptions (.measure name argument)
      (.refine .int (.theory (.eq (.var valueName) (.measure name observed)))) := by
  intro scope facts types environment frame realizes
  obtain ⟨value, evaluated, valueTyped⟩ := semantics scope facts types environment frame realizes
  obtain ⟨result, measureEvaluation⟩ := measure_total signature model assignment valid adequate types environment
    name declaration arguments value declared (by simpa only [family] using valueTyped)
  have observed : LogicalEval signature (environment.bind valueName (.int result)) observed value := by
    apply (LogicalEval.environment_congr signature environment _ observed value ?_).mp
    · exact observed_evaluation observation evaluated
    · intro n free
      have inContext := typed.observation_scoped _ observation n free
      obtain ⟨⟨entryName, type⟩, member, equal⟩ := List.mem_map.mp inContext
      have fresh : n ≠ valueName := by simpa only [← equal] using scope.witness_fresh member
      simp [Environment.bind, List.lookup_cons, beq_eq_false_iff_ne.mpr fresh]
  refine ⟨.int result, .measure evaluated measureEvaluation, ?_⟩
  simp only [Ty.denote, Atom.denote, Formula.denote, LSort.contains]
  exact ⟨⟨result, rfl⟩, .int result, .var (by simp [Environment.bind]), .measure observed measureEvaluation⟩

/-- Every declaratively typed expression terminates in every realized context,
including open polymorphic contexts and strict-subvalue recursive frames. -/
theorem fundamental_open
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (valid : signature.validate = .ok ()) (adequate : DatatypeAdequate signature model assignment)
    (context : Context) (assumptions : List Atom) (expression : Expr) (type : Ty)
    (typed : HasType signature model assignment context assumptions expression type) :
    SemTyped signature model assignment context assumptions expression type := by
  induction typed using HasType.rec
    (motive_2 := fun context assumptions expressions types _ =>
      SemTypes signature model assignment context assumptions expressions types)
    (motive_3 := fun context assumptions scrutinee data arguments branches result _ =>
      SemBranches signature model assignment context assumptions scrutinee data arguments branches result) with
  | var lookup => exact semTyped_var lookup
  | int => exact semTyped_int _
  | bool => exact semTyped_bool _
  | lam formed added _ ih => exact semTyped_lam formed added ih
  | app _ _ observation fresh ihFn ihArg => exact semTyped_app ihFn ihArg observation fresh
  | tyLam _ ih => exact semTyped_tyLam ih
  | tyApp _ _ ih => exact semTyped_tyApp ih
  | letE _ typeScope added fresh _ ihRhs ihBody => exact semTyped_let ihRhs typeScope added fresh ihBody
  | ctor found arity _ typed observations ih => exact semTyped_ctor valid adequate found arity typed ih observations
  | matchE resultScope argumentsScope typed declared _ _ coverage _ ihScrutinee ihBranches =>
    exact semTyped_match valid adequate resultScope argumentsScope typed ihScrutinee declared coverage ihBranches
  | structRec domainFormed _ added codomainFormed _ ih =>
    exact semTyped_structRec domainFormed added codomainFormed ih
  | recur recursion smaller _ ih => exact semTyped_recur recursion smaller ih
  | measure declared family typed observation ih => exact semTyped_measure valid adequate declared family typed ih observation
  | ann _ _ ih => exact semTyped_ann ih
  | subsumption _ subtyping ih => exact semTyped_subsumption ih subtyping
  | nil => exact semTypes_nil
  | cons _ _ ihHead ihTail => exact semTypes_cons ihHead ihTail
  | _ =>
    intros
    first
    | exact semBranches_nil
    | apply semBranches_cons <;> assumption

theorem fundamental_closed
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (valid : signature.validate = .ok ()) (adequate : DatatypeAdequate signature model assignment)
    (expression : Expr) (type : Ty)
    (typed : HasType signature model assignment {} [] expression type) :
    ∃ value, Eval signature [] none expression value ∧
      type.denote signature model assignment [] [] value :=
  SemTyped.closed (fundamental_open signature model assignment valid adequate {} [] expression type typed)

end SystemFRK
