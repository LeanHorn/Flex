import Flex.VCG.SystemFRK.VCGen
import Flex.VCG.SystemFRK.Binding.Substitution
import Flex.VCG.SystemFRK.Semantics.Measures

/-! Logical interfaces for the constraint generator. -/
namespace SystemFRK

@[simp] theorem Cstr.andThen_denote (left right : Cstr) :
    (left.andThen right).denote signature assignment environment ↔
      left.denote signature assignment environment ∧ right.denote signature assignment environment := by
  cases left <;> cases right <;> simp [Cstr.andThen, Cstr.denote]

theorem guardPredicates_denote (predicates : List Atom) (body : Cstr) :
    (guardPredicates predicates body).denote signature assignment environment ↔
      (∀ p ∈ predicates, p.denote signature assignment environment) →
        body.denote signature assignment environment := by
  induction predicates with
  | nil => simp [guardPredicates]
  | cons p ps ih =>
    change (p.denote signature assignment environment →
      (guardPredicates ps body).denote signature assignment environment) ↔ _
    rw [ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨fun h ⟨a,b⟩ => h a b, fun h a b => h ⟨a,b⟩⟩

theorem Cstr.heads_denote (atoms : List Atom) :
    ((atoms.map Cstr.head).foldr Cstr.andThen .truth).denote signature assignment environment ↔
      ∀ p ∈ atoms, p.denote signature assignment environment := by
  induction atoms with
  | nil => simp [Cstr.denote]
  | cons p ps ih => simp [Cstr.andThen_denote, Cstr.denote, ih]

theorem Ty.denote_outer (type : Ty) :
    type.denote signature model assignment types environment value ↔
      type.outerBase.denote signature model assignment types environment value ∧
      ∀ p ∈ type.outerPredicates,
        p.denote signature assignment (environment.bind valueName value) := by
  induction type using Ty.rec
      (motive_2 := fun _ => True) with
  | refine base predicate ih =>
    simp only [Ty.denote, Ty.outerBase, Ty.outerPredicates, ih, List.mem_append,
      List.mem_singleton, and_assoc]
    grind
  | _ => simp [Ty.outerBase, Ty.outerPredicates]

theorem Ty.denote_sort (type : Ty)
    (typed : type.denote signature model assignment types environment value) :
    type.sort.contains value := by
  induction type using Ty.rec (motive_2 := fun _ => True) with
  | int | bool => simpa only [Ty.denote, Ty.sort] using typed
  | refine base p ih =>
    simp only [Ty.denote] at typed
    exact ih typed.1
  | _ => trivial

theorem Cstr.environment_congr (constraint : Cstr)
    (signature : Signature) (assignment : KAssignment) (left right : Environment)
    (agree : ∀ name, left.lookup name = right.lookup name) :
    constraint.denote signature assignment left ↔ constraint.denote signature assignment right := by
  induction constraint generalizing left right with
  | truth => rfl
  | head atom => exact atom.environment_congr signature assignment left right (fun n _ => agree n)
  | guard atom body ih =>
    exact imp_congr (atom.environment_congr signature assignment left right (fun n _ => agree n))
      (ih left right agree)
  | conj a b ia ib => exact and_congr (ia left right agree) (ib left right agree)
  | all name sort body ih =>
    apply forall_congr'; intro value
    apply imp_congr_right; intro _
    apply ih
    intro n
    by_cases h : n = name
    · subst n; simp [Environment.bind]
    · simp [Environment.bind, List.lookup_cons, show (n == name) = false from by simpa using h, agree]

/-- Constraint validity relative to typed slots and the current branch facts. -/
def Entails (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (context : Context) (assumptions : List Atom) (constraint : Cstr) : Prop :=
  ∀ types environment, types.length = context.typeDepth →
    environment.Satisfies signature model assignment types context.vars →
    AssumptionsHold signature assignment environment assumptions →
    constraint.denote signature assignment environment

theorem Entails.andThen (left right : Cstr) :
    Entails signature model assignment context assumptions (left.andThen right) ↔
      Entails signature model assignment context assumptions left ∧
      Entails signature model assignment context assumptions right := by
  simp only [Entails, Cstr.andThen_denote]
  exact ⟨fun h => ⟨fun t e d v a => (h t e d v a).1, fun t e d v a => (h t e d v a).2⟩,
    fun ⟨l,r⟩ t e d v a => ⟨l t e d v a, r t e d v a⟩⟩

theorem Entails.of_valid (valid : constraint.Valid signature assignment) :
    Entails signature model assignment context assumptions constraint := by
  intro _ environment _ _ _
  exact valid environment

/-- Only actual datatype inhabitants supply the measure-definedness guards. -/
theorem typeFacts_hold
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (typed : type.denote signature model assignment types environment value)
    (observed : LogicalEval signature observationEnvironment term value) :
    ∀ atom ∈ typeFacts signature type term,
      atom.denote signature assignment observationEnvironment := by
  unfold typeFacts
  cases base : type.outerBase <;> simp only [List.not_mem_nil, false_implies, forall_const]
  case data family arguments =>
    intro atom member
    obtain ⟨measure, _, member⟩ := List.mem_flatMap.mp member
    cases declared : signature.findMeasure measure.name with
    | none => simp [declared] at member
    | some declaration =>
      simp only [declared] at member
      split at member
      · rename_i familyEq
        have familyEq : declaration.datatype = family := by simpa using familyEq
        have dataTyped := (type.denote_outer.mp typed).1
        rw [base] at dataTyped
        obtain ⟨n, evaluated⟩ := measure_total signature model assignment validSignature adequate
          types environment measure.name declaration arguments value declared
          (by simpa only [familyEq] using dataTyped)
        obtain rfl := List.mem_singleton.mp member
        exact ⟨.int n, .measure observed evaluated, .measure observed evaluated⟩
      · simp at member

/-- Use the existing runtime slot to interpret a bound constraint in the extended context. -/
theorem Entails.bind
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (added : context.add name type = .ok next)
    (valid : Entails signature model assignment context assumptions (bindConstraint signature name type body)) :
    Entails signature model assignment next assumptions body := by
  obtain ⟨_, _, _, rfl⟩ := (context.add_eq_ok next name type).mp added
  intro types environment depth variables assumptionsHold
  obtain ⟨value, lookup, typed⟩ := variables name type (by simp)
  have outer := valid types environment depth
    (fun n t ht => variables n t (List.mem_cons_of_mem _ ht)) assumptionsHold
  have withFacts := outer value (type.denote_sort typed)
  have witnessed := (guardPredicates_denote _ _).mp withFacts
    (typeFacts_hold validSignature adequate typed (.var (by simp [Environment.bind])))
  apply (body.environment_congr signature assignment (environment.bind name value) environment ?_).mp
  · apply (guardPredicates_denote _ _).mp witnessed
    intro p hp
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp hp
    apply (atom_substitution signature assignment (environment.bind name value)
      valueName (.var name) original value (.var (by simp [Environment.bind]))).mpr
    apply (original.environment_congr signature assignment
      (environment.bind valueName value) ((environment.bind name value).bind valueName value) ?_).mp
    · exact (type.denote_outer.mp typed).2 original originalMember
    · intro n _
      by_cases hn : n = valueName
      · subst n; simp [Environment.bind]
      · by_cases hn' : n = name
        · subst n; simp [Environment.bind, List.lookup_cons, show (name == valueName) = false from by simpa using hn, lookup]
        · simp [Environment.bind, List.lookup_cons,
            show (n == valueName) = false from by simpa using hn,
            show (n == name) = false from by simpa using hn']
  · intro n
    by_cases h : n = name
    · subst n; simpa [Environment.bind] using lookup.symm
    · simp [Environment.bind, List.lookup_cons, show (n == name) = false from by simpa using h]

/-- Type abstraction changes only semantic type candidates; Horn constraints
are independent of those candidates. -/
theorem Entails.underType
    (valid : Entails signature model assignment context assumptions body) :
    Entails signature model assignment context.underType assumptions body := by
  intro types environment depth variables facts
  cases types with
  | nil => simp [Context.underType] at depth
  | cons candidate rest =>
    have previous : environment.Satisfies signature model assignment rest context.vars := by
      intro n t ht
      obtain ⟨v, lookup, typed⟩ := variables n (t.shiftTypes 1 0)
        (List.mem_map.mpr ⟨(n,t),ht,rfl⟩)
      refine ⟨v, lookup, ?_⟩
      have eqn : (t.shiftTypes 1 0).denote signature model assignment (candidate :: rest) environment =
          t.denote signature model assignment rest environment :=
        Ty.shiftTypes_denote signature model assignment rest [candidate] environment t
      rwa [eqn] at typed
    exact valid rest environment (by simpa [Context.underType] using depth) previous facts

theorem Entails.guard
    (valid : Entails signature model assignment context assumptions (.guard atom body)) :
    Entails signature model assignment context (atom :: assumptions) body := by
  intro types environment depth variables facts
  exact valid types environment depth variables
    (fun a ha => facts a (List.mem_cons_of_mem atom ha)) (facts atom (by simp))

/-- Pattern-field quantifiers expose the constraint in the context obtained by
performing the same sequence of checked context extensions. -/
theorem Entails.bindFields
    (validSignature : signature.validate = .ok ())
    (adequate : DatatypeAdequate signature model assignment)
    (added : extendFields context fields = .ok next)
    (valid : Entails signature model assignment context assumptions (bindFields signature fields body)) :
    Entails signature model assignment next assumptions body := by
  induction fields generalizing context with
  | nil =>
    simp only [extendFields, List.foldlM_nil, Except.pure, pure, Except.ok.injEq] at added
    subst next
    exact valid
  | cons field fields ih =>
    obtain ⟨name, type⟩ := field
    change Except.bind (context.add name type) (fun middle => extendFields middle fields) = .ok next at added
    cases addResult : context.add name type with
    | error message =>
      simp [addResult, Except.bind] at added
    | ok middle =>
      apply ih (context := middle)
      · simpa only [addResult, Except.bind] using added
      · exact Entails.bind validSignature adequate addResult valid

/-- Recursion annotations do not change what a Horn constraint means. -/
theorem Entails.context_congr
    (depth : left.typeDepth = right.typeDepth) (variables : left.vars = right.vars) :
    Entails signature model assignment left assumptions constraint ↔
      Entails signature model assignment right assumptions constraint := by
  simp only [Entails, depth, variables]

theorem Entails.markSmaller
    (valid : Entails signature model assignment context assumptions constraint) :
    Entails signature model assignment (SystemFRK.markSmaller context scrutinee fields) assumptions constraint := by
  apply (Entails.context_congr (left := context) ?_ ?_).mp valid
  all_goals unfold SystemFRK.markSmaller; split <;> first | rfl | split <;> rfl

end SystemFRK
