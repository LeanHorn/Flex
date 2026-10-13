import Flex.VCG.SystemFRK.Typing.Context

/-! Context and environment transport for pattern fields. -/
namespace SystemFRK

theorem extendFields_shape (context next : Context) (fields : List (String × Ty))
    (added : extendFields context fields = .ok next) :
    next = { context with vars := fields.reverse ++ context.vars } := by
  induction fields generalizing context with
  | nil => simpa [extendFields, pure, Except.pure] using added.symm
  | cons field fields ih =>
    rcases field with ⟨name, type⟩
    simp only [extendFields, List.foldlM_cons] at added
    cases first : context.add name type with
    | error message => simp [first, bind, Except.bind] at added
    | ok intermediate =>
      simp only [first, bind, Except.bind] at added
      have rest := ih intermediate added
      obtain ⟨_, _, _, rfl⟩ := (context.add_eq_ok intermediate name type).mp first
      simpa [List.reverse_cons, List.append_assoc] using rest

theorem extendFields_scoped (context next : Context) (fields : List (String × Ty))
    (scope : context.Scoped) (formed : ∀ name type, (name, type) ∈ fields → type.InScope context)
    (added : extendFields context fields = .ok next) : next.Scoped := by
  induction fields generalizing context with
  | nil => have equal : context = next := by simpa [extendFields, pure, Except.pure] using added
           exact equal ▸ scope
  | cons field fields ih =>
    rcases field with ⟨name, type⟩
    simp only [extendFields, List.foldlM_cons] at added
    cases first : context.add name type with
    | error message => simp [first, bind, Except.bind] at added
    | ok intermediate =>
      simp only [first, bind, Except.bind] at added
      apply ih intermediate (context.scoped_add intermediate name type scope
        (formed name type (by simp)) first) ?_ added
      obtain ⟨_, _, _, rfl⟩ := (context.add_eq_ok intermediate name type).mp first
      intro n t member
      obtain ⟨indices, names⟩ := formed n t (by simp [member])
      exact ⟨indices, fun x hx => by simpa [Context.names] using Or.inr (names x hx)⟩

theorem lookup_of_mem_unique {α : Type} (entries : List (String × α))
    (unique : (entries.map Prod.fst).Nodup) {name : String} {value : α}
    (member : (name, value) ∈ entries) : entries.lookup name = some value := by
  induction entries with
  | nil => simp at member
  | cons entry rest ih =>
    rcases entry with ⟨n, v⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    rcases List.mem_cons.mp member with same | tailMember
    · cases same; simp
    · have distinct : name ≠ n := by
        intro eq; subst n
        exact unique.1 (List.mem_map.mpr ⟨(name,value),tailMember,rfl⟩)
      simpa [List.lookup_cons, beq_eq_false_iff_ne.mpr distinct] using ih unique.2 tailMember

theorem lookup_preserved_by_fresh_front {α : Type} (front : List (String × α))
    (environment : List (String × α)) (name : String)
    (fresh : name ∉ front.map Prod.fst) :
    (front ++ environment).lookup name = environment.lookup name := by
  have absent : front.lookup name = none := by
    rw [List.lookup_eq_none_iff]
    intro entry member
    apply bne_iff_ne.mpr
    intro eq
    exact fresh (List.mem_map.mpr ⟨entry, member, eq.symm⟩)
  simp [List.lookup_append, absent]

theorem All₂.length_eq {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (paired : All₂ relation left right) :
    left.length = right.length := by
  induction paired with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem All₂.named_member {relation : Ty → Value → Prop}
    {fields : List (String × Ty)} {values : List Value}
    (paired : All₂ (fun field value => relation field.2 value) fields values)
    {name : String} {type : Ty} (member : (name, type) ∈ fields) :
    ∃ value, (name, value) ∈ (fields.map Prod.fst).zip values ∧ relation type value := by
  induction paired with
  | nil => simp at member
  | @cons field fields value values typed paired ih =>
    rcases List.mem_cons.mp member with same | tailMember
    · cases same
      exact ⟨value, by simp, typed⟩
    · obtain ⟨v, found, typed⟩ := ih tailMember
      exact ⟨v, by simp [found], typed⟩

theorem extendFields_assumptionsScoped (context next : Context)
    (fields : List (String × Ty)) (assumptions : List Atom)
    (facts : AssumptionsScoped context assumptions)
    (added : extendFields context fields = .ok next) : AssumptionsScoped next assumptions := by
  rw [extendFields_shape context next fields added]
  intro atom member name free
  simp only [Context.names, List.map_append, List.mem_append]
  exact Or.inr (facts atom member name free)

/-- Pattern fields use source order at runtime and reverse order in the static
context; fresh names make the two lookup orders agree. -/
theorem extendFields_realizes (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (context next : Context) (fields : List (String × Ty))
    (assumptions : List Atom) (types : TypeEnvironment) (environment : Environment)
    (frame : RecursionFrame) (values : List Value)
    (scope : context.Scoped) (facts : AssumptionsScoped context assumptions)
    (formed : ∀ name type, (name, type) ∈ fields → type.InScope context)
    (added : extendFields context fields = .ok next)
    (realizes : context.Realizes signature model assignment types environment frame assumptions)
    (typed : All₂ (fun field value => field.2.denote signature model assignment types environment value)
      fields values) :
    next.Realizes signature model assignment types
      (environment.bindMany (fields.map Prod.fst) values) frame assumptions := by
  have nextScope := extendFields_scoped context next fields scope formed added
  have shape := extendFields_shape context next fields added
  have unique : ((fields.map Prod.fst).reverse ++ context.names).Nodup := by
    simpa [shape, Context.names, List.map_reverse] using nextScope.unique
  have separate := List.nodup_append.mp unique
  let entries := (fields.map Prod.fst).zip values
  have entryNames : entries.map Prod.fst = fields.map Prod.fst := by
    exact List.map_fst_zip (by simpa using Nat.le_of_eq typed.length_eq)
  have entryUnique : (entries.map Prod.fst).Nodup := by
    rw [entryNames]
    simpa [List.Nodup, List.pairwise_reverse, ne_comm] using separate.1
  have agree (name : String) (member : name ∈ context.names) :
      (environment.bindMany (fields.map Prod.fst) values).lookup name = environment.lookup name := by
    apply lookup_preserved_by_fresh_front
    rw [entryNames]
    intro inFields
    exact separate.2.2 name (by simpa using inFields) name member rfl
  have transport (type : Ty) (typeScope : type.InScope context) :
      type.denote signature model assignment types
          (environment.bindMany (fields.map Prod.fst) values) =
        type.denote signature model assignment types environment :=
    type.environment_congr signature model assignment types _ _ (fun name hn => agree name (typeScope.2 name hn))
  subst next
  constructor
  · exact realizes.typeDepth
  · intro name type member
    rcases List.mem_append.mp member with newField | oldField
    · have inFields : (name, type) ∈ fields := by simpa using newField
      obtain ⟨value, inEntries, valueTyped⟩ := typed.named_member inFields
      refine ⟨value, ?_, ?_⟩
      · change (entries ++ environment).lookup name = some value
        simp [List.lookup_append, lookup_of_mem_unique entries entryUnique inEntries]
      · rwa [transport type (formed name type inFields)]
    · obtain ⟨value, found, valueTyped⟩ := realizes.variables name type oldField
      exact ⟨value, (agree name (List.mem_map.mpr ⟨(name,type),oldField,rfl⟩)).trans found,
        by rwa [transport type (scope.types name type oldField)]⟩
  · intro atom member
    exact (atom.environment_congr signature assignment _ environment
      (fun name free => agree name (facts atom member name free))).mpr (realizes.assumptions atom member)
  · have previous := realizes.recursion
    cases recursion : context.recursion with
    | none => simp [FrameRealizes]
    | some recScope =>
      obtain ⟨binderFound, domainScope, codomainScope, _⟩ := scope.recursion recScope recursion
      have binderMember : recScope.binder ∈ context.names := by
        obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp binderFound
        simp [Context.names, entries]
      simp only [FrameRealizes, recursion] at previous ⊢
      obtain ⟨function, root, frameEqual, rootLookup, rootTyped, smaller, calls⟩ := previous
      refine ⟨function, root, frameEqual, (agree _ binderMember).trans rootLookup,
        ?_, ?_, ?_⟩
      · rwa [transport _ domainScope]
      · intro name member
        obtain ⟨value, found, decrease⟩ := smaller name member
        exact ⟨value, (agree name (scope.smaller name member)).trans found, decrease⟩
      · intro argument decrease argumentTyped
        rw [transport _ domainScope] at argumentTyped
        obtain ⟨result, application, resultTyped⟩ := calls argument decrease argumentTyped
        refine ⟨result, application, ?_⟩
        rw [recScope.codomain.environment_congr signature model assignment types
          ((environment.bindMany (fields.map Prod.fst) values).bind recScope.binder argument)
          (environment.bind recScope.binder argument) (by
            intro name free
            by_cases same : name = recScope.binder
            · subst name; simp [Environment.bind]
            · simpa [Environment.bind, List.lookup_cons, beq_eq_false_iff_ne.mpr same] using
                agree name (codomainScope.2 name free))]
        exact resultTyped

theorem extendFields_bindMany_agrees (context next : Context) (fields : List (String × Ty))
    (scope : context.Scoped) (formed : ∀ name type, (name, type) ∈ fields → type.InScope context)
    (added : extendFields context fields = .ok next)
    (environment : Environment) (values : List Value) (lengths : fields.length = values.length) :
    ∀ name ∈ context.names,
      (environment.bindMany (fields.map Prod.fst) values).lookup name = environment.lookup name := by
  have nextScope := extendFields_scoped context next fields scope formed added
  have unique : ((fields.map Prod.fst).reverse ++ context.names).Nodup := by
    simpa [extendFields_shape context next fields added, Context.names, List.map_reverse] using nextScope.unique
  intro name member
  apply lookup_preserved_by_fresh_front
  rw [List.map_fst_zip (by simpa using Nat.le_of_eq lengths)]
  intro inFields
  exact (List.nodup_append.mp unique).2.2 name (by simpa using inFields) name member rfl

theorem LogicalListEval.variables_of_lookup (signature : Signature) (environment : Environment)
    (names : List String) (values : List Value) (lengths : names.length = values.length)
    (lookup : ∀ name value, (name,value) ∈ names.zip values → environment.lookup name = some value) :
    LogicalListEval signature environment (names.map LTerm.var) values := by
  induction names generalizing values with
  | nil => cases values <;> simp_all; exact .nil
  | cons name names ih =>
    cases values with
    | nil => simp at lengths
    | cons value values =>
      exact .cons (.var (lookup name value (by simp)))
        (ih values (by simpa using lengths) (fun n v member => lookup n v (by simp [member])))

theorem extendFields_values_observed (signature : Signature) (context next : Context)
    (fields : List (String × Ty)) (scope : context.Scoped)
    (formed : ∀ name type, (name, type) ∈ fields → type.InScope context)
    (added : extendFields context fields = .ok next)
    (environment : Environment) (values : List Value) (lengths : fields.length = values.length) :
    LogicalListEval signature (environment.bindMany (fields.map Prod.fst) values)
      ((fields.map Prod.fst).map LTerm.var) values := by
  have nextScope := extendFields_scoped context next fields scope formed added
  have unique : ((fields.map Prod.fst).reverse ++ context.names).Nodup := by
    simpa [extendFields_shape context next fields added, Context.names, List.map_reverse] using nextScope.unique
  have fieldsUnique : (fields.map Prod.fst).Nodup :=
    by simpa [List.Nodup, List.pairwise_reverse, ne_comm] using (List.nodup_append.mp unique).1
  apply LogicalListEval.variables_of_lookup signature _ _ values (by simpa using lengths)
  intro name value member
  change (((fields.map Prod.fst).zip values) ++ environment).lookup name = some value
  rw [List.lookup_append, lookup_of_mem_unique _ ?_ member]
  · rfl
  · rwa [List.map_fst_zip (by simpa using Nat.le_of_eq lengths)]

theorem LogicalListEval.variables_member {signature : Signature} {environment : Environment}
    {names : List String} {values : List Value}
    (evaluates : LogicalListEval signature environment (names.map LTerm.var) values)
    {name : String} (member : name ∈ names) :
    ∃ value, environment.lookup name = some value ∧ value ∈ values := by
  induction names generalizing values with
  | nil => simp at member
  | cons head names ih =>
    cases evaluates with
    | cons evaluated tail =>
      rcases List.mem_cons.mp member with equal | member
      · subst name
        cases evaluated with
        | var lookup => exact ⟨_, lookup, by simp⟩
      · obtain ⟨value, lookup, inValues⟩ := ih tail member
        exact ⟨value, lookup, by simp [inValues]⟩

end SystemFRK
