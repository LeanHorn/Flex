import Flex.VCG.SystemFRK.SemanticTyping
import Flex.VCG.SystemFRK.Binding.TypeIndices

/-! Term and type context extension preserve static scope and runtime realization. -/
namespace SystemFRK

theorem Context.scoped_add (context next : Context) (name : String) (type : Ty)
    (hasScope : context.Scoped) (typeScope : type.InScope context)
    (added : context.add name type = .ok next) : next.Scoped := by
  obtain ⟨nonempty, reserved, fresh, rfl⟩ := (context.add_eq_ok next name type).mp added
  have weaken (t : Ty) (ht : t.InScope context) :
      t.InScope { context with vars := (name, type) :: context.vars } :=
    ⟨ht.1, fun n hn => by simpa [Context.names] using Or.inr (ht.2 n hn)⟩
  constructor
  · simpa [Context.names] using List.nodup_cons.mpr ⟨fresh, hasScope.unique⟩
  · intro n t ht
    rcases List.mem_cons.mp ht with eq | ht
    · rcases Prod.mk.inj eq with ⟨rfl, rfl⟩; exact ⟨nonempty, reserved⟩
    · exact hasScope.sourceNames n t ht
  · intro n t ht
    rcases List.mem_cons.mp ht with eq | ht
    · rcases Prod.mk.inj eq with ⟨rfl, rfl⟩; exact weaken _ typeScope
    · exact weaken _ (hasScope.types n t ht)
  · intro scope he
    obtain ⟨lookup, domain, codomain, binderFresh⟩ := hasScope.recursion scope he
    have binderMem : scope.binder ∈ context.names := by
      obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp lookup
      simp [Context.names, entries]
    have distinct : (scope.binder == name) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro h
      exact fresh (h ▸ binderMem)
    exact ⟨by simpa [List.lookup_cons, distinct] using lookup,
      weaken _ domain, weaken _ codomain, binderFresh⟩
  · intro n hn
    simpa [Context.names] using Or.inr (hasScope.smaller n hn)

theorem assumptionsScoped_add (context next : Context) (name : String) (type : Ty)
    (assumptions : List Atom) (hasScope : AssumptionsScoped context assumptions)
    (added : context.add name type = .ok next) : AssumptionsScoped next assumptions := by
  obtain ⟨_, _, _, rfl⟩ := (context.add_eq_ok next name type).mp added
  intro atom ha n hn
  simpa [Context.names] using Or.inr (hasScope atom ha n hn)

theorem Context.realizes_add (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (context next : Context) (assumptions : List Atom)
    (types : TypeEnvironment) (environment : Environment) (frame : RecursionFrame)
    (name : String) (type : Ty) (value : Value)
    (hasScope : context.Scoped) (factsScope : AssumptionsScoped context assumptions)
    (typeScope : type.InScope context) (added : context.add name type = .ok next)
    (realizes : context.Realizes signature model assignment types environment frame assumptions)
    (typed : type.denote signature model assignment types environment value) :
    next.Realizes signature model assignment types (environment.bind name value) frame assumptions := by
  obtain ⟨_, _, fresh, rfl⟩ := (context.add_eq_ok next name type).mp added
  have different (n : String) (hn : n ∈ context.names) : (n == name) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    exact fresh (h ▸ hn)
  have lookup (n : String) (hn : n ∈ context.names) :
      (environment.bind name value).lookup n = environment.lookup n := by
    simp [Environment.bind, List.lookup_cons, different n hn]
  have weaken (t : Ty) (ht : t.InScope context) :
      t.denote signature model assignment types (environment.bind name value) =
        t.denote signature model assignment types environment :=
    t.environment_congr signature model assignment types _ _ (fun n hn => lookup n (ht.2 n hn))
  constructor
  · exact realizes.typeDepth
  · intro n t ht
    rcases List.mem_cons.mp ht with eq | ht
    · rcases Prod.mk.inj eq with ⟨rfl, rfl⟩
      exact ⟨value, by simp [Environment.bind], by rwa [weaken t typeScope]⟩
    · obtain ⟨v, found, hv⟩ := realizes.variables n t ht
      exact ⟨v, (lookup n (by exact List.mem_map.mpr ⟨(n,t),ht,rfl⟩)).trans found,
        by rwa [weaken t (hasScope.types n t ht)]⟩
  · intro atom ha
    apply (atom.environment_congr signature assignment _ environment
      (fun n hn => lookup n (factsScope atom ha n hn))).mpr
    exact realizes.assumptions atom ha
  · have previous := realizes.recursion
    cases he : context.recursion with
    | none => simp [FrameRealizes]
    | some scope =>
      obtain ⟨_, domain, codomain, _⟩ := hasScope.recursion scope he
      have binderMem : scope.binder ∈ context.names := by
        obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp (hasScope.recursion scope he).1
        simp [Context.names, entries]
      simp only [FrameRealizes, he] at previous ⊢
      obtain ⟨function, root, frameEq, rootLookup, rootTyped, smaller, calls⟩ := previous
      refine ⟨function, root, frameEq, (lookup _ binderMem).trans rootLookup,
        ?_, ?_, ?_⟩
      · rwa [weaken _ domain]
      · intro n hn
        obtain ⟨v, found, decrease⟩ := smaller n hn
        exact ⟨v, (lookup n (hasScope.smaller n hn)).trans found, decrease⟩
      · intro argument decrease argTyped
        rw [weaken _ domain] at argTyped
        obtain ⟨result, application, resultTyped⟩ := calls argument decrease argTyped
        refine ⟨result, application, ?_⟩
        rw [scope.codomain.environment_congr signature model assignment types
          ((environment.bind name value).bind scope.binder argument)
          (environment.bind scope.binder argument) (by
            intro n hn
            by_cases same : n = scope.binder
            · subst n; simp [Environment.bind]
            · have h : (n == scope.binder) = false := beq_eq_false_iff_ne.mpr same
              simpa [Environment.bind, List.lookup_cons, h] using lookup n (codomain.2 n hn))]
        exact resultTyped

theorem Context.scoped_underType (context : Context) (hasScope : context.Scoped) :
    context.underType.Scoped := by
  have names : context.underType.names = context.names := by
    simp [Context.names, Context.underType, List.map_map, Function.comp_def]
  have shift (type : Ty) (inScope : type.InScope context) :
      (Ty.shiftTypes 1 0 type).InScope context.underType := by
    refine ⟨Ty.shiftTypes_scoped type context.typeDepth 1 0 inScope.1, ?_⟩
    simpa [names] using inScope.2
  constructor
  · simpa [names] using hasScope.unique
  · intro name type member
    change (name, type) ∈ context.vars.map (fun (x, t) => (x, Ty.shiftTypes 1 0 t)) at member
    obtain ⟨⟨oldName, oldType⟩, memberOld, equal⟩ := List.mem_map.mp member
    cases equal
    exact hasScope.sourceNames _ _ memberOld
  · intro name type member
    change (name, type) ∈ context.vars.map (fun (x, t) => (x, Ty.shiftTypes 1 0 t)) at member
    obtain ⟨⟨oldName, oldType⟩, memberOld, equal⟩ := List.mem_map.mp member
    cases equal
    exact shift oldType (hasScope.types _ _ memberOld)
  · intro scope equal
    change context.recursion.map _ = some scope at equal
    cases original : context.recursion with
    | none => simp [original] at equal
    | some oldScope =>
      simp only [original, Option.map_some, Option.some.injEq] at equal
      subst scope
      obtain ⟨lookup, domain, codomain, fresh⟩ := hasScope.recursion oldScope original
      refine ⟨?_, shift _ domain, shift _ codomain, ?_⟩
      · change (context.vars.map (fun (x, t) => (x, Ty.shiftTypes 1 0 t))).lookup oldScope.binder = _
        generalize entries : context.vars = variables at lookup ⊢
        clear entries
        induction variables with
        | nil => simp at lookup
        | cons entry rest ih =>
          rcases entry with ⟨name, type⟩
          simp only [List.map_cons, List.lookup_cons] at lookup ⊢
          split at lookup
          · simp_all
          · simp_all
      · simpa using fresh
  · intro name member
    rw [names]
    exact hasScope.smaller name member

theorem assumptionsScoped_underType (context : Context) (assumptions : List Atom)
    (hasScope : AssumptionsScoped context assumptions) :
    AssumptionsScoped context.underType assumptions := by
  simpa [AssumptionsScoped, Context.names, Context.underType, List.map_map,
    Function.comp_def] using hasScope

/-- Type extension shifts stored types and the recursion summary; runtime values stay fixed. -/
theorem Context.realizes_underType (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (context : Context) (assumptions : List Atom)
    (types : TypeEnvironment) (environment : Environment) (frame : RecursionFrame)
    (candidate : Candidate)
    (realizes : context.Realizes signature model assignment types environment frame assumptions) :
    context.underType.Realizes signature model assignment (candidate :: types)
      environment frame assumptions := by
  have shift (type : Ty) (value : Value) :
      (Ty.shiftTypes 1 0 type).denote signature model assignment (candidate :: types)
          environment value ↔ type.denote signature model assignment types environment value := by
    change (Ty.shiftTypes [candidate].length 0 type).denote signature model assignment
        ([candidate] ++ types) environment value ↔ _
    rw [Ty.shiftTypes_denote]
  constructor
  · simpa [Context.underType] using congrArg Nat.succ realizes.typeDepth
  · intro name type member
    change (name, type) ∈ context.vars.map (fun (x, t) => (x, Ty.shiftTypes 1 0 t)) at member
    obtain ⟨⟨oldName, oldType⟩, memberOld, equal⟩ := List.mem_map.mp member
    cases equal
    obtain ⟨value, lookup, typed⟩ := realizes.variables _ oldType memberOld
    exact ⟨value, lookup, (shift oldType value).mpr typed⟩
  · exact realizes.assumptions
  · have previous := realizes.recursion
    cases sourceFrame : context.recursion with
    | none => simp [FrameRealizes, Context.underType, sourceFrame]
    | some scope =>
      simp only [FrameRealizes, sourceFrame] at previous
      obtain ⟨function, root, frameEqual, rootLookup, rootTyped, smaller, calls⟩ := previous
      simp only [FrameRealizes, Context.underType, sourceFrame, Option.map_some]
      refine ⟨function, root, frameEqual, rootLookup, (shift _ _).mpr rootTyped, smaller, ?_⟩
      intro argument decrease typed
      obtain ⟨result, application, resultTyped⟩ := calls argument decrease ((shift _ _).mp typed)
      refine ⟨result, application, ?_⟩
      change (Ty.shiftTypes [candidate].length 0 scope.codomain).denote signature model assignment
        ([candidate] ++ types) (environment.bind scope.binder argument) result
      rwa [Ty.shiftTypes_denote]

end SystemFRK
