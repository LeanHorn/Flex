import Flex.VCG.LambdaRK.SemanticTyping
import Flex.VCG.LambdaRK.EnvironmentLemmas

/-! Fresh context extension preserves static scope and runtime realization. -/
namespace LambdaRK

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

end LambdaRK
