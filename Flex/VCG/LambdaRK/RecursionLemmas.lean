import Flex.VCG.LambdaRK.ContextLemmas
import Flex.VCG.LambdaRK.StructuralOrder

/-! Semantic structural recursion. The recursive function is justified by
well-founded induction on constructor subvalues. Installing its frame replaces
the enclosing recursive frame; closures created by the body retain this frame.
No substitution theorem or draft admission is used in this module. -/
namespace LambdaRK

theorem Context.scoped_recursiveBody
    {context next : Context} {name : String} {domain codomain : Ty}
    (hasScope : context.Scoped) (domainScope : domain.InScope context)
    (added : context.add name domain = .ok next)
    (codomainScope : codomain.InScope next) :
    ({ next with recursion := some { binder := name, domain, codomain }, smaller := [] } : Context).Scoped := by
  have nextScope := context.scoped_add next name domain hasScope domainScope added
  obtain ⟨_, _, fresh, rfl⟩ := (context.add_eq_ok next name domain).mp added
  constructor
  · exact nextScope.unique
  · exact nextScope.sourceNames
  · exact nextScope.types
  · intro scope same
    cases Option.some.inj same
    refine ⟨by simp, ?_, codomainScope, ?_⟩
    · exact nextScope.types name domain (by simp)
    · exact fun member => fresh (domainScope.2 name member)
  · simp

/-- The body receives only the induction hypotheses for strict subvalues of
the current root. The postcondition is evaluated at the smaller argument, not
at the root, even for dependent summaries. -/
theorem Context.realizes_recursiveBody
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context next : Context} {assumptions : List Atom}
    {types : TypeEnvironment} {environment : Environment} {outerFrame : RecursionFrame}
    {name : String} {domain codomain : Ty} {function root : Value}
    (hasScope : context.Scoped) (factsScope : AssumptionsScoped context assumptions)
    (domainScope : domain.InScope context)
    (added : context.add name domain = .ok next)
    (realizes : context.Realizes signature model assignment types environment outerFrame assumptions)
    (rootTyped : domain.denote signature model assignment types environment root)
    (calls : ∀ argument, Smaller argument root →
      domain.denote signature model assignment types environment argument →
      ∃ result, Apply signature function argument result ∧
        codomain.denote signature model assignment types (environment.bind name argument) result) :
    ({ next with recursion := some { binder := name, domain, codomain }, smaller := [] } : Context).Realizes
      signature model assignment types (environment.bind name root) (some function)
        assumptions := by
  have nextRealizes := context.realizes_add signature model assignment next assumptions types
    environment outerFrame name domain root hasScope factsScope domainScope added realizes rootTyped
  have fresh := ((context.add_eq_ok next name domain).mp added).2.2.1
  have domainAgree : domain.denote signature model assignment types (environment.bind name root) =
      domain.denote signature model assignment types environment :=
    domain.environment_congr signature model assignment types _ _ (by
      intro n member
      have different : n ≠ name := fun equal => fresh (equal ▸ domainScope.2 n member)
      simp [Environment.bind, List.lookup_cons, beq_eq_false_iff_ne.mpr different])
  refine ⟨nextRealizes.typeDepth, nextRealizes.variables, nextRealizes.assumptions, ?_⟩
  change ∃ f r, some function = some f ∧ _
  refine ⟨function, root, rfl, by simp [Environment.bind], ?_, by simp, ?_⟩
  · rwa [domainAgree]
  · intro argument decrease argumentTyped
    rw [domainAgree] at argumentTyped
    obtain ⟨result, applies, resultTyped⟩ := calls argument decrease argumentTyped
    refine ⟨result, applies, ?_⟩
    rw [codomain.environment_congr signature model assignment types
      ((environment.bind name root).bind name argument) (environment.bind name argument) (by
        intro n _
        simp only [Environment.bind, List.lookup_cons]
        split <;> simp_all)]
    exact resultTyped

/-- Semantic introduction rule. A body theorem handles arbitrary stored
closures and type closures through `SemTyped`; the induction below never
assumes correctness of the current recursive call. -/
theorem semTyped_structRec_of_scope
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context next : Context} {assumptions : List Atom}
    {name : String} {domain codomain : Ty} {body : Expr}
    (domainScope : domain.InScope context)
    (added : context.add name domain = .ok next)
    (codomainScope : codomain.InScope next)
    (bodyTyped : SemTyped signature model assignment
      { next with recursion := some { binder := name, domain, codomain }, smaller := [] }
      assumptions body codomain) :
    SemTyped signature model assignment context assumptions (.structRec name domain codomain body)
      (.arrow name domain codomain) := by
  intro hasScope facts types environment outerFrame realizes
  refine ⟨.recursiveClosure name body environment, .structRec, ?_⟩
  simp only [Ty.denote]
  apply Apply.recursiveClosure_total signature environment name body
    (domain.denote signature model assignment types environment)
    (fun argument result =>
      codomain.denote signature model assignment types (environment.bind name argument) result)
  intro argument argumentTyped calls
  exact bodyTyped (Context.scoped_recursiveBody hasScope domainScope added codomainScope)
    (assumptionsScoped_add context next name domain assumptions facts added)
    types (environment.bind name argument) (some (.recursiveClosure name body environment))
    (Context.realizes_recursiveBody hasScope facts domainScope added realizes argumentTyped calls)

/-- Recursive elimination before substitution. Evaluation reads the lexical
frame supplied by the body, so the same rule applies under captured closures. -/
theorem recursive_call_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {types : TypeEnvironment} {environment : Environment}
    {frame : RecursionFrame} {scope : RecScope} {name : String}
    (scopeEqual : context.recursion = some scope)
    (smaller : name ∈ context.smaller)
    (frameTyped : FrameRealizes signature model assignment types environment frame context)
    (argument : ∃ value, Eval signature environment frame (.var name) value ∧
      scope.domain.denote signature model assignment types environment value) :
    ∃ argument result, LogicalEval signature environment (.var name) argument ∧
      Eval signature environment frame (.recur (.var name)) result ∧
      scope.codomain.denote signature model assignment types
        (environment.bind scope.binder argument) result := by
  simp only [FrameRealizes, scopeEqual] at frameTyped
  obtain ⟨function, root, frameEqual, _, _, decreases, calls⟩ := frameTyped
  obtain ⟨value, evaluates, typed⟩ := argument
  cases evaluates with
  | var lookup =>
    obtain ⟨smallValue, smallLookup, decrease⟩ := decreases name smaller
    have equal : smallValue = value := Option.some.inj (smallLookup.symm.trans lookup)
    subst smallValue
    obtain ⟨result, applies, resultTyped⟩ := calls value decrease typed
    exact ⟨value, result, .var lookup, .recur frameEqual (.var lookup) applies, resultTyped⟩

end LambdaRK
