import Flex.VCG.LambdaRK.SemanticTyping
import Flex.VCG.LambdaRK.DraftBinding
import Flex.VCG.LambdaRK.ContextLemmas

/-!
# Context transport obligations

These proved structural formation and weakening interfaces serve the open
fundamental theorem. They use the completed binding and environment-transport
lemmas and have no admitted dependencies.
-/

namespace LambdaRK.Draft

theorem wfTy_inScope (signature : Signature) (context : Context) (type : Ty)
    (fuel : Nat) (_hasScope : context.Scoped)
    (formed : wfTy signature context fuel type = .ok ()) : type.InScope context := by
  exact LambdaRK.wfTy_inScope signature context type fuel formed

theorem scoped_add (context next : Context) (name : String) (type : Ty)
    (hasScope : context.Scoped) (typeScope : type.InScope context)
    (added : context.add name type = .ok next) : next.Scoped := by
  exact context.scoped_add next name type hasScope typeScope added

theorem assumptionsScoped_add (context next : Context) (name : String) (type : Ty)
    (assumptions : List Atom) (hasScope : AssumptionsScoped context assumptions)
    (added : context.add name type = .ok next) : AssumptionsScoped next assumptions := by
  exact LambdaRK.assumptionsScoped_add context next name type assumptions hasScope added

/-- Extending an environment preserves the recursive-call induction hypothesis
only because the new source name is fresh for the old context and summary. -/
theorem realizes_add (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (context next : Context) (assumptions : List Atom)
    (types : TypeEnvironment) (environment : Environment) (frame : RecursionFrame)
    (name : String) (type : Ty) (value : Value)
    (hasScope : context.Scoped) (factsScope : AssumptionsScoped context assumptions)
    (typeScope : type.InScope context) (added : context.add name type = .ok next)
    (realizes : context.Realizes signature model assignment types environment frame assumptions)
    (typed : type.denote signature model assignment types environment value) :
    next.Realizes signature model assignment types (environment.bind name value) frame assumptions := by
  exact context.realizes_add signature model assignment next assumptions types environment frame
    name type value hasScope factsScope typeScope added realizes typed

theorem scoped_underType (context : Context) (hasScope : context.Scoped) :
    context.underType.Scoped := by
  have names : context.underType.names = context.names := by
    simp [Context.names, Context.underType, List.map_map, Function.comp_def]
  have shift (type : Ty) (inScope : type.InScope context) :
      (Ty.shiftTypes 1 0 type).InScope context.underType := by
    refine ⟨shiftTypes_scoped type context.typeDepth 1 0 inScope.1, ?_⟩
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

/-- Adding an arbitrary semantic candidate shifts every stored type, including
the recursive summary; the runtime environment and closure frame stay fixed. -/
theorem realizes_underType (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (context : Context) (assumptions : List Atom)
    (types : TypeEnvironment) (environment : Environment) (frame : RecursionFrame)
    (candidate : Candidate)
    (realizes : context.Realizes signature model assignment types environment frame assumptions) :
    context.underType.Realizes signature model assignment (candidate :: types)
      environment frame assumptions := by
  have shift (type : Ty) (value : Value) :
      (Ty.shiftTypes 1 0 type).denote signature model assignment (candidate :: types)
          environment value ↔ type.denote signature model assignment types environment value := by
    exact type_shift_denote signature model assignment types [candidate] environment type value
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
      exact (type_shift_denote signature model assignment types [candidate]
        (environment.bind scope.binder argument) scope.codomain result).mpr resultTyped

end LambdaRK.Draft
