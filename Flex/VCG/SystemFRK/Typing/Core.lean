import Flex.VCG.SystemFRK.Binding.Substitution
import Flex.VCG.SystemFRK.Typing.Context

/-! System F cases of the logical relation. -/

namespace SystemFRK

/-- ANF observations agree with source evaluation. -/
theorem observed_evaluation
    {signature : Signature} {environment : Environment} {frame : RecursionFrame}
    {expression : Expr} {observed : LTerm} {value : Value}
    (observation : observe expression = .ok observed)
    (evaluates : Eval signature environment frame expression value) :
    LogicalEval signature environment observed value := by
  cases expression <;> simp only [observe, Except.ok.injEq] at observation
  all_goals try contradiction
  case var name =>
    subst observed
    cases evaluates with
    | var lookup => exact .var lookup
  case int n => subst observed; cases evaluates; exact .int
  case bool b => subst observed; cases evaluates; exact .bool

theorem semTyped_var
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {name : String} {type : Ty}
    (lookup : context.vars.lookup name = some type) :
    SemTyped signature model assignment context assumptions (.var name) (selfType name type) := by
  intro hasScope _ types environment frame realizes
  obtain ⟨value, lookupValue, valueTyped⟩ := realizes.lookup lookup
  have member : (name, type) ∈ context.vars := by
    obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp lookup
    simp [entries]
  have fresh := hasScope.witness_fresh member
  refine ⟨value, .var lookupValue, ?_⟩
  simp only [selfType, Ty.denote, Atom.denote, Formula.denote]
  refine ⟨valueTyped, value, .var ?_, .var ?_⟩
  · simp [Environment.bind]
  · simpa only [Environment.bind, List.lookup_cons,
      beq_eq_false_iff_ne.mpr fresh] using lookupValue

theorem semTyped_int
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} (n : Int) :
    SemTyped signature model assignment context assumptions (.int n)
      (.refine .int (.theory (.eq (.var valueName) (.int n)))) := by
  intro _ _ types environment frame _
  refine ⟨.int n, .int, ?_⟩
  simp only [Ty.denote, LSort.contains, Atom.denote, Formula.denote]
  refine ⟨⟨n, rfl⟩, .int n, .var ?_, .int⟩
  simp [Environment.bind]

theorem semTyped_bool
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} (b : Bool) :
    SemTyped signature model assignment context assumptions (.bool b)
      (.refine .bool (.theory (.eq (.var valueName) (.bool b)))) := by
  intro _ _ types environment frame _
  refine ⟨.bool b, .bool, ?_⟩
  simp only [Ty.denote, LSort.contains, Atom.denote, Formula.denote]
  refine ⟨⟨b, rfl⟩, .bool b, .var ?_, .bool⟩
  simp [Environment.bind]

theorem semTyped_app
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom}
    {fn arg : Expr} {name : String} {domain codomain : Ty} {observed : LTerm}
    (function : SemTyped signature model assignment context assumptions fn
      (.arrow name domain codomain))
    (argument : SemTyped signature model assignment context assumptions arg domain)
    (observation : observe arg = .ok observed)
    (witnessFresh : valueName ∉ observed.freeVars) :
    SemTyped signature model assignment context assumptions (.app fn arg)
      (Ty.substTerm name observed codomain) := by
  intro hasScope facts types environment frame realizes
  obtain ⟨functionValue, functionEval, functionTyped⟩ :=
    function hasScope facts types environment frame realizes
  obtain ⟨argumentValue, argumentEval, argumentTyped⟩ :=
    argument hasScope facts types environment frame realizes
  simp only [Ty.denote] at functionTyped
  obtain ⟨result, applies, resultTyped⟩ := functionTyped argumentValue argumentTyped
  refine ⟨result, .app functionEval argumentEval applies, ?_⟩
  rwa [codomain.substTerm_denote signature model assignment types environment name observed
    argumentValue witnessFresh (observed_evaluation observation argumentEval)]

theorem semTyped_tyApp
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {fn : Expr} {argument body : Ty}
    (function : SemTyped signature model assignment context assumptions fn (.all body)) :
    SemTyped signature model assignment context assumptions (.tyApp fn argument)
      (Ty.substType argument 0 body) := by
  intro hasScope facts types environment frame realizes
  obtain ⟨functionValue, functionEval, functionTyped⟩ :=
    function hasScope facts types environment frame realizes
  simp only [Ty.denote] at functionTyped
  obtain ⟨result, applies, resultTyped⟩ :=
    functionTyped (argument.denote signature model assignment types environment)
  refine ⟨result, .tyApp functionEval applies, ?_⟩
  rwa [body.substType_denote]

theorem semTyped_ann
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {expression : Expr} {type : Ty}
    (typed : SemTyped signature model assignment context assumptions expression type) :
    SemTyped signature model assignment context assumptions (.ann expression type) type := by
  intro hasScope facts types environment frame realizes
  obtain ⟨value, evaluates, denotes⟩ := typed hasScope facts types environment frame realizes
  exact ⟨value, .ann evaluates, denotes⟩

theorem semTyped_subsumption
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {expression : Expr} {source target : Ty}
    (typed : SemTyped signature model assignment context assumptions expression source)
    (subtyping : Subtype signature model assignment context assumptions source target) :
    SemTyped signature model assignment context assumptions expression target := by
  intro hasScope facts types environment frame realizes
  obtain ⟨value, evaluates, denotes⟩ := typed hasScope facts types environment frame realizes
  exact ⟨value, evaluates, subtyping types environment realizes.typeDepth
    realizes.variables realizes.assumptions value denotes⟩

theorem semTyped_lam
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context next : Context} {assumptions : List Atom}
    {name : String} {domain codomain : Ty} {body : Expr}
    (formed : wfTy signature context 512 domain = .ok ())
    (added : context.add name domain = .ok next)
    (bodyTyped : SemTyped signature model assignment next assumptions body codomain) :
    SemTyped signature model assignment context assumptions (.lam name domain body)
      (.arrow name domain codomain) := by
  intro hasScope facts types environment frame realizes
  have domainScope := wfTy_inScope signature context domain 512 formed
  refine ⟨.closure name body environment frame, .lam, ?_⟩
  simp only [Ty.denote]
  intro argument argumentTyped
  obtain ⟨result, evaluates, typed⟩ := bodyTyped (Context.scoped_add _ _ _ _ hasScope domainScope added)
    (assumptionsScoped_add _ _ _ _ _ facts added) types (environment.bind name argument) frame
    (Context.realizes_add signature model assignment context next assumptions types environment frame
      name domain argument hasScope facts domainScope added realizes argumentTyped)
  exact ⟨result, .closure evaluates, typed⟩

theorem semTyped_tyLam
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {body : Expr} {type : Ty}
    (bodyTyped : SemTyped signature model assignment context.underType assumptions body type) :
    SemTyped signature model assignment context assumptions (.tyLam body) (.all type) := by
  intro hasScope facts types environment frame realizes
  refine ⟨.typeClosure body environment frame, .tyLam, ?_⟩
  simp only [Ty.denote]
  intro candidate
  obtain ⟨result, evaluates, typed⟩ := bodyTyped
    (Context.scoped_underType _ hasScope) (assumptionsScoped_underType _ _ facts)
    (candidate :: types) environment frame
    (Context.realizes_underType signature model assignment context assumptions types environment frame
      candidate realizes)
  exact ⟨result, .closure evaluates, typed⟩

theorem semTyped_let
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context next : Context} {assumptions : List Atom}
    {name : String} {rhs body : Expr} {type result : Ty}
    (rhsTyped : SemTyped signature model assignment context assumptions rhs type)
    (typeScope : type.InScope context)
    (added : context.add name type = .ok next)
    (fresh : name ∉ result.freeVars)
    (bodyTyped : SemTyped signature model assignment next assumptions body result) :
    SemTyped signature model assignment context assumptions (.letE name rhs body) result := by
  intro hasScope facts types environment frame realizes
  obtain ⟨value, rhsEval, valueTyped⟩ := rhsTyped hasScope facts types environment frame realizes
  obtain ⟨resultValue, bodyEval, bodyDenote⟩ := bodyTyped (Context.scoped_add _ _ _ _ hasScope typeScope added)
    (assumptionsScoped_add _ _ _ _ _ facts added) types (environment.bind name value) frame
    (Context.realizes_add signature model assignment context next assumptions types environment frame
      name type value hasScope facts typeScope added realizes valueTyped)
  refine ⟨resultValue, .letE rhsEval bodyEval, ?_⟩
  rw [← result.environment_congr signature model assignment types
    (environment.bind name value) environment ?_]
  · exact bodyDenote
  · intro freeName member
    have distinct : freeName ≠ name := fun equal => fresh (equal ▸ member)
    simp only [Environment.bind, List.lookup_cons, beq_eq_false_iff_ne.mpr distinct]

end SystemFRK
