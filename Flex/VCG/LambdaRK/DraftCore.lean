import Flex.VCG.LambdaRK.DraftBinding
import Flex.VCG.LambdaRK.Judgments
import Flex.VCG.LambdaRK.SemanticTyping
import Flex.VCG.LambdaRK.DraftContext

/-!
# Fundamental theorem: the System F core cases

These proofs construct actual evaluations using the completed binding and
context transport theorems. The core theorem has no admitted dependencies.
Constructor/match and measure cases are developed separately; structural
recursion is proved in `DraftRecursion`.
-/

namespace LambdaRK.Draft

/-- ANF observations denote exactly the value computed by the observed source
expression. This bridge needs no substitution assumptions. -/
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

theorem variable_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {types : TypeEnvironment} {environment : Environment} {frame : RecursionFrame}
    {name : String} {type : Ty} {value : Value}
    (lookup : environment.lookup name = some value)
    (typed : type.denote signature model assignment types environment value)
    (fresh : name ≠ valueName) :
    ∃ result, Eval signature environment frame (.var name) result ∧
      (selfType name type).denote signature model assignment types environment result := by
  refine ⟨value, .var lookup, ?_⟩
  simp only [selfType, Ty.denote, Atom.denote, Formula.denote]
  refine ⟨typed, value, .var ?_, .var ?_⟩
  · simp [Environment.bind]
  · simpa only [Environment.bind, List.lookup_cons,
      show (name == valueName) = false from beq_eq_false_iff_ne.mpr fresh] using lookup

theorem integer_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {types : TypeEnvironment} {environment : Environment} {frame : RecursionFrame}
    (n : Int) :
    ∃ result, Eval signature environment frame (.int n) result ∧
      (Ty.refine .int (.theory (.eq (.var valueName) (.int n)))).denote
        signature model assignment types environment result := by
  refine ⟨.int n, .int, ?_⟩
  simp only [Ty.denote, LSort.contains, Atom.denote, Formula.denote]
  refine ⟨⟨n, rfl⟩, .int n, .var ?_, .int⟩
  simp [Environment.bind]

theorem boolean_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {types : TypeEnvironment} {environment : Environment} {frame : RecursionFrame}
    (b : Bool) :
    ∃ result, Eval signature environment frame (.bool b) result ∧
      (Ty.refine .bool (.theory (.eq (.var valueName) (.bool b)))).denote
        signature model assignment types environment result := by
  refine ⟨.bool b, .bool, ?_⟩
  simp only [Ty.denote, LSort.contains, Atom.denote, Formula.denote]
  refine ⟨⟨b, rfl⟩, .bool b, .var ?_, .bool⟩
  simp [Environment.bind]

/-- Function introduction establishes termination for every argument in the
domain; its closure remembers the lexical environment and recursion frame. -/
theorem lambda_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {types : TypeEnvironment} {environment : Environment} {frame : RecursionFrame}
    {name : String} {domain codomain : Ty} {body : Expr}
    (bodyTyped : ∀ argument,
      domain.denote signature model assignment types environment argument →
      ∃ result, Eval signature (environment.bind name argument) frame body result ∧
        codomain.denote signature model assignment types
          (environment.bind name argument) result) :
    ∃ value, Eval signature environment frame (.lam name domain body) value ∧
      (Ty.arrow name domain codomain).denote
        signature model assignment types environment value := by
  refine ⟨.closure name body environment frame, .lam, ?_⟩
  simp only [Ty.denote]
  intro argument argumentTyped
  obtain ⟨result, evaluates, typed⟩ := bodyTyped argument argumentTyped
  exact ⟨result, .closure evaluates, typed⟩

/-- Type abstraction suspends evaluation; every semantic type candidate may
then instantiate its body, including candidates interpreting universal types. -/
theorem type_lambda_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {types : TypeEnvironment} {environment : Environment} {frame : RecursionFrame}
    {body : Expr} {type : Ty}
    (bodyTyped : ∀ candidate : Candidate,
      ∃ result, Eval signature environment frame body result ∧
        type.denote signature model assignment (candidate :: types) environment result) :
    ∃ value, Eval signature environment frame (.tyLam body) value ∧
      (Ty.all type).denote signature model assignment types environment value := by
  refine ⟨.typeClosure body environment frame, .tyLam, ?_⟩
  simp only [Ty.denote]
  intro candidate
  obtain ⟨result, evaluates, typed⟩ := bodyTyped candidate
  exact ⟨result, .closure evaluates, typed⟩

/-- The dependent application case uses an actual observed runtime argument,
then transports the function's postcondition through capture-avoiding
substitution. -/
theorem application_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {types : TypeEnvironment} {environment : Environment} {frame : RecursionFrame}
    {fn arg : Expr} {name : String} {domain codomain : Ty} {observed : LTerm}
    (function : ∃ value, Eval signature environment frame fn value ∧
      (Ty.arrow name domain codomain).denote signature model assignment types environment value)
    (argument : ∃ value, Eval signature environment frame arg value ∧
      domain.denote signature model assignment types environment value)
    (observation : observe arg = .ok observed)
    (witnessFresh : valueName ∉ observed.freeVars) :
    ∃ value, Eval signature environment frame (.app fn arg) value ∧
      (Ty.substTerm name observed codomain).denote
        signature model assignment types environment value := by
  obtain ⟨functionValue, functionEval, functionTyped⟩ := function
  obtain ⟨argumentValue, argumentEval, argumentTyped⟩ := argument
  simp only [Ty.denote] at functionTyped
  obtain ⟨result, applies, resultTyped⟩ := functionTyped argumentValue argumentTyped
  refine ⟨result, .app functionEval argumentEval applies, ?_⟩
  exact (type_term_substitution signature model assignment types environment
    name observed codomain argumentValue result witnessFresh
    (observed_evaluation observation argumentEval)).mpr resultTyped

/-- Impredicative type application instantiates the universal interpretation
with the semantic candidate of an arbitrary type argument. -/
theorem type_application_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {types : TypeEnvironment} {environment : Environment} {frame : RecursionFrame}
    {fn : Expr} {argument body : Ty}
    (function : ∃ value, Eval signature environment frame fn value ∧
      (Ty.all body).denote signature model assignment types environment value) :
    ∃ value, Eval signature environment frame (.tyApp fn argument) value ∧
      (Ty.substType argument 0 body).denote
        signature model assignment types environment value := by
  obtain ⟨functionValue, functionEval, functionTyped⟩ := function
  simp only [Ty.denote] at functionTyped
  obtain ⟨result, applies, resultTyped⟩ :=
    functionTyped (argument.denote signature model assignment types environment)
  exact ⟨result, .tyApp functionEval applies,
    (type_substitution signature model assignment types environment argument body result).mpr
      resultTyped⟩

/-- Let-elimination drops the local environment slot only when the result type
does not mention its binder. -/
theorem let_case
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {types : TypeEnvironment} {environment : Environment} {frame : RecursionFrame}
    {name : String} {rhs body : Expr} {type result : Ty}
    (rhsTyped : ∃ value, Eval signature environment frame rhs value ∧
      type.denote signature model assignment types environment value)
    (bodyTyped : ∀ value, type.denote signature model assignment types environment value →
      ∃ resultValue, Eval signature (environment.bind name value) frame body resultValue ∧
        result.denote signature model assignment types (environment.bind name value) resultValue)
    (fresh : name ∉ result.freeVars) :
    ∃ value, Eval signature environment frame (.letE name rhs body) value ∧
      result.denote signature model assignment types environment value := by
  obtain ⟨rhsValue, rhsEval, rhsDenote⟩ := rhsTyped
  obtain ⟨resultValue, bodyEval, bodyDenote⟩ := bodyTyped rhsValue rhsDenote
  refine ⟨resultValue, .letE rhsEval bodyEval, ?_⟩
  apply (type_environment_congr signature model assignment types
    (environment.bind name rhsValue) environment result resultValue ?_).mp bodyDenote
  intro freeName member
  have distinct : freeName ≠ name := fun equal => fresh (equal ▸ member)
  simp only [Environment.bind, List.lookup_cons,
    show (freeName == name) = false from beq_eq_false_iff_ne.mpr distinct]

/-! The rule lemmas below expose the induction interface of the open theorem.
They work with the original declarative rules, not with checker success. -/

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
  exact variable_case lookupValue valueTyped
    (hasScope.witness_fresh member)

theorem semTyped_int
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} (n : Int) :
    SemTyped signature model assignment context assumptions (.int n)
      (.refine .int (.theory (.eq (.var valueName) (.int n)))) := by
  intro _ _ _ _ _ _
  exact integer_case n

theorem semTyped_bool
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} (b : Bool) :
    SemTyped signature model assignment context assumptions (.bool b)
      (.refine .bool (.theory (.eq (.var valueName) (.bool b)))) := by
  intro _ _ _ _ _ _
  exact boolean_case b

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
  exact application_case (function hasScope facts types environment frame realizes)
    (argument hasScope facts types environment frame realizes) observation witnessFresh

theorem semTyped_tyApp
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {fn : Expr} {argument body : Ty}
    (function : SemTyped signature model assignment context assumptions fn (.all body)) :
    SemTyped signature model assignment context assumptions (.tyApp fn argument)
      (Ty.substType argument 0 body) := by
  intro hasScope facts types environment frame realizes
  exact type_application_case (function hasScope facts types environment frame realizes)

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
  have domainScope := wfTy_inScope signature context domain 512 hasScope formed
  apply lambda_case
  intro argument argumentTyped
  exact bodyTyped (scoped_add _ _ _ _ hasScope domainScope added)
    (assumptionsScoped_add _ _ _ _ _ facts added) types (environment.bind name argument) frame
    (realizes_add signature model assignment context next assumptions types environment frame
      name domain argument hasScope facts domainScope added realizes argumentTyped)

theorem semTyped_tyLam
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {body : Expr} {type : Ty}
    (bodyTyped : SemTyped signature model assignment context.underType assumptions body type) :
    SemTyped signature model assignment context assumptions (.tyLam body) (.all type) := by
  intro hasScope facts types environment frame realizes
  apply type_lambda_case
  intro candidate
  exact bodyTyped (scoped_underType _ hasScope) (assumptionsScoped_underType _ _ facts)
    (candidate :: types) environment frame
    (realizes_underType signature model assignment context assumptions types environment frame
      candidate realizes)

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
  apply let_case (rhsTyped hasScope facts types environment frame realizes) ?_ fresh
  intro value valueTyped
  exact bodyTyped (scoped_add _ _ _ _ hasScope typeScope added)
    (assumptionsScoped_add _ _ _ _ _ facts added) types (environment.bind name value) frame
    (realizes_add signature model assignment context next assumptions types environment frame
      name type value hasScope facts typeScope added realizes valueTyped)

/-- The System F expression fragment whose fundamental theorem is established
here. Types may still mention abstract datatype candidates. -/
inductive CoreExpr : Expr → Prop where
  | var (name) : CoreExpr (.var name)
  | int (n) : CoreExpr (.int n)
  | bool (b) : CoreExpr (.bool b)
  | lam {name domain body} : CoreExpr body → CoreExpr (.lam name domain body)
  | app {fn arg} : CoreExpr fn → CoreExpr arg → CoreExpr (.app fn arg)
  | tyLam {body} : CoreExpr body → CoreExpr (.tyLam body)
  | tyApp {fn argument} : CoreExpr fn → CoreExpr (.tyApp fn argument)
  | letE {name rhs body} : CoreExpr rhs → CoreExpr body → CoreExpr (.letE name rhs body)
  | ann {expression type} : CoreExpr expression → CoreExpr (.ann expression type)

/-- The complete open fundamental theorem for the System F expression core.
Its proof uses the independent declarative derivation and the completed binding
and context-transport lemmas; the core theorem is admission-free. -/
theorem fundamental_core
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {context : Context} {assumptions : List Atom} {expression : Expr} {type : Ty}
    (typed : HasType signature model assignment context assumptions expression type) :
    CoreExpr expression → SemTyped signature model assignment context assumptions expression type := by
  induction typed using HasType.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ _ => True) with
  | var lookup => exact fun _ => semTyped_var lookup
  | int => exact fun _ => semTyped_int _
  | bool => exact fun _ => semTyped_bool _
  | lam formed added typed ih =>
    intro core
    cases core with
    | lam body => exact semTyped_lam formed added (ih body)
  | app fn arg observation fresh ihFn ihArg =>
    intro core
    cases core with
    | app fnCore argCore => exact semTyped_app (ihFn fnCore) (ihArg argCore) observation fresh
  | tyLam typed ih =>
    intro core
    cases core with
    | tyLam body => exact semTyped_tyLam (ih body)
  | tyApp typed formed ih =>
    intro core
    cases core with
    | tyApp fn => exact semTyped_tyApp (ih fn)
  | letE rhs typeScope added fresh body ihRhs ihBody =>
    intro core
    cases core with
    | letE rhsCore bodyCore => exact semTyped_let (ihRhs rhsCore) typeScope added fresh (ihBody bodyCore)
  | ann formed typed ih =>
    intro core
    cases core with
    | ann expression => exact semTyped_ann (ih expression)
  | subsumption typed subtyping ih => exact fun core => semTyped_subsumption (ih core) subtyping
  | ctor | matchE | structRec | recur | measure => intro core; cases core
  | _ => intros; trivial

theorem fundamental_core_closed
    {signature : Signature} {model : DataModel} {assignment : KAssignment}
    {expression : Expr} {type : Ty}
    (typed : HasType signature model assignment {} [] expression type)
    (core : CoreExpr expression) :
    ∃ value, Eval signature [] none expression value ∧
      type.denote signature model assignment [] [] value :=
  SemTyped.closed (fundamental_core typed core)

end LambdaRK.Draft
