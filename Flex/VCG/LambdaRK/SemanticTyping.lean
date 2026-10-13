import Flex.VCG.LambdaRK.Judgments
import Flex.VCG.LambdaRK.BindingLemmas

/-!
# Open semantic typing

The fundamental theorem must hold in open environments, including underneath
type abstractions and recursive closures. These invariants state its precise
induction interface. A recursion frame supplies correctness only for arguments
strictly smaller than the current root; it never assumes the current call is
already correct. No proof admissions are used in this module.
-/

namespace LambdaRK

def AssumptionsScoped (context : Context) (assumptions : List Atom) : Prop :=
  ∀ atom ∈ assumptions, ∀ name ∈ atom.freeVars, name ∈ context.names

/-- Formation properties needed by semantic weakening. Computational checking
implies these properties in a separate, currently draft formation proof. -/
structure Context.Scoped (context : Context) : Prop where
  unique : context.names.Nodup
  sourceNames : ∀ name type, (name, type) ∈ context.vars →
    name.isEmpty = false ∧ name.startsWith "$" = false
  types : ∀ name type, (name, type) ∈ context.vars → type.InScope context
  recursion : ∀ scope, context.recursion = some scope →
    context.vars.lookup scope.binder = some scope.domain ∧
    scope.domain.InScope context ∧ scope.codomain.InScope context ∧
    scope.binder ∉ scope.domain.freeVars
  smaller : ∀ name ∈ context.smaller, name ∈ context.names

/-- The well-founded induction hypothesis available inside a recursive body.
The runtime frame may persist when the source context cannot access it. -/
def FrameRealizes (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (types : TypeEnvironment)
    (environment : Environment) (frame : RecursionFrame) (context : Context) : Prop :=
  match context.recursion with
  | none => True
  | some scope => ∃ function root,
      frame = some function ∧ environment.lookup scope.binder = some root ∧
      scope.domain.denote signature model assignment types environment root ∧
      (∀ name ∈ context.smaller, ∃ value,
        environment.lookup name = some value ∧ Smaller value root) ∧
      (∀ argument, Smaller argument root →
        scope.domain.denote signature model assignment types environment argument →
        ∃ result, Apply signature function argument result ∧
          scope.codomain.denote signature model assignment types
            (environment.bind scope.binder argument) result)

structure Context.Realizes (context : Context) (signature : Signature)
    (model : DataModel) (assignment : KAssignment) (types : TypeEnvironment)
    (environment : Environment) (frame : RecursionFrame) (assumptions : List Atom) : Prop where
  typeDepth : types.length = context.typeDepth
  variables : environment.Satisfies signature model assignment types context.vars
  assumptions : AssumptionsHold signature assignment environment assumptions
  recursion : FrameRealizes signature model assignment types environment frame context

/-- Open total correctness. Static formation and runtime realization are
premises; evaluation and membership in the result type are the conclusion. -/
def SemTyped (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (context : Context) (assumptions : List Atom) (expression : Expr) (type : Ty) : Prop :=
  context.Scoped → AssumptionsScoped context assumptions →
    ∀ (types : TypeEnvironment) (environment : Environment) (frame : RecursionFrame),
      context.Realizes signature model assignment types environment frame assumptions →
      ∃ value, Eval signature environment frame expression value ∧
        type.denote signature model assignment types environment value

theorem Context.scoped_empty : ({} : Context).Scoped := by
  constructor
  · simp [Context.names]
  · simp
  · simp
  · simp
  · simp

theorem assumptionsScoped_nil (context : Context) : AssumptionsScoped context [] := by
  simp [AssumptionsScoped]

theorem Context.realizes_empty (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (environment : Environment) (frame : RecursionFrame) :
    ({} : Context).Realizes signature model assignment [] environment frame [] := by
  constructor
  · rfl
  · simp [Environment.Satisfies]
  · simp [AssumptionsHold]
  · trivial

theorem Context.Scoped.witness_fresh {context : Context} (hasScope : context.Scoped)
    {name : String} {type : Ty} (member : (name, type) ∈ context.vars) :
    name ≠ valueName := by
  intro equal
  have valid := (hasScope.sourceNames name type member).2
  subst name
  have reserved : valueName.startsWith "$" = true := by decide +kernel
  simp [reserved] at valid

theorem Context.Realizes.lookup {context : Context} {signature : Signature}
    {model : DataModel} {assignment : KAssignment} {types : TypeEnvironment}
    {environment : Environment} {frame : RecursionFrame} {assumptions : List Atom}
    (realizes : context.Realizes signature model assignment types environment frame assumptions)
    {name : String} {type : Ty} (lookup : context.vars.lookup name = some type) :
    ∃ value, environment.lookup name = some value ∧
      type.denote signature model assignment types environment value := by
  apply realizes.variables name type
  obtain ⟨before, after, entries, _⟩ := List.lookup_eq_some_iff.mp lookup
  simp [entries]

/-- Closing the open theorem needs neither an artificial frame nor assumptions
about values stored in unrelated environment slots. -/
theorem SemTyped.closed {signature : Signature} {model : DataModel}
    {assignment : KAssignment} {expression : Expr} {type : Ty}
    (typed : SemTyped signature model assignment {} [] expression type) :
    ∃ value, Eval signature [] none expression value ∧
      type.denote signature model assignment [] [] value :=
  typed Context.scoped_empty (assumptionsScoped_nil _) [] [] none
    (Context.realizes_empty signature model assignment [] none)

end LambdaRK
