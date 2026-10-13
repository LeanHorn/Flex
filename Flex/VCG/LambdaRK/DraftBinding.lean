import Flex.VCG.LambdaRK.BindingLemmas
import Flex.VCG.LambdaRK.Model
import Flex.VCG.LambdaRK.LogicalLemmas
import Flex.VCG.LambdaRK.SubstitutionLemmas

/-!
# Proved substitution interfaces for the main proofs

The named interfaces used by the staged semantic proofs now delegate to
admission-free syntactic, alpha-renaming, environment-agreement, and semantic
substitution lemmas. They retain their existing signatures so the core proof
and later language cases share one stable binding interface.

`TypeScoped` concerns de Bruijn indices only. It does not assert preservation of
the fuel-bounded `wfTy` checker. Alpha-renaming is specified by free names and
semantic equivalence, not by literal equality of named types. Expression-level
type substitution is only intended for logically closed replacements; a future
evaluation lemma must relate erased closures rather than equate their syntax.
-/

namespace LambdaRK.Draft

/-! ## Syntactic scope and freshness -/

theorem freshenBinders_freeVars (avoid : List String) (type : Ty) (name : String) :
    name ∈ (type.freshenBinders avoid).freeVars ↔ name ∈ type.freeVars := by
  exact type.freshenBinders_freeVars avoid name

theorem freshenBinders_avoids (avoid : List String) (type : Ty) (name : String)
    (bound : name ∈ (type.freshenBinders avoid).TermBinders) :
    name ∉ avoid := by
  exact type.freshenBinders_avoids avoid name bound

theorem shiftTypes_scoped (type : Ty) (depth amount cutoff : Nat)
    (hasScope : type.TypeScoped depth) :
    (Ty.shiftTypes amount cutoff type).TypeScoped (depth + amount) := by
  exact type.shiftTypes_scoped depth amount cutoff hasScope

theorem substType_scoped (body replacement : Ty) (depth index : Nat)
    (indexInScope : index ≤ depth)
    (bodyScoped : body.TypeScoped (depth + 1))
    (replacementScoped : replacement.TypeScoped depth) :
    (Ty.substType replacement index body).TypeScoped depth := by
  exact body.substType_scoped replacement depth index indexInScope bodyScoped replacementScoped

theorem instantiateParams_scoped (arguments : List Ty) (field : Ty) (depth : Nat)
    (fieldScoped : field.TypeScoped arguments.length)
    (argumentsScoped : ∀ argument ∈ arguments, argument.TypeScoped depth) :
    (Ty.instantiateParams arguments field).TypeScoped depth := by
  exact Ty.instantiateParams_scoped arguments field depth fieldScoped argumentsScoped

/-! ## Environment agreement and alpha-renaming

These are the weakening interfaces for the logical and semantic layers. They
compare lookups on free names, so irrelevant environment slots can differ.
-/

theorem logical_environment_congr
    (signature : Signature) (left right : Environment) (term : LTerm) (value : Value)
    (agree : ∀ name ∈ term.freeVars, left.lookup name = right.lookup name) :
    LogicalEval signature left term value ↔ LogicalEval signature right term value := by
  exact LogicalEval.environment_congr signature left right term value agree

theorem type_environment_congr
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (left right : Environment) (type : Ty) (value : Value)
    (agree : ∀ name ∈ type.freeVars, left.lookup name = right.lookup name) :
    type.denote signature model assignment types left value ↔
      type.denote signature model assignment types right value := by
  rw [type.environment_congr signature model assignment types left right agree]

theorem freshenBinders_denote
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment)
    (avoid : List String) (type : Ty) (value : Value) :
    (type.freshenBinders avoid).denote signature model assignment types environment value ↔
      type.denote signature model assignment types environment value := by
  rw [type.freshenBinders_denote]

/-! ## Logical substitution

The term lemma is proved in `LogicalLemmas`. Its list, formula, and atom
liftings below are independent of the semantic type-substitution proofs.
-/

theorem logical_substitution
    (signature : Signature) (environment : Environment)
    (name : String) (replacement term : LTerm) (replacementValue value : Value)
    (h : LogicalEval signature environment replacement replacementValue) :
    LogicalEval signature environment (term.substTerm name replacement) value ↔
      LogicalEval signature (Environment.bind environment name replacementValue) term value := by
  exact LogicalEval.substitution signature environment name replacement term replacementValue value h

theorem logical_list_substitution
    (signature : Signature) (environment : Environment)
    (name : String) (replacement : LTerm) (terms : List LTerm)
    (replacementValue : Value) (values : List Value)
    (h : LogicalEval signature environment replacement replacementValue) :
    LogicalListEval signature environment (terms.map (·.substTerm name replacement)) values ↔
      LogicalListEval signature (environment.bind name replacementValue) terms values := by
  induction terms generalizing values with
  | nil => constructor <;> intro derivation <;> cases derivation <;> constructor
  | cons term terms ih =>
    constructor
    · intro derivation
      cases derivation with
      | cons head tail =>
        exact .cons ((logical_substitution _ _ _ _ _ _ _ h).mp head) ((ih _).mp tail)
    · intro derivation
      cases derivation with
      | cons head tail =>
        exact .cons ((logical_substitution _ _ _ _ _ _ _ h).mpr head) ((ih _).mpr tail)

theorem formula_substitution
    (signature : Signature) (environment : Environment)
    (name : String) (replacement : LTerm) (formula : Formula) (replacementValue : Value)
    (h : LogicalEval signature environment replacement replacementValue) :
    (formula.substTerm name replacement).denote signature environment ↔
      formula.denote signature (environment.bind name replacementValue) := by
  induction formula with
  | truth => rfl
  | falsity => rfl
  | eq left right =>
    simp only [Formula.substTerm, Formula.denote, logical_substitution _ _ _ _ _ _ _ h]
  | le left right =>
    simp only [Formula.substTerm, Formula.denote, logical_substitution _ _ _ _ _ _ _ h]
  | and left right ihLeft ihRight =>
    exact and_congr ihLeft ihRight
  | or left right ihLeft ihRight =>
    exact or_congr ihLeft ihRight
  | not body ih => exact not_congr ih

theorem atom_substitution
    (signature : Signature) (assignment : KAssignment) (environment : Environment)
    (name : String) (replacement : LTerm) (atom : Atom) (replacementValue : Value)
    (h : LogicalEval signature environment replacement replacementValue) :
    (atom.substTerm name replacement).denote signature assignment environment ↔
      atom.denote signature assignment (environment.bind name replacementValue) := by
  cases atom with
  | theory formula => exact formula_substitution _ _ _ _ _ _ h
  | kvar predicate arguments =>
    simp only [Atom.substTerm, Atom.denote, logical_list_substitution _ _ _ _ _ _ _ h]

/-! ## Interfaces used by application, System F, and datatypes -/

/-- `$value` is the fixed refinement witness. A replacement referring to it
would be captured by a refinement; arrow-binder freshening cannot prevent that.
Source observations satisfy this condition because `$` names are reserved. -/
theorem type_term_substitution
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment)
    (name : String) (replacement : LTerm) (body : Ty) (replacementValue value : Value)
    (witnessFresh : valueName ∉ replacement.freeVars)
    (evaluates : LogicalEval signature environment replacement replacementValue) :
    (Ty.substTerm name replacement body).denote signature model assignment types environment value ↔
      body.denote signature model assignment types
        (environment.bind name replacementValue) value := by
  rw [body.substTerm_denote signature model assignment types environment name replacement replacementValue witnessFresh evaluates]

/-- Weakening under new semantic type candidates, including under `all`. -/
theorem type_shift_denote
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types extraTypes : TypeEnvironment) (environment : Environment) (body : Ty) (value : Value) :
    (Ty.shiftTypes extraTypes.length 0 body).denote
        signature model assignment (extraTypes ++ types) environment value ↔
      body.denote signature model assignment types environment value := by
  rw [body.shiftTypes_denote signature model assignment types extraTypes environment]

/-- Semantic type substitution, including arguments with free logical names.
The candidate on the right retains the original environment. The proof must
use alpha-freshening and environment agreement to transport that candidate
under every arrow crossed on the left. -/
theorem type_substitution
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment) (replacement body : Ty)
    (value : Value) :
    (Ty.substType replacement 0 body).denote signature model assignment types environment value ↔
      body.denote signature model assignment
        ((replacement.denote signature model assignment types environment) :: types)
        environment value := by
  rw [body.substType_denote]

/-- The earlier closed interface is a specialization of the open contract;
its proof uses the proved general theorem. -/
theorem type_substitution_closed
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment) (replacement body : Ty)
    (_closed : replacement.freeVars = []) (value : Value) :
    (Ty.substType replacement 0 body).denote signature model assignment types environment value ↔
      body.denote signature model assignment
        ((replacement.denote signature model assignment types environment) :: types)
        environment value := by
  exact type_substitution signature model assignment types environment replacement body value

/-- Constructor fields use declaration-order parameters, so their semantic
arguments are prepended in declaration order rather than reversed. Free logical
names are supported by the same freshness/environment-agreement argument. -/
theorem instantiateParams_denote
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment)
    (arguments : List Ty) (field : Ty) (value : Value) :
    (Ty.instantiateParams arguments field).denote signature model assignment types environment value ↔
      field.denote signature model assignment
        ((arguments.map (fun argument =>
          argument.denote signature model assignment types environment)) ++ types)
        environment value := by
  rw [field.instantiateParams_denote]

theorem instantiateParams_denote_closed
    (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment)
    (arguments : List Ty) (field : Ty) (value : Value)
    (_closed : ∀ argument ∈ arguments, argument.freeVars = []) :
    (Ty.instantiateParams arguments field).denote signature model assignment types environment value ↔
      field.denote signature model assignment
        ((arguments.map (fun argument =>
          argument.denote signature model assignment types environment)) ++ types)
        environment value := by
  exact instantiateParams_denote signature model assignment types environment arguments field value

end LambdaRK.Draft
