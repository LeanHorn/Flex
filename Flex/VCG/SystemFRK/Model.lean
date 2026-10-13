import Flex.VCG.SystemFRK.Semantics

/-! Semantic types and constraints. System F variables range over predicates
`Value → Prop`; the datatype model is constructed in `Datatypes/`. -/

namespace SystemFRK

abbrev Candidate := Value → Prop
abbrev TypeEnvironment := List Candidate
abbrev KAssignment := String → List Value → Prop

inductive All₂ {α β : Type} (relation : α → β → Prop) : List α → List β → Prop where
  | nil : All₂ relation [] []
  | cons {a as b bs} : relation a b → All₂ relation as bs →
      All₂ relation (a :: as) (b :: bs)

mutual
  inductive LogicalEval (signature : Signature) (environment : Environment) :
      LTerm → Value → Prop where
    | var {name value} : environment.lookup name = some value →
        LogicalEval signature environment (.var name) value
    | int {n} : LogicalEval signature environment (.int n) (.int n)
    | bool {b} : LogicalEval signature environment (.bool b) (.bool b)
    | add {left right m n} :
        LogicalEval signature environment left (.int m) →
        LogicalEval signature environment right (.int n) →
        LogicalEval signature environment (.add left right) (.int (m + n))
    | ctor {name fields values} : LogicalListEval signature environment fields values →
        LogicalEval signature environment (.ctor name fields) (.ctor name values)
    | measure {name argument value result} :
        LogicalEval signature environment argument value →
        MeasureEval signature name value result →
        LogicalEval signature environment (.measure name argument) (.int result)

  inductive LogicalListEval (signature : Signature) (environment : Environment) :
      List LTerm → List Value → Prop where
    | nil : LogicalListEval signature environment [] []
    | cons {term terms value values} :
        LogicalEval signature environment term value →
        LogicalListEval signature environment terms values →
        LogicalListEval signature environment (term :: terms) (value :: values)
end

def Formula.denote (signature : Signature) (environment : Environment) : Formula → Prop
  | .truth => True
  | .falsity => False
  | .eq left right => ∃ value,
      LogicalEval signature environment left value ∧ LogicalEval signature environment right value
  | .le left right => ∃ m n,
      LogicalEval signature environment left (.int m) ∧
      LogicalEval signature environment right (.int n) ∧ m ≤ n
  | .and left right => left.denote signature environment ∧ right.denote signature environment
  | .or left right => left.denote signature environment ∨ right.denote signature environment
  | .not body => ¬ body.denote signature environment

def Atom.denote (signature : Signature) (assignment : KAssignment)
    (environment : Environment) : Atom → Prop
  | .theory formula => formula.denote signature environment
  | .kvar name arguments => ∃ values,
      LogicalListEval signature environment arguments values ∧ assignment name values

def LSort.contains : LSort → Candidate
  | .int => fun value => ∃ n, value = .int n
  | .bool => fun value => ∃ b, value = .bool b
  | .value => fun _ => True

def Cstr.denote (signature : Signature) (assignment : KAssignment)
    (environment : Environment) : Cstr → Prop
  | .truth => True
  | .head atom => atom.denote signature assignment environment
  | .guard antecedent consequent =>
      antecedent.denote signature assignment environment →
      consequent.denote signature assignment environment
  | .all binder sort body => ∀ value, sort.contains value →
      body.denote signature assignment (environment.bind binder value)
  | .conj left right =>
      left.denote signature assignment environment ∧ right.denote signature assignment environment

/-- Validity in every runtime environment. -/
def Cstr.Valid (signature : Signature) (assignment : KAssignment) (constraint : Cstr) : Prop :=
  ∀ environment, constraint.denote signature assignment environment

structure DataModel where
  datatype : String → List Candidate → Candidate

/-- Function shape is required even when the argument type is empty. -/
def Value.IsFunction : Value → Prop
  | .closure .. | .recursiveClosure .. => True
  | _ => False

/-- Total correctness: function and polymorphic values must evaluate when eliminated. -/
def Ty.denote (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (types : TypeEnvironment) (environment : Environment) : Ty → Candidate
  | .var index => types[index]?.getD (fun _ => False)
  | .int => LSort.int.contains
  | .bool => LSort.bool.contains
  | .data name arguments => model.datatype name
      (arguments.map (fun argument => argument.denote signature model assignment types environment))
  | .arrow binder domain codomain => fun function => function.IsFunction ∧ ∀ argument,
      domain.denote signature model assignment types environment argument →
      ∃ result, Apply signature function argument result ∧
        codomain.denote signature model assignment types (environment.bind binder argument) result
  | .all body => fun function => ∀ candidate : Candidate,
      ∃ result, TypeApply signature function result ∧
        body.denote signature model assignment (candidate :: types) environment result
  | .refine base predicate => fun value =>
      base.denote signature model assignment types environment value ∧
      predicate.denote signature assignment (environment.bind valueName value)

/-- Exact constructor laws, proved for the canonical model in `Datatypes/Adequacy`. -/
def DatatypeAdequate (signature : Signature) (model : DataModel)
    (assignment : KAssignment) : Prop :=
  ∀ (types : TypeEnvironment) (environment : Environment) (name : String)
    (arguments : List Ty) (value : Value),
    (Ty.data name arguments).denote signature model assignment types environment value ↔
      ∃ (declaration : DataDecl) (constructor : CtorDecl) (fields : List Value),
        signature.findData name = some declaration ∧
        declaration.params = arguments.length ∧
        constructor ∈ declaration.ctors ∧
        value = .ctor constructor.name fields ∧
        All₂ (fun fieldType field =>
          (Ty.instantiateParams arguments fieldType).denote
            signature model assignment types environment field) constructor.fields fields

def Environment.Satisfies (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (types : TypeEnvironment)
    (environment : Environment) (context : List (String × Ty)) : Prop :=
  ∀ name type, (name, type) ∈ context → ∃ value,
    environment.lookup name = some value ∧
    type.denote signature model assignment types environment value

end SystemFRK
