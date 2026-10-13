import Flex.VCG.LambdaRK.Model
import Flex.VCG.LambdaRK.Context

/-!
# Declarative typing specification

These rules are independent of `check`/`synth`: there is no constructor turning
checker success into typing. Subsumption uses semantic entailment, and pattern
branches carry their constructor equation explicitly. The computational context
and well-formedness operations are shared with the draft checker.

Let bindings require an explicitly scoped inferred type: semantic subsumption
alone does not imply syntactic formation. Match results must be scoped in the
outer context so that pattern-bound names cannot escape. Applications exclude the reserved
refinement witness from logical observations, as required by substitution.
-/

namespace LambdaRK

def AssumptionsHold (signature : Signature) (assignment : KAssignment)
    (environment : Environment) (assumptions : List Atom) : Prop :=
  ∀ atom, atom ∈ assumptions → atom.denote signature assignment environment

/-- Semantic subtyping under the current typed variables and branch facts. -/
def Subtype (signature : Signature) (model : DataModel) (assignment : KAssignment)
    (context : Context) (assumptions : List Atom) (source target : Ty) : Prop :=
  ∀ (types : TypeEnvironment) (environment : Environment),
    types.length = context.typeDepth →
    environment.Satisfies signature model assignment types context.vars →
    AssumptionsHold signature assignment environment assumptions →
    ∀ value, source.denote signature model assignment types environment value →
      target.denote signature model assignment types environment value

/-- Add constructor fields, retaining the same explicit freshness checks as
ordinary context extension. This operation does no expression checking. -/
def extendFields (context : Context) (fields : List (String × Ty)) : Except String Context :=
  fields.foldlM (fun context (name, type) => context.add name type) context

/-- The structural decrease information available in a pattern branch. -/
def markSmaller (context : Context) (scrutinee : String)
    (fields : List (String × Ty)) : Context :=
  match context.recursion with
  | none => context
  | some recursion =>
    if scrutinee == recursion.binder || context.smaller.contains scrutinee then
      { context with smaller := (fields.foldl (fun smaller (name, type) =>
          if type.outerBase == recursion.domain.outerBase then name :: smaller else smaller)
          context.smaller) }
    else context

mutual
  inductive HasType (signature : Signature) (model : DataModel) (assignment : KAssignment) :
      Context → List Atom → Expr → Ty → Prop where
    | var {context assumptions name type} :
        context.vars.lookup name = some type →
        HasType signature model assignment context assumptions (.var name) (selfType name type)
    | int {context assumptions n} :
        HasType signature model assignment context assumptions (.int n)
          (.refine .int (.theory (.eq (.var valueName) (.int n))))
    | bool {context assumptions b} :
        HasType signature model assignment context assumptions (.bool b)
          (.refine .bool (.theory (.eq (.var valueName) (.bool b))))
    | lam {context assumptions name domain body codomain next} :
        wfTy signature context 512 domain = .ok () →
        context.add name domain = .ok next →
        HasType signature model assignment next assumptions body codomain →
        HasType signature model assignment context assumptions (.lam name domain body)
          (.arrow name domain codomain)
    | app {context assumptions fn arg name domain codomain observed} :
        HasType signature model assignment context assumptions fn (.arrow name domain codomain) →
        HasType signature model assignment context assumptions arg domain →
        observe arg = .ok observed →
        valueName ∉ observed.freeVars →
        HasType signature model assignment context assumptions (.app fn arg)
          (Ty.substTerm name observed codomain)
    | tyLam {context assumptions body type} :
        HasType signature model assignment context.underType assumptions body type →
        HasType signature model assignment context assumptions (.tyLam body) (.all type)
    | tyApp {context assumptions fn argument body} :
        HasType signature model assignment context assumptions fn (.all body) →
        wfTy signature context 512 argument = .ok () →
        HasType signature model assignment context assumptions (.tyApp fn argument)
          (Ty.substType argument 0 body)
    | letE {context assumptions name rhs body type result next} :
        HasType signature model assignment context assumptions rhs type →
        type.InScope context →
        context.add name type = .ok next →
        name ∉ result.freeVars →
        HasType signature model assignment next assumptions body result →
        HasType signature model assignment context assumptions (.letE name rhs body) result
    | ctor {context assumptions name arguments fields data constructor observed} :
        signature.findCtor name = some (data, constructor) →
        arguments.length = data.params →
        (∀ type, type ∈ arguments → wfTy signature context 512 type = .ok ()) →
        HasTypes signature model assignment context assumptions fields
          (constructor.fields.map (Ty.instantiateParams arguments)) →
        fields.mapM observe = .ok observed →
        HasType signature model assignment context assumptions (.ctor name arguments fields)
          (.refine (.data data.name arguments)
            (.theory (.eq (.var valueName) (.ctor name observed))))
    | matchE {context assumptions scrutinee name arguments data branches result} :
        result.InScope context →
        HasType signature model assignment context assumptions (.var scrutinee) (.data name arguments) →
        signature.findData name = some data →
        (branches.map (·.1)).length = data.ctors.length →
        (branches.map (·.1)).Nodup →
        (∀ constructor, constructor ∈ data.ctors → constructor.name ∈ branches.map (·.1)) →
        BranchesTyped signature model assignment context assumptions scrutinee data arguments
          branches result →
        HasType signature model assignment context assumptions (.matchE (.var scrutinee) branches) result
    | structRec {context assumptions name domain codomain body next data arguments} :
        wfTy signature context 512 domain = .ok () →
        domain.outerBase = .data data arguments →
        context.add name domain = .ok next →
        wfTy signature next 512 codomain = .ok () →
        HasType signature model assignment
          { next with recursion := some { binder := name, domain, codomain }, smaller := [] }
          assumptions body codomain →
        HasType signature model assignment context assumptions (.structRec name domain codomain body)
          (.arrow name domain codomain)
    | recur {context assumptions recursion name} :
        context.recursion = some recursion → name ∈ context.smaller →
        HasType signature model assignment context assumptions (.var name) recursion.domain →
        HasType signature model assignment context assumptions (.recur (.var name))
          (Ty.substTerm recursion.binder (.var name) recursion.codomain)
    | measure {context assumptions name argument data arguments declaration observed} :
        signature.findMeasure name = some declaration → declaration.datatype = data →
        HasType signature model assignment context assumptions argument (.data data arguments) →
        observe argument = .ok observed →
        HasType signature model assignment context assumptions (.measure name argument)
          (.refine .int (.theory (.eq (.var valueName) (.measure name observed))))
    | ann {context assumptions expression type} :
        wfTy signature context 512 type = .ok () →
        HasType signature model assignment context assumptions expression type →
        HasType signature model assignment context assumptions (.ann expression type) type
    | subsumption {context assumptions expression source target} :
        HasType signature model assignment context assumptions expression source →
        Subtype signature model assignment context assumptions source target →
        HasType signature model assignment context assumptions expression target

  inductive HasTypes (signature : Signature) (model : DataModel) (assignment : KAssignment) :
      Context → List Atom → List Expr → List Ty → Prop where
    | nil {context assumptions} : HasTypes signature model assignment context assumptions [] []
    | cons {context assumptions expression expressions type types} :
        HasType signature model assignment context assumptions expression type →
        HasTypes signature model assignment context assumptions expressions types →
        HasTypes signature model assignment context assumptions (expression :: expressions) (type :: types)

  inductive BranchesTyped (signature : Signature) (model : DataModel) (assignment : KAssignment) :
      Context → List Atom → String → DataDecl → List Ty →
      List (String × List String × Expr) → Ty → Prop where
    | nil {context assumptions scrutinee data arguments result} :
        BranchesTyped signature model assignment context assumptions scrutinee data arguments [] result
    | cons {context assumptions scrutinee data arguments name names body branches result constructor next} :
        constructor ∈ data.ctors → constructor.name = name →
        names.length = constructor.fields.length →
        extendFields context (names.zip (constructor.fields.map (Ty.instantiateParams arguments))) = .ok next →
        HasType signature model assignment
          (markSmaller next scrutinee (names.zip (constructor.fields.map (Ty.instantiateParams arguments))))
          (.theory (.eq (.var scrutinee) (.ctor name (names.map LTerm.var))) :: assumptions)
          body result →
        BranchesTyped signature model assignment context assumptions scrutinee data arguments branches result →
        BranchesTyped signature model assignment context assumptions scrutinee data arguments
          ((name, names, body) :: branches) result
end

end LambdaRK
