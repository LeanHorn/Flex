import Flex.VCG.LambdaRK.Signature

/-!
# Operational semantics of the draft λRK language

Evaluation erases type arguments. Term closures capture their lexical environment
and recursion frame; `recur` refers to the structural function being evaluated,
including when it occurs underneath an ordinary lambda. The typing rules, not
this operational relation, enforce that recursive calls use smaller arguments.
-/

namespace LambdaRK

inductive Value where
  | int (value : Int)
  | bool (value : Bool)
  | ctor (name : String) (fields : List Value)
  | closure (binder : String) (body : Expr)
      (environment : List (String × Value)) (recursion : Option Value)
  | typeClosure (body : Expr)
      (environment : List (String × Value)) (recursion : Option Value)
  | recursiveClosure (binder : String) (body : Expr)
      (environment : List (String × Value))
  deriving Inhabited

abbrev Environment := List (String × Value)
abbrev RecursionFrame := Option Value

def Environment.bind (environment : Environment) (name : String) (value : Value) :
    Environment := (name, value) :: environment

def Environment.bindMany (environment : Environment) (names : List String)
    (values : List Value) : Environment := names.zip values ++ environment

def findBranch (branches : List (String × List String × Expr)) (ctor : String) :
    Option (String × List String × Expr) := branches.find? (fun b => b.1 == ctor)

mutual
  /-- Meaning of a declared measure on a constructor value. -/
  inductive MeasureEval (signature : Signature) : String → Value → Int → Prop where
    | constructor {name declaration ctor fields branch result} :
        signature.findMeasure name = some declaration →
        declaration.cases.find? (fun c => c.ctor == ctor) = some branch →
        MeasureBodyEval signature name fields branch.body result →
        MeasureEval signature name (.ctor ctor fields) result

  /-- Measure programs only inspect integer fields and recurse on constructor
  fields. Signature validation supplies the typing and decrease conditions. -/
  inductive MeasureBodyEval (signature : Signature) :
      String → List Value → MeasureBody → Int → Prop where
    | literal {name fields n} :
        MeasureBodyEval signature name fields (.literal n) n
    | field {name fields index n} :
        fields[index]? = some (.int n) →
        MeasureBodyEval signature name fields (.field index) n
    | recur {name fields index value n} :
        fields[index]? = some value → MeasureEval signature name value n →
        MeasureBodyEval signature name fields (.recur index) n
    | add {name fields left right m n} :
        MeasureBodyEval signature name fields left m →
        MeasureBodyEval signature name fields right n →
        MeasureBodyEval signature name fields (.add left right) (m + n)
end

mutual
  /-- Call-by-value evaluation with lexical environments and erased types. -/
  inductive Eval (signature : Signature) :
      Environment → RecursionFrame → Expr → Value → Prop where
    | var {environment frame name value} :
        environment.lookup name = some value →
        Eval signature environment frame (.var name) value
    | int {environment frame n} : Eval signature environment frame (.int n) (.int n)
    | bool {environment frame b} : Eval signature environment frame (.bool b) (.bool b)
    | lam {environment frame name domain body} :
        Eval signature environment frame (.lam name domain body)
          (.closure name body environment frame)
    | tyLam {environment frame body} :
        Eval signature environment frame (.tyLam body)
          (.typeClosure body environment frame)
    | structRec {environment frame name domain codomain body} :
        Eval signature environment frame (.structRec name domain codomain body)
          (.recursiveClosure name body environment)
    | app {environment frame fn arg function argument result} :
        Eval signature environment frame fn function →
        Eval signature environment frame arg argument →
        Apply signature function argument result →
        Eval signature environment frame (.app fn arg) result
    | tyApp {environment frame fn argument function result} :
        Eval signature environment frame fn function →
        TypeApply signature function result →
        Eval signature environment frame (.tyApp fn argument) result
    | letE {environment frame name rhs body value result} :
        Eval signature environment frame rhs value →
        Eval signature (Environment.bind environment name value) frame body result →
        Eval signature environment frame (.letE name rhs body) result
    | ctor {environment frame name arguments fields values} :
        EvalList signature environment frame fields values →
        Eval signature environment frame (.ctor name arguments fields) (.ctor name values)
    | matchE {environment frame scrutinee branches name fields names body result} :
        Eval signature environment frame scrutinee (.ctor name fields) →
        findBranch branches name = some (name, names, body) →
        names.length = fields.length →
        Eval signature (Environment.bindMany environment names fields) frame body result →
        Eval signature environment frame (.matchE scrutinee branches) result
    | recur {environment frame argument value function result} :
        frame = some function →
        Eval signature environment frame argument value →
        Apply signature function value result →
        Eval signature environment frame (.recur argument) result
    | measure {environment frame name argument value result} :
        Eval signature environment frame argument value →
        MeasureEval signature name value result →
        Eval signature environment frame (.measure name argument) (.int result)
    | ann {environment frame expression type result} :
        Eval signature environment frame expression result →
        Eval signature environment frame (.ann expression type) result

  /-- Applying either an ordinary closure or a structurally recursive closure. -/
  inductive Apply (signature : Signature) : Value → Value → Value → Prop where
    | closure {name body environment frame argument result} :
        Eval signature (Environment.bind environment name argument) frame body result →
        Apply signature (.closure name body environment frame) argument result
    | recursiveClosure {name body environment argument result} :
        Eval signature (Environment.bind environment name argument)
          (some (.recursiveClosure name body environment)) body result →
        Apply signature (.recursiveClosure name body environment) argument result

  /-- Type application performs the suspended computation; types are erased. -/
  inductive TypeApply (signature : Signature) : Value → Value → Prop where
    | closure {body environment frame result} :
        Eval signature environment frame body result →
        TypeApply signature (.typeClosure body environment frame) result

  inductive EvalList (signature : Signature) :
      Environment → RecursionFrame → List Expr → List Value → Prop where
    | nil {environment frame} : EvalList signature environment frame [] []
    | cons {environment frame expression expressions value values} :
        Eval signature environment frame expression value →
        EvalList signature environment frame expressions values →
        EvalList signature environment frame (expression :: expressions) (value :: values)
end

/-- Strict structural subvalues, the semantic ordering behind source recursion. -/
inductive Smaller : Value → Value → Prop where
  | field {name fields value} : value ∈ fields → Smaller value (.ctor name fields)
  | trans {small middle large} : Smaller small middle → Smaller middle large → Smaller small large

end LambdaRK
