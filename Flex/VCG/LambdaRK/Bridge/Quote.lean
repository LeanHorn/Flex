import Flex.VCG.LambdaRK.Bridge.Syntax
import Flex.VCG.LambdaRK.Bridge.Reflect
import Flex.VCG.LambdaRK.Bridge.Semantics

/-!
Turn the scalar frontend's syntax into ordinary Lean propositions. Solver input
therefore goes through the existing checked CHC exporter, model importer, and
certificate API. This layer rejects malformed indices and inconsistent scalar
types before constructing a solver goal.
-/

namespace LambdaRK.Bridge

open Lean Meta

def scalarSortType : ScalarSort → Lean.Expr
  | .int => mkConst ``Int
  | .bool => mkConst ``Bool

private def requireType (expression type : Lean.Expr) : MetaM Unit := do
  unless ← isDefEq (← inferType expression) type do
    throwError "λRK bridge: expected {type}, got {expression}"

/-- Variable numbers index the clause's scalar binders, rather than source names.
Every occurrence is type-checked, so a malformed lowering cannot reinterpret a
Boolean binder as an integer. -/
def scalarTermExpr (variables : Array Lean.Expr) : ScalarTerm → MetaM Lean.Expr
  | .var index sort => do
      let some expression := variables[index]?
        | throwError "λRK bridge: unknown scalar variable {index}"
      requireType expression (scalarSortType sort)
      return expression
  | .int value => return toExpr value
  | .bool value => return toExpr value
  | .add left right => do
      let left ← scalarTermExpr variables left
      let right ← scalarTermExpr variables right
      requireType left (mkConst ``Int)
      requireType right (mkConst ``Int)
      mkAppM ``HAdd.hAdd #[left, right]

/-- Relation expressions are the actual typed predicate slots that will be
quantified in the solver goal. Multiple declarations may have different arities
and different mixtures of integer and Boolean arguments. -/
def scalarFormulaExpr (relations : Array (String × Lean.Expr))
    (variables : Array Lean.Expr) : ScalarFormula → MetaM Lean.Expr
  | .truth => return mkConst ``True
  | .falsity => return mkConst ``False
  | .eq left right => do
      let left ← scalarTermExpr variables left
      let right ← scalarTermExpr variables right
      requireType right (← inferType left)
      mkEq left right
  | .le left right => do
      let left ← scalarTermExpr variables left
      let right ← scalarTermExpr variables right
      requireType left (mkConst ``Int)
      requireType right (mkConst ``Int)
      mkAppM ``LE.le #[left, right]
  | .and left right => do
      return mkAnd (← scalarFormulaExpr relations variables left)
        (← scalarFormulaExpr relations variables right)
  | .or left right => do
      return mkOr (← scalarFormulaExpr relations variables left)
        (← scalarFormulaExpr relations variables right)
  | .not body => do
      return mkNot (← scalarFormulaExpr relations variables body)
  | .rel name arguments => do
      let some (_, relation) := relations.find? (fun entry => entry.1 == name)
        | throwError "λRK bridge: undeclared scalar relation {name}"
      let arguments ← arguments.toArray.mapM (scalarTermExpr variables)
      let expression := mkAppN relation arguments
      check expression
      unless ← isProp expression do
        throwError "λRK bridge: relation {name} has the wrong argument count"
      return expression

/-- Quote one complete closed scalar clause. Binder order is retained even for
unused variables, matching the compiler's observation table for reconstruction. -/
def scalarClauseExpr (relations : Array (String × Lean.Expr))
    (clause : ScalarClause) : MetaM Lean.Expr :=
  go 0 #[]
where
  go (index : Nat) (variables : Array Lean.Expr) : MetaM Lean.Expr := do
    if h : index < clause.variables.size then
      let scalar :=  clause.variables[index]
      unless scalar.index == index do
        throwError "λRK bridge: scalar binder indices must be consecutive"
      withLocalDeclD (Name.mkSimple s!"scalar_{index}") (scalarSortType scalar.sort)
        fun expression => go (index + 1) (variables.push expression)
    else
      let mut body ← scalarFormulaExpr relations variables clause.head
      for guard in clause.guards.reverse do
        body ← mkArrow (← scalarFormulaExpr relations variables guard) body
      mkForallFVars variables body
  termination_by clause.variables.size - index

/-- The predicate type used by both existential synthesis slots and the runtime
assignment decoder. Value arguments are retained for residual-only relations. -/
def predicateTypeExpr (declaration : KDecl) : MetaM Lean.Expr := do
  let mut type := mkSort .zero
  for sort in declaration.args.reverse do
    let domain := match sort with
      | .int => mkConst ``Int
      | .bool => mkConst ``Bool
      | .value => mkConst ``Value
    type ← mkArrow domain type
  return type

/-- Lift a heterogeneous bundle of Lean predicates back to source κ-assignment.
Unmentioned κ names are false; duplicate declarations are rejected. The result
uses the shared semantic decoder, including its arity and runtime-sort checks. -/
def predicateAssignmentExpr (relations : Array (KDecl × Lean.Expr)) : MetaM Lean.Expr := do
  let mut names : Array String := #[]
  for (declaration, predicate) in relations do
    if names.contains declaration.name then
      throwError "λRK bridge: duplicate predicate declaration {declaration.name}"
    names := names.push declaration.name
    requireType predicate (← predicateTypeExpr declaration)
  let listValue := mkApp (mkConst ``List [0]) (mkConst ``Value)
  let mut assignment := mkLambda `name .default (mkConst ``String)
    (mkLambda `values .default listValue (mkConst ``False))
  for (declaration, predicate) in relations.reverse do
    assignment := mkApp4 (mkConst ``bindPredicate) (toExpr declaration.name)
      (toExpr declaration.args) predicate assignment
  check assignment
  return assignment

end LambdaRK.Bridge
