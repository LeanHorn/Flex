import Flex.VCG.SystemFRK.Bridge.Syntax
import Flex.VCG.SystemFRK.Bridge.Reflect
import Flex.VCG.SystemFRK.Bridge.Semantics

/-! Quote scalar clauses as typed Lean propositions for the shared CHC API. -/

namespace SystemFRK.Bridge

open Lean Meta

def scalarSortType : ScalarSort → Lean.Expr
  | .int => mkConst ``Int
  | .bool => mkConst ``Bool

private def requireType (expression type : Lean.Expr) : MetaM Unit := do
  unless ← isDefEq (← inferType expression) type do
    throwError "SystemFRK bridge: expected {type}, got {expression}"

/-- Index scalar binders numerically and check each occurrence’s sort. -/
def scalarTermExpr (variables : Array Lean.Expr) : ScalarTerm → MetaM Lean.Expr
  | .var index sort => do
      let some expression := variables[index]?
        | throwError "SystemFRK bridge: unknown scalar variable {index}"
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

/-- Use the typed predicate slots quantified in the solver goal. -/
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
        | throwError "SystemFRK bridge: undeclared scalar relation {name}"
      let arguments ← arguments.toArray.mapM (scalarTermExpr variables)
      let expression := mkAppN relation arguments
      check expression
      unless ← isProp expression do
        throwError "SystemFRK bridge: relation {name} has the wrong argument count"
      return expression

/-- Quote a closed scalar clause, preserving binder order for reconstruction. -/
def scalarClauseExpr (relations : Array (String × Lean.Expr))
    (clause : ScalarClause) : MetaM Lean.Expr :=
  go 0 #[]
where
  go (index : Nat) (variables : Array Lean.Expr) : MetaM Lean.Expr := do
    if h : index < clause.variables.size then
      let scalar :=  clause.variables[index]
      unless scalar.index == index do
        throwError "SystemFRK bridge: scalar binder indices must be consecutive"
      withLocalDeclD (Name.mkSimple s!"scalar_{index}") (scalarSortType scalar.sort)
        fun expression => go (index + 1) (variables.push expression)
    else
      let mut body ← scalarFormulaExpr relations variables clause.head
      for guard in clause.guards.reverse do
        body ← mkArrow (← scalarFormulaExpr relations variables guard) body
      mkForallFVars variables body
  termination_by clause.variables.size - index

/-- Predicate type shared by synthesis slots and the runtime argument decoder. -/
def predicateTypeExpr (declaration : KDecl) : MetaM Lean.Expr := do
  let mut type := mkSort .zero
  for sort in declaration.args.reverse do
    let domain := match sort with
      | .int => mkConst ``Int
      | .bool => mkConst ``Bool
      | .value => mkConst ``Value
    type ← mkArrow domain type
  return type

/-- Lift typed predicates to a κ-assignment; undeclared names are false and duplicates are rejected. -/
def predicateAssignmentExpr (relations : Array (KDecl × Lean.Expr)) : MetaM Lean.Expr := do
  let mut names : Array String := #[]
  for (declaration, predicate) in relations do
    if names.contains declaration.name then
      throwError "SystemFRK bridge: duplicate predicate declaration {declaration.name}"
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

end SystemFRK.Bridge
