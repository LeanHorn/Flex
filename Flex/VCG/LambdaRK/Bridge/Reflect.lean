import Flex.VCG.LambdaRK.Syntax

/-!
Reflection of λRK syntax for the solver bridge. The compiler may inspect a
computed frontend value, but every source proposition is rebuilt from ordinary
constructor expressions and checked by Lean. These instances do not add axioms
or alter the source language's equality operations.
-/

namespace LambdaRK.Bridge

open Lean

private def listExpr (type : Lean.Expr) (items : List Lean.Expr) : Lean.Expr :=
  items.foldr (fun item tail => mkApp3 (mkConst ``List.cons [0]) type item tail)
    (mkApp (mkConst ``List.nil [0]) type)

instance : ToExpr LSort where
  toTypeExpr := mkConst ``LSort
  toExpr
    | .int => mkConst ``LSort.int
    | .bool => mkConst ``LSort.bool
    | .value => mkConst ``LSort.value

private def reflectTerm : LTerm → Lean.Expr
  | .var name => mkApp (mkConst ``LTerm.var) (toExpr name)
  | .int value => mkApp (mkConst ``LTerm.int) (toExpr value)
  | .bool value => mkApp (mkConst ``LTerm.bool) (toExpr value)
  | .add left right => mkApp2 (mkConst ``LTerm.add) (reflectTerm left) (reflectTerm right)
  | .ctor name fields => mkApp2 (mkConst ``LTerm.ctor) (toExpr name)
      (listExpr (mkConst ``LTerm) (fields.map reflectTerm))
  | .measure name argument =>
      mkApp2 (mkConst ``LTerm.measure) (toExpr name) (reflectTerm argument)

instance : ToExpr LTerm := ⟨reflectTerm, mkConst ``LTerm⟩

private def reflectFormula : Formula → Lean.Expr
  | .truth => mkConst ``Formula.truth
  | .falsity => mkConst ``Formula.falsity
  | .eq left right => mkApp2 (mkConst ``Formula.eq) (toExpr left) (toExpr right)
  | .le left right => mkApp2 (mkConst ``Formula.le) (toExpr left) (toExpr right)
  | .and left right =>
      mkApp2 (mkConst ``Formula.and) (reflectFormula left) (reflectFormula right)
  | .or left right =>
      mkApp2 (mkConst ``Formula.or) (reflectFormula left) (reflectFormula right)
  | .not body => mkApp (mkConst ``Formula.not) (reflectFormula body)

instance : ToExpr Formula := ⟨reflectFormula, mkConst ``Formula⟩

instance : ToExpr Atom where
  toTypeExpr := mkConst ``Atom
  toExpr
    | .theory formula => mkApp (mkConst ``Atom.theory) (toExpr formula)
    | .kvar name arguments => mkApp2 (mkConst ``Atom.kvar) (toExpr name) (toExpr arguments)

private def reflectType : Ty → Lean.Expr
  | .var index => mkApp (mkConst ``Ty.var) (toExpr index)
  | .int => mkConst ``Ty.int
  | .bool => mkConst ``Ty.bool
  | .data name arguments => mkApp2 (mkConst ``Ty.data) (toExpr name)
      (listExpr (mkConst ``Ty) (arguments.map reflectType))
  | .arrow name domain codomain =>
      mkApp3 (mkConst ``Ty.arrow) (toExpr name) (reflectType domain) (reflectType codomain)
  | .all body => mkApp (mkConst ``Ty.all) (reflectType body)
  | .refine base predicate => mkApp2 (mkConst ``Ty.refine) (reflectType base) (toExpr predicate)

instance : ToExpr Ty := ⟨reflectType, mkConst ``Ty⟩

private def reflectExpression : LambdaRK.Expr → Lean.Expr
  | .var name => mkApp (mkConst ``LambdaRK.Expr.var) (toExpr name)
  | .int value => mkApp (mkConst ``LambdaRK.Expr.int) (toExpr value)
  | .bool value => mkApp (mkConst ``LambdaRK.Expr.bool) (toExpr value)
  | .lam name domain body =>
      mkApp3 (mkConst ``LambdaRK.Expr.lam) (toExpr name) (toExpr domain) (reflectExpression body)
  | .app fn arg => mkApp2 (mkConst ``LambdaRK.Expr.app)
      (reflectExpression fn) (reflectExpression arg)
  | .letE name value body => mkApp3 (mkConst ``LambdaRK.Expr.letE)
      (toExpr name) (reflectExpression value) (reflectExpression body)
  | .tyLam body => mkApp (mkConst ``LambdaRK.Expr.tyLam) (reflectExpression body)
  | .tyApp fn argument =>
      mkApp2 (mkConst ``LambdaRK.Expr.tyApp) (reflectExpression fn) (toExpr argument)
  | .ctor name arguments fields => mkApp3 (mkConst ``LambdaRK.Expr.ctor)
      (toExpr name) (toExpr arguments)
      (listExpr (mkConst ``LambdaRK.Expr) (fields.map reflectExpression))
  | .matchE scrutinee branches =>
      let string := mkConst ``String
      let names := mkApp (mkConst ``List [0]) string
      let branchBody := mkApp2 (mkConst ``Prod [0, 0]) names (mkConst ``LambdaRK.Expr)
      let branchType := mkApp2 (mkConst ``Prod [0, 0]) string branchBody
      mkApp2 (mkConst ``LambdaRK.Expr.matchE) (reflectExpression scrutinee)
        (listExpr branchType (branches.map fun branch =>
          mkApp4 (mkConst ``Prod.mk [0, 0]) string branchBody (toExpr branch.1)
            (mkApp4 (mkConst ``Prod.mk [0, 0]) names (mkConst ``LambdaRK.Expr)
              (toExpr branch.2.1) (reflectExpression branch.2.2))))
  | .structRec name domain codomain body => mkApp4 (mkConst ``LambdaRK.Expr.structRec)
      (toExpr name) (toExpr domain) (toExpr codomain) (reflectExpression body)
  | .recur argument => mkApp (mkConst ``LambdaRK.Expr.recur) (reflectExpression argument)
  | .measure name argument =>
      mkApp2 (mkConst ``LambdaRK.Expr.measure) (toExpr name) (reflectExpression argument)
  | .ann expression type =>
      mkApp2 (mkConst ``LambdaRK.Expr.ann) (reflectExpression expression) (toExpr type)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first
    | decreasing_trivial
    | rename_i member
      rcases branch with ⟨name, binders, body⟩
      have bound := List.sizeOf_lt_of_mem member
      simp_all only [Prod.mk.sizeOf_spec, LambdaRK.Expr.matchE.sizeOf_spec]
      omega

instance : ToExpr LambdaRK.Expr := ⟨reflectExpression, mkConst ``LambdaRK.Expr⟩

instance : ToExpr CtorDecl where
  toTypeExpr := mkConst ``CtorDecl
  toExpr declaration :=
    mkApp2 (mkConst ``CtorDecl.mk) (toExpr declaration.name) (toExpr declaration.fields)

instance : ToExpr DataDecl where
  toTypeExpr := mkConst ``DataDecl
  toExpr declaration := mkApp3 (mkConst ``DataDecl.mk)
    (toExpr declaration.name) (toExpr declaration.params) (toExpr declaration.ctors)

private def reflectMeasureBody : MeasureBody → Lean.Expr
  | .literal value => mkApp (mkConst ``MeasureBody.literal) (toExpr value)
  | .field index => mkApp (mkConst ``MeasureBody.field) (toExpr index)
  | .recur index => mkApp (mkConst ``MeasureBody.recur) (toExpr index)
  | .add left right =>
      mkApp2 (mkConst ``MeasureBody.add) (reflectMeasureBody left) (reflectMeasureBody right)

instance : ToExpr MeasureBody := ⟨reflectMeasureBody, mkConst ``MeasureBody⟩

instance : ToExpr MeasureCase where
  toTypeExpr := mkConst ``MeasureCase
  toExpr branch := mkApp2 (mkConst ``MeasureCase.mk) (toExpr branch.ctor) (toExpr branch.body)

instance : ToExpr MeasureDecl where
  toTypeExpr := mkConst ``MeasureDecl
  toExpr declaration := mkApp3 (mkConst ``MeasureDecl.mk)
    (toExpr declaration.name) (toExpr declaration.datatype) (toExpr declaration.cases)

instance : ToExpr KDecl where
  toTypeExpr := mkConst ``KDecl
  toExpr declaration := mkApp2 (mkConst ``KDecl.mk)
    (toExpr declaration.name) (toExpr declaration.args)

instance : ToExpr Signature where
  toTypeExpr := mkConst ``Signature
  toExpr signature := mkApp3 (mkConst ``Signature.mk)
    (toExpr signature.datatypes) (toExpr signature.measures) (toExpr signature.kvars)

private def reflectConstraint : Cstr → Lean.Expr
  | .truth => mkConst ``Cstr.truth
  | .head atom => mkApp (mkConst ``Cstr.head) (toExpr atom)
  | .guard antecedent consequent =>
      mkApp2 (mkConst ``Cstr.guard) (toExpr antecedent) (reflectConstraint consequent)
  | .all binder sort body =>
      mkApp3 (mkConst ``Cstr.all) (toExpr binder) (toExpr sort) (reflectConstraint body)
  | .conj left right =>
      mkApp2 (mkConst ``Cstr.conj) (reflectConstraint left) (reflectConstraint right)

instance : ToExpr Cstr := ⟨reflectConstraint, mkConst ``Cstr⟩

end LambdaRK.Bridge
