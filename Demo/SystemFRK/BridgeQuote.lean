import Flex.VCG.SystemFRK.Bridge.Quote
import Flex.VCG.SystemFRK.Bridge.Read
import Demo.SystemFRK
import Flex.CHC

/-! Quotation, checked reflection, and heterogeneous relation regressions.
These inspect source syntax and the shared exporter; no solver executable is
needed. End-to-end backend checks live alongside the bridge goal tests. -/
namespace SystemFRKBridgeQuoteChecks

open Lean Meta Elab SystemFRK SystemFRK.Bridge

-- The executable compiler is allowed to propose data, but its implementation
-- is not a logical authority. Deliberately disagree with kernel reduction to
-- exercise the checked conversion at the native-reflection boundary.
private def misleadingConstraintImpl : Cstr := .head (.theory .falsity)

@[implemented_by misleadingConstraintImpl]
private def misleadingConstraint : Cstr := .truth

run_elab do
  let checkedSignature ← readSignature (mkConst ``SystemFRK.Examples.signature)
  unless checkedSignature == SystemFRK.Examples.signature do
    throwError "checked source reflection changed the signature"
  let sourceConstraint : Cstr := .all "b" .bool
    (.all "n" .int (.head (.theory (.le (.int 0) (.var "n")))))
  let checkedConstraint ← readConstraint (toExpr sourceConstraint)
  unless checkedConstraint == sourceConstraint do
    throwError "checked source reflection changed a constraint"
  let signature := SystemFRK.Examples.signature
  let program := SystemFRK.Examples.map
  let type := SystemFRK.Examples.mapTy
  for (value, expected) in [
      (toExpr signature, mkConst ``SystemFRK.Examples.signature),
      (toExpr program, mkConst ``SystemFRK.Examples.map),
      (toExpr type, mkConst ``SystemFRK.Examples.mapTy)] do
    check value
    unless ← isDefEq value expected do
      throwError "reflection changed source value"
    checkWithKernel value
  let first : KDecl := ⟨"first", [.bool, .int]⟩
  let second : KDecl := ⟨"second", [.int]⟩
  withLocalDeclD `first (← predicateTypeExpr first) fun firstExpr => do
    withLocalDeclD `second (← predicateTypeExpr second) fun secondExpr => do
      let relations := #[("first", firstExpr), ("second", secondExpr)]
      let source : SourceClause := ⟨0, [], [], .theory .truth⟩
      let clause : ScalarClause := {
        source := source
        «variables» := #[⟨0, .bool, .var "b"⟩, ⟨1, .int, .var "n"⟩]
        guards := #[.rel "first" [.var 0 .bool, .var 1 .int]]
        head := .rel "second" [.add (.var 1 .int) (.int 1)] }
      let proposition ← scalarClauseExpr relations clause
      check proposition
      unless ← isProp proposition do throwError "not a proposition"
      let assignment ← predicateAssignmentExpr #[(first, firstExpr), (second, secondExpr)]
      check assignment
      unless ← isDefEq (← inferType assignment) (mkConst ``KAssignment) do
        throwError "not a source assignment"
      let mut rejected := false
      try
        discard <| scalarClauseExpr relations {clause with head := .rel "first" [.int 1]}
      catch _ => rejected := true
      unless rejected do throwError "bad arity accepted"
      rejected := false
      try
        discard <| scalarClauseExpr relations {clause with head := .eq (.var 0 .int) (.int 1)}
      catch _ => rejected := true
      unless rejected do throwError "bad sort accepted"
      let closedSecond ← mkAppM ``Exists #[← mkLambdaFVars #[secondExpr] proposition]
      let closed ← mkAppM ``Exists #[← mkLambdaFVars #[firstExpr] closedSecond]
      let goal ← mkFreshExprMVar closed
      let (_, kvars, body) ← peelExistentialsAndIntro goal.mvarId!
      let exported ← Flex.CHC.exportConstraints kvars (← body.getType)
      unless exported.relations.size == 2 do throwError "lost a relation"
      unless exported.clauseCount == 1 do throwError "changed clause count"
      unless exported.relations[0]!.argumentSorts == #[.bool, .int] &&
          exported.relations[1]!.argumentSorts == #[.int] do
        throwError "changed relation argument sorts"

run_elab do
  withLocalDeclD `signature (mkConst ``Signature) fun parameter => do
    let rejected ← try
      discard <| readSignature parameter
      pure false
    catch _ => pure true
    unless rejected do throwError "open signature was accepted"
  let unresolved ← mkFreshExprMVar (mkConst ``Cstr)
  let rejected ← try
    discard <| readConstraint unresolved
    pure false
  catch _ => pure true
  unless rejected do throwError "unresolved source constraint was accepted"

  let rejected ← try
    discard <| readConstraint (mkConst ``misleadingConstraint)
    pure false
  catch _ => pure true
  unless rejected do
    throwError "native reflection bypassed the kernel's source-syntax equality check"

end SystemFRKBridgeQuoteChecks
