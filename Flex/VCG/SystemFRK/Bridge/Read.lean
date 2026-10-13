import Flex.VCG.SystemFRK.Bridge.Reflect

/-! Native evaluation proposes syntax; kernel-checked reflection identifies it
with the original term. Native computation supplies no proof. -/

namespace SystemFRK.Bridge

open Lean Meta Elab

private unsafe def readClosedSyntax (α : Type) [ToExpr α]
    (expression : Lean.Expr) : TermElabM α := do
  let expression ← instantiateMVars expression
  if expression.hasFVar || expression.hasMVar || expression.hasLevelMVar ||
      expression.hasLooseBVars then
    throwError "SystemFRK bridge: source syntax must be closed and contain no unresolved variables"
  let value ← evalExpr α (toTypeExpr α) expression
  let reflected := toExpr value
  let equality ← mkEq expression reflected
  let reflexivity ← mkEqRefl reflected
  checkWithKernel (mkExpectedPropHint reflexivity equality)
  return value

private unsafe def readSignatureImpl (expression : Lean.Expr) : TermElabM Signature :=
  readClosedSyntax Signature expression

/-- Evaluate a closed signature and check its reflection by kernel conversion. -/
@[implemented_by readSignatureImpl]
def readSignature (_expression : Lean.Expr) : TermElabM Signature :=
  throwError "SystemFRK bridge: source reflection requires the elaborator runtime"

private unsafe def readConstraintImpl (expression : Lean.Expr) : TermElabM Cstr :=
  readClosedSyntax Cstr expression

/-- Evaluate a closed constraint and check its reflection by kernel conversion. -/
@[implemented_by readConstraintImpl]
def readConstraint (_expression : Lean.Expr) : TermElabM Cstr :=
  throwError "SystemFRK bridge: source reflection requires the elaborator runtime"

end SystemFRK.Bridge
