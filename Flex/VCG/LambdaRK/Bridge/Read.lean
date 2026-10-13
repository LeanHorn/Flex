import Flex.VCG.LambdaRK.Bridge.Reflect

/-!
Read concrete source syntax for the executable compiler. Native evaluation is
only a way to propose data: an ordinary kernel-checked reflexivity proof must
identify its constructor reflection with the original expression. No evaluated
Boolean, trusted axiom, or `native_decide` certificate is used.
-/

namespace LambdaRK.Bridge

open Lean Meta Elab

private unsafe def readClosedSyntax (α : Type) [ToExpr α]
    (expression : Lean.Expr) : TermElabM α := do
  let expression ← instantiateMVars expression
  if expression.hasFVar || expression.hasMVar || expression.hasLevelMVar ||
      expression.hasLooseBVars then
    throwError "λRK bridge: source syntax must be closed and contain no unresolved variables"
  let value ← evalExpr α (toTypeExpr α) expression
  let reflected := toExpr value
  let equality ← mkEq expression reflected
  let reflexivity ← mkEqRefl reflected
  checkWithKernel (mkExpectedPropHint reflexivity equality)
  return value

private unsafe def readSignatureImpl (expression : Lean.Expr) : TermElabM Signature :=
  readClosedSyntax Signature expression

/-- Evaluate a concrete signature, then validate its reflected value by kernel
conversion. The executable implementation is confined to elaboration. -/
@[implemented_by readSignatureImpl]
def readSignature (_expression : Lean.Expr) : TermElabM Signature :=
  throwError "λRK bridge: source reflection requires the elaborator runtime"

private unsafe def readConstraintImpl (expression : Lean.Expr) : TermElabM Cstr :=
  readClosedSyntax Cstr expression

/-- Evaluate concrete generated constraints, with the same checked conversion
boundary used for signatures. Computation never supplies a logical assumption. -/
@[implemented_by readConstraintImpl]
def readConstraint (_expression : Lean.Expr) : TermElabM Cstr :=
  throwError "λRK bridge: source reflection requires the elaborator runtime"

end LambdaRK.Bridge
