import Flex.CHC.Fragment
import Qq

namespace Flex.CHC.Prepare

open Lean Meta Qq

/-- Expose only beta/let/metadata wrappers. In particular, do not unfold `Int.le`
to `Int.NonNeg`, which a generic SMT query builder would declare as a new predicate. -/
partial def expose (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData.headBeta
  match expression with
  | .letE _ _ value body _ => expose (body.instantiate1 value)
  | _ => return expression

private def canonical (original expected : Expr) : MetaM Unit := do
  unless ← isDefEq original expected do
    throwError "CHC export: nonstandard operator instance in {original}"

/-- lean-smt's integer recognizers erase typeclass instances. Check that those
instances really denote the standard operations before handing terms to it. -/
private def checkIntegerInstance (e : Expr) : MetaM Unit := do
  let int := mkConst ``Int
  if let some n := e.natLitOf? int then
    canonical e (mkIntLit n)
  else if let some a := e.negOf? int then
    let a : Q(Int) := a
    canonical e q(-$a)
  else
    let operators := #[e.hAddOf? int int, e.hSubOf? int int, e.hMulOf? int int,
      e.leOf? int, e.ltOf? int, e.geOf? int, e.gtOf? int]
    for arguments in operators, i in [:operators.size] do
      if let some (a, b) := arguments then
        let a : Q(Int) := a
        let b : Q(Int) := b
        let expected := #[q($a + $b), q($a - $b), q($a * $b),
          q($a ≤ $b), q($a < $b), q($a ≥ $b), q($a > $b)][i]!
        canonical e expected

/-- Normalize local lets while checking the source-level restrictions. Quantifiers
are handled by `clause`, never hidden inside theory terms or guards. -/
partial def atom (input : Expr) : MetaM Expr := do
  let e ← expose input
  checkIntegerInstance e
  if e.beq?.isSome || e.bne?.isSome then
    throwError "CHC export: BEq comparisons are unsupported; use propositional equality"
  match e with
  | .forallE .. | .lam .. =>
    throwError "CHC export: quantifiers must be clause binders; higher-order terms are unsupported"
  | .app .. =>
    let head := e.getAppFn
    let args ← e.getAppArgs.mapM atom
    return mkAppN head args
  | .mvar .. => throwError "CHC export: unresolved metavariable {e}"
  | _ => return e

/-- Move value binders ahead of guards, retaining guard order and proof premises.
All variables receive disjoint generated names. Unused value binders can be
removed because Int, Bool, and Prop are nonempty; unused relation arguments remain
part of the relation's declared signature. -/
partial def clause (input : Expr) : MetaM Expr :=
  go input #[] #[]
where
  go (input : Expr) (variables guards : Array Expr) : MetaM Expr := do
    let e ← expose input
    if let .forallE _ domain body _ := e then
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError "CHC export: constraints depending on proof terms are unsupported"
        let guard ← atom domain
        withLocalDeclD `guard domain fun proof =>
          go (body.instantiate1 proof) variables (guards.push guard)
      else
        discard <| Fragment.valueSort domain
        withLocalDeclD (Name.mkSimple s!"v_{variables.size}") domain fun binder =>
          go (body.instantiate1 binder) (variables.push binder) guards
    else
      let mut result ← atom e
      for guard in guards.reverse do result ← mkArrow guard result
      mkForallFVars variables result (usedOnly := true)

end Flex.CHC.Prepare
