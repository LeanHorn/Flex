import Lean

open Lean Meta

namespace PAScrape

private def numericLiteral (ty e : Expr) : MetaM Bool := do
  if ty.isConstOf ``Nat then return (← getNatValue? e).isSome
  return (← getIntValue? e).isSome

/-- Propose at most three variants of a closed numeric qualifier.
    Replace a literal bound with a parameter, or propose `≤` from `<`.
    These are candidates for PA to check, not proved implications. -/
def deepScrapeVariants (q : Expr) : MetaM (Array Expr) := do
  if q.hasFVar || q.hasMVar || q.hasLooseBVars then return #[]
  lambdaTelescope q fun xs body => do
    let body := body.consumeMData.headBeta
    let fn := body.getAppFn
    let some name := fn.constName? | return #[]
    let args := body.getAppArgs
    let arity :=
      if name == ``Eq then 3
      else if name == ``LE.le || name == ``LT.lt then 4
      else if name == ``Nat.le || name == ``Nat.lt ||
          name == ``Int.le || name == ``Int.lt then 2
      else 0
    if arity == 0 || args.size != arity then return #[]
    let lhs := args[arity - 2]!
    let rhs := args[arity - 1]!
    let ty ← whnf (← inferType lhs)
    unless ty.isConstOf ``Nat || ty.isConstOf ``Int do return #[]
    let mut variants := #[]
    if name == ``LT.lt || name == ``Nat.lt || name == ``Int.lt then
      let rel := if ty.isConstOf ``Nat then ``Nat.le else ``Int.le
      let weaker := mkApp2 (mkConst rel) lhs rhs
      variants := variants.push (← mkLambdaFVars xs (← instantiateMVars weaker))
    for i in #[arity - 2, arity - 1] do
      if ← numericLiteral ty args[i]! then
        let variant ← withLocalDeclD `bound ty fun bound =>
          mkLambdaFVars (xs.push bound) (mkAppN fn (args.set! i bound))
        variants := variants.push variant
    return variants

end PAScrape
