import Flex.Preprocess.Nesting

open Lean Meta Elab Tactic

/-- Factor shared binders and guards, leaving the equivalent goal visible before `zap`. -/
elab "nest_chc" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let exposed ← whnf target
  let r ← Flex.Preprocess.Nesting.nest exposed
  let next ← mkFreshExprSyntheticOpaqueMVar r.expr
  goal.assign (← mkAppM ``Iff.mpr #[r.proof, next])
  replaceMainGoal [next.mvarId!]
