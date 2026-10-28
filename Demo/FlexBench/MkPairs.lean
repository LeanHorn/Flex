import Flex.Tactic.Tactics.Flex
import Benchmarks.FluxRS.MkPairsWithBound

/-! Building a bounded vector of pairs: `zap` removes the acyclic κs and `fix`
solves the loop invariant. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem MkPairsSimple_flex : MkPairsSimple := by
  flex

#print axioms MkPairsSimple_flex
