import Flex.Tactic.Tactics.Flex
import Benchmarks.FluxRS.FibSumLoop

/-! A loop summing `1 … n` against a recursive specification: `fix` finds
`0 ≤ i ∧ i ≤ n ∧ total = fib_spec_sum i` from the benchmark's qualifiers. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem FibSumLoop_flex : FibSumLoop := by
  flex

#print axioms FibSumLoop_flex
