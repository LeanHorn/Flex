import Benchmarks.FluxRS.FibSumLoop

/-! Recursive summation using the benchmark's handwritten `@[qualif]` declarations,
including `total = fib_spec_sum i`. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem FibSumLoop_flex : FibSumLoop := by
  flex

#print axioms FibSumLoop_flex
