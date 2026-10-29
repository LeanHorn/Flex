import Benchmarks.FluxRS.MkPairsWithBound

/-! Bounded pairs using the benchmark's handwritten `@[qualif]` declarations. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem MkPairsSimple_flex : MkPairsSimple := by
  flex

#print axioms MkPairsSimple_flex
