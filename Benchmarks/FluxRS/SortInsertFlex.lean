import Flex.Tactic
import Benchmarks.FluxRS.SortInsert

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem F.SortInsert_flex : F.SortInsert := by
  unfold F.SortInsert
  zap
  fix (scrape := deep)

#print axioms F.SortInsert_flex

/-- The same insertion benchmark through the unified tactic. -/
theorem F.SortInsert_unified : F.SortInsert := by
  flex (scrape := deep) (config := { heartbeats := 1500000 })

#print axioms F.SortInsert_unified
