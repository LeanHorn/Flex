import Flex.Tactic
import Benchmarks.FluxRS.SortInsert

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem F.SortInsert_flex : F.SortInsert := by
  unfold F.SortInsert
  zap
  fix (scrape := deep)

#print axioms F.SortInsert_flex
