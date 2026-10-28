import Flex.Tactic.Tactics.Flex
import Benchmarks.FluxRS.SortInsertionSort

/-! Insertion sort: the sortedness invariant needs qualifiers scraped from the
specification's definitions. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem SortInsertionSort_flex : F.SortInsertionSort := by
  flex (scrape := deep)

#print axioms SortInsertionSort_flex
