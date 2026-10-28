import Flex.Tactic.Tactics.Flex
import Benchmarks.FluxRS.SortInsert

/-! Inserting into a sorted array. Deep scraping makes `fix` expensive: its equal
share of the budget (one sixth) is not enough, so give each step more. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem SortInsert_flex : F.SortInsert := by
  flex (scrape := deep) (config := { heartbeats := 1500000 })

#print axioms SortInsert_flex
