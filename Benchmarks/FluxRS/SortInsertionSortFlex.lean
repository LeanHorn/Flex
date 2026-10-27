import Flex.Tactic
import Benchmarks.FluxRS.SortInsertionSort

/-!
Fix proves this; Spacer and Eldarica find no invariant.

Needed invariant (written by hand as `inv_sort` in flex-benchmarks):
  k0 n arr len old oldLen := 0 < n ∧ n ≤ len ∧ len = oldLen ∧ sorted arr 0 n
`sorted`, `sorted_exc` = `sort_is_sorted_between`, `sort_is_sorted_between_exc` (∀ i j over the array).

Spacer/Eldarica treat each `sorted …` as an unknown Bool, so they cannot show:
  init: sorted old 0 1                              -- true for every array
  step: sorted arr 0 n → sorted_exc arr 0 (n+1) n   -- the insert precondition

Fix copies `sorted v 0 (n+1)` from the VC, turns it into the candidate `sorted arr 0 n`,
and proves init and step in Lean from the definition.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem F.SortInsertionSort_flex : F.SortInsertionSort := by
  unfold F.SortInsertionSort
  fix (scrape := deep)

#print axioms F.SortInsertionSort_flex
