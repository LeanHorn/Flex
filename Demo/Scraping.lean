import Flex

/-! Qualifier scraping from constraints and recursive definitions. -/

namespace OracleScrape

theorem countdown_scraped :
  ∃ k : Int → Prop,
    k 5
    ∧ (∀ i, k i → 1 ≤ i → k (i - 1))
    ∧ (∀ i, k i → 0 ≤ i) := by
  fix (scrape := head)

@[grind]
def fib (n : Int) : Int :=
  if n ≤ 1 then 1 else fib (n - 1) + fib (n - 2)
  termination_by n.toNat

theorem fib_scraped :
  ∃ k : Int → Int → Int → Int → Prop,
      ∀ n : Int, n ≥ 0 →
        ((¬ (n ≤ 1)) →
          k 2 1 2 n
        ∧ (∀ i prev curr : Int,
            k i prev curr n →
              ((¬ (i < n)) → curr = fib n)
            ∧ ((i < n) → k (i + 1) curr (prev + curr) n)))
      ∧ ((n ≤ 1) → 1 = fib n)
 := by fix (scrape := both) (defs := [fib])

end OracleScrape
