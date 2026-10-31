import Flex
import Benchmarks.Imp

/-! All 15 successful Imp cases: generated VCs, automatic scraping, no supplied invariants. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace ImpBench.SumRange

theorem inferred (n : Nat) : generated n := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.SumRange

namespace ImpBench.SumSquares

theorem inferred (n : Nat) : generated n := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.SumSquares

namespace ImpBench.ArithmeticProgression

theorem inferred (a d : Int) (n : Nat) : generated a d n := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.ArithmeticProgression

namespace ImpBench.Multiply

theorem inferred (a b : Nat) : generated a b := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.Multiply

namespace ImpBench.Power

theorem inferred (base exponent : Nat) : generated base exponent := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.Power

namespace ImpBench.Fibonacci

theorem inferred (n : Nat) : generated n := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.Fibonacci

namespace ImpBench.Divide

theorem inferred (a b : Nat) : generated a b := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.Divide

namespace ImpBench.ListSum

theorem inferred (input : List Int) : generated input := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.ListSum

namespace ImpBench.CountPredicate

theorem inferred (input : List Int) (p : Int → Bool) : generated input p := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.CountPredicate

namespace ImpBench.AllPredicate

theorem inferred (input : List Int) (p : Int → Bool) : generated input p := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.AllPredicate

namespace ImpBench.CopyList

theorem inferred (input : List Int) : generated input := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.CopyList

namespace ImpBench.MapList

theorem inferred (input : List Int) (f : Int → Int) : generated input f := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.MapList

namespace ImpBench.ReverseList

theorem inferred (input : List Int) : generated input := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.ReverseList

namespace ImpBench.FilterList

theorem inferred (input : List Int) (p : Int → Bool) : generated input p := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.FilterList

namespace ImpBench.StablePartition

theorem inferred (input : List Int) (p : Int → Bool) : generated input p := by
  imp_prepare
  fix (scrape := deep)

end ImpBench.StablePartition
