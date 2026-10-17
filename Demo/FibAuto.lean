import Flex

/-! Recursive Fibonacci with scraped qualifiers and the real lean-auto/Z3 oracle.
    The definition is deliberately not tagged `@[grind]`: `d[fib]` supplies its
    equations to SMT. Requires `z3` on PATH. -/

namespace FibAutoDemo

set_option auto.smt.timeout 2
set_option auto.smt.solver.name "z3"

def fib (n : Int) : Int :=
  if n ≤ 1 then 1 else fib (n - 1) + fib (n - 2)
  termination_by n.toNat

def memoVC : Prop := ∃ k : Int → Int → Prop,
  (∀ n, n ≤ 1 → k n 1) ∧
  (∀ n a b, ¬ n ≤ 1 → k (n - 1) a → k (n - 2) b → k n (a + b)) ∧
  (∀ n v, k n v → v = fib n)

set_option maxHeartbeats 2000000 in
theorem memo_correct : memoVC := by
  fix (scrape := head) (defs := [fib]) (oracle := flex_auto [*] d[fib])

open Lean in
run_meta do
  unless (← collectAxioms ``memo_correct).contains ``autoSMTSorry do
    throwError "expected Fibonacci to use the external SMT oracle"

end FibAutoDemo
