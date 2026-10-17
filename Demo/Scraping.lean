import Flex

/-! Opt-in PA scraping and per-call oracle regression examples. No manual
    Fibonacci qualifiers or external solver installation are needed here. -/

namespace OracleScrape

open Lean Meta Elab Term

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

-- A failed/nonterminal backend must not count as success or modify the
-- caller's metavariables; an admitted result needs explicit trust.
run_elab do
  let no ← proveLeafWith (← `(tactic| skip)) (mkConst ``False)
  unless no.isNone do throwError "nonterminal oracle accepted"
  let no ← proveLeafWith (← `(tactic| admit)) (mkConst ``False)
  unless no.isNone do throwError "untrusted admit accepted"
  let yes ← proveLeafWith (← `(tactic| admit)) (mkConst ``False) true
  unless yes.isSome do throwError "trusted oracle rejected"
  let x ← mkFreshExprMVar (some (mkConst ``Nat))
  let goal ← mkEq x (mkNatLit 0)
  let _ ← proveLeafWith (← `(tactic| exact rfl)) goal
  if ← x.mvarId!.isAssigned then throwError "oracle assigned caller's metavariable"
  let no ← proveLeafWith (← `(tactic| (exact True.intro; fail "rollback"))) (mkConst ``True)
  unless no.isNone do throwError "failing oracle accepted"

end OracleScrape
