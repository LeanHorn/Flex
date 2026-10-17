import Flex

/-! Opt-in PA scraping and per-call oracle regression examples. No manual
    Fibonacci qualifiers or external solver installation are needed here. -/

namespace OracleScrape

open Lean Meta Elab Term

@[grind]
def fib (n : Int) : Int :=
  if n ≤ 1 then 1 else fib (n - 1) + fib (n - 2)
  termination_by n.toNat

-- Definition scraping must find shifted recursive applications, close every
-- local binder, and deduplicate candidates independently of binder names.
run_elab do
  let qs ← scrapePAQualifiers (mkConst ``True) { defs := #[``fib] }
  for stx in #[← `(fun (v i : Int) => v = fib i),
               ← `(fun (v i : Int) => v = fib (i - 1)),
               ← `(fun (v i : Int) => v = fib (i - 2)),
               ← `(fun (i : Int) => ¬ i ≤ 1)] do
    let expected ← elabTerm stx none
    unless ← qs.anyM (fun q => do isDefEq expected q) do
      throwError "missing qualifier {expected}"
  for q in qs do
    if q.hasFVar || q.hasExprMVar || q.hasLooseBVars then
      throwError "scraped qualifier has escaped binders: {q}"
  let body ← elabTerm (← `(∀ n : Int, n ≤ 5 → 0 ≤ n)) none
  let heads ← scrapePAQualifiers body { mode := .head }
  let both ← scrapePAQualifiers body { mode := .both }
  unless heads.size == 1 && both.size == 2 do throwError "head/both mismatch"
  let repeated ← elabTerm (← `((∀ x : Int, 0 ≤ x) ∧ (∀ y : Int, 0 ≤ y))) none
  unless (← scrapePAQualifiers repeated { mode := .head }).size == 1 do
    throwError "alpha-equivalent qualifiers were not deduplicated"
  unless (← scrapePAQualifiers body { mode := .both, maxQualifiers := 1 }).size == 1 do
    throwError "qualifier limit ignored"
  let wide ← elabTerm (← `(∀ a b c d : Int, a + b ≤ c + d)) none
  unless (← scrapePAQualifiers wide { mode := .head }).isEmpty do
    throwError "parameter limit ignored"

def countdown : Prop := ∃ k : Int → Prop,
  k 5 ∧ (∀ i, k i → 1 ≤ i → k (i - 1)) ∧ (∀ i, k i → 0 ≤ i)

theorem countdown_scraped : countdown := by fix (scrape := head)

def fibVC : Prop :=
  ∃ k : Int → Int → Int → Int → Prop,
    ∀ n : Int, n ≥ 0 →
      ((¬ (n ≤ 1)) →
        k 2 1 2 n
      ∧ (∀ i prev curr : Int,
          k i prev curr n →
            ((¬ (i < n)) → curr = fib n)
          ∧ ((i < n) → k (i + 1) curr (prev + curr) n)))
    ∧ ((n ≤ 1) → 1 = fib n)

set_option maxHeartbeats 1000000 in
theorem fib_scraped : fibVC := by fix (scrape := both) (defs := [fib])

-- An opaque constant forces the custom oracle to contribute a global lemma
-- that the built-in PA oracle cannot discover by itself.
opaque secret : Int := 7
theorem secret_spec : secret = 7 := by native_decide

run_elab do
  let goal ← elabTerm (← `(secret = 7)) none
  if (← proveLeaf goal).isSome then throwError "example no longer requires fallback"

def needsOracle : Prop := ∃ k : Int → Prop,
  k 7 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → secret ≤ n)

theorem fallback_used : needsOracle := by
  fix (scrape := head) (oracle := simp_all only [secret_spec]; omega)

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

-- Exercise optional trust syntax without admitting the resulting theorem.
example : needsOracle := by
  fix (scrape := head) (oracle := simp_all only [secret_spec]; omega) (trust := true)

end OracleScrape
