import Flex

/-! `fix`, from the standard qualifier bank to definition scraping.
The `flex_auto` examples require Z3 on PATH. -/

-- 1. Unary invariant: `0 ≤ i`, using the standard bank.
def countdownVC : Prop :=
  ∃ k : Int → Prop,
    k 5
    ∧ (∀ i, k i → 1 ≤ i → k (i - 1))
    ∧ (∀ i, k i → 0 ≤ i)

theorem countdown : countdownVC := by
  fix

-- 2. Relational invariant: `0 ≤ i ∧ i ≤ x`, using the standard bank.
def cyc0 : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x → κ ν x)
    ∧ (∀ i : Int, κ i x ∧ 1 ≤ i → ∀ ν : Int, ν = i - 1 → κ ν x)
    ∧ (∀ i : Int, κ i x → 0 ≤ i ∧ i ≤ x)

theorem cyc0_fix : cyc0 := by
  fix

-- 3. Mixed Nat/Bool invariant: `n ≤ bound ∧ enabled = true`.
theorem guarded_countdown :
  ∃ k : Nat → Nat → Bool → Prop,
    (∀ bound, k bound bound true)
    ∧ (∀ n bound enabled, k n bound enabled → enabled = true →
        0 < n → k (n - 1) bound enabled)
    ∧ (∀ n bound enabled, k n bound enabled → n ≤ bound)
    ∧ (∀ n bound enabled, k n bound enabled → enabled = false → False) := by
  fix

-- 4. Two mutually recursive predicates, both bounded by `0 ≤ i ∧ i ≤ bound`.
theorem alternating_phases :
  ∃ p q : Int → Int → Prop,
    (∀ bound, 0 ≤ bound → p 0 bound)
    ∧ (∀ i bound, p i bound → i < bound → q (i + 1) bound)
    ∧ (∀ i bound, q i bound → p i bound)
    ∧ (∀ i bound, p i bound → i ≤ bound)
    ∧ (∀ i bound, q i bound → i ≤ bound) := by
  fix

-- 5. Mixed constraints: `zap` removes acyclic predicates, then `fix` solves the loops.
namespace Mixed

-- One acyclic seed feeds a cyclic countdown.
def seededCountdown : Prop :=
  ∃ κseed : Int → Int → Prop,
  ∃ κinv  : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 2 → κseed ν x)
    ∧ (∀ v : Int, κseed v x → κinv v x)
    ∧ (∀ i : Int, κinv i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν x)
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)

theorem seededCountdown_correct : seededCountdown := by
  zap
  focus fix

-- Two acyclic seeds merge into one invariant.
def mergingSeeds : Prop :=
  ∃ κlo  : Int → Int → Prop,
  ∃ κhi  : Int → Int → Prop,
  ∃ κinv : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x     → κlo ν x)
    ∧ (∀ ν : Int, ν = x + 4 → κhi ν x)
    ∧ (∀ v : Int, κlo v x → κinv v x)
    ∧ (∀ v : Int, κhi v x → κinv v x)
    ∧ (∀ i : Int, κinv i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν x)
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)

theorem mergingSeeds_correct : mergingSeeds := by
  zap
  focus fix

-- A stride-two loop shares input with an independent output check.
def strideTwo : Prop :=
  ∃ κpre : Int → Int → Prop,
  ∃ κout : Int → Int → Prop,
  ∃ κinv : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κpre ν x)
    ∧ (∀ ν : Int, ν = x + 3 → κout ν x)
    ∧ (∀ v : Int, κpre v x → κinv v x)
    ∧ (∀ i : Int, κinv i x ∧ 2 ≤ i →
        ∀ ν : Int, ν = i - 2 → κinv ν x)
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)
    ∧ (∀ r : Int, κout r x → 3 ≤ r)

theorem strideTwo_correct : strideTwo := by
  zap
  focus fix

-- Two independent loops, one seeded through an acyclic predicate.
def independentLoops : Prop :=
  ∃ κfused : Int → Int → Prop,
  ∃ κlp1   : Int → Int → Prop,
  ∃ κlp2   : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κfused ν x)
    ∧ (∀ ν : Int, ν = x     → κlp1 ν x)
    ∧ (∀ i : Int, κlp1 i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κlp1 ν x)
    ∧ (∀ i : Int, κlp1 i x → 0 ≤ i)
    ∧ (∀ v : Int, κfused v x → κlp2 v x)
    ∧ (∀ i : Int, κlp2 i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κlp2 ν x)
    ∧ (∀ i : Int, κlp2 i x → 0 ≤ i)
    ∧ (∀ r : Int, κfused r x → 1 ≤ r)

theorem independentLoops_correct : independentLoops := by
  zap
  focus fix

-- A two-step acyclic chain feeds a loop.
def chainedSeed : Prop :=
  ∃ κa   : Int → Int → Prop,
  ∃ κb   : Int → Int → Prop,
  ∃ κfin : Int → Int → Prop,
  ∃ κinv : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κa ν x)
    ∧ (∀ v : Int, κa v x → ∀ ν : Int, ν = v + 1 → κb ν x)
    ∧ (∀ v : Int, κb v x → κinv v x)
    ∧ (∀ i : Int, κinv i x ∧ 1 ≤ i →
        ∀ ν : Int, ν = i - 1 → κinv ν x)
    ∧ (∀ i : Int, κinv i x → 0 ≤ i)
    ∧ (∀ ν : Int, ν = x + 5 → κfin ν x)
    ∧ (∀ r : Int, κfin r x → 5 ≤ r)

theorem chainedSeed_correct : chainedSeed := by
  zap
  focus fix

-- A bounded counter drives a nonnegative accumulator.
def counterAndAccumulator : Prop :=
  ∃ κseed : Int → Int → Prop,
  ∃ κhi   : Int → Int → Prop,
  ∃ κcnt  : Int → Int → Int → Prop,
  ∃ κacc  : Int → Int → Int → Prop,
    ∀ n : Int, 0 ≤ n →
      (∀ ν : Int, ν = 0 → κseed ν n)
    ∧ (∀ ν : Int, ν = n → κhi ν n)
    ∧ (∀ v : Int, κseed v n → ∀ b : Int, κhi b n → κcnt v b n)
    ∧ (∀ v : Int, κseed v n → ∀ b : Int, κhi b n → κacc v b n)
    ∧ (∀ i m : Int, κcnt i m n → i < m →
        ∀ a : Int, κacc a m n →
          (∀ ν : Int, ν = i + 1 → κcnt ν m n)
        ∧ (∀ ν : Int, ν = a + i → κacc ν m n))
    ∧ (∀ i m : Int, κcnt i m n → i ≥ m →
        ∀ a : Int, κacc a m n → 0 ≤ a)

theorem counterAndAccumulator_correct : counterAndAccumulator := by
  zap
  focus fix

-- The cyclic predicate is quantified before its acyclic seed.
def cyclicBeforeSeed : Prop :=
  ∃ κinv  : Int → Int → Int → Prop,
  ∃ κseed : Int → Int → Prop,
    ∀ n : Int, 0 ≤ n →
      (∀ ν : Int, ν = 0 → κseed ν n)
    ∧ (∀ v : Int, κseed v n → κinv v n n)
    ∧ (∀ i b : Int, κinv i b n → i < b →
        ∀ ν : Int, ν = i + 1 → κinv ν b n)
    ∧ (∀ i b : Int, κinv i b n → i ≥ b → 0 ≤ i)

theorem cyclicBeforeSeed_correct : cyclicBeforeSeed := by
  zap
  focus fix

end Mixed

-- 6. Basic scraping adds the problem's literal bound `i ≤ 5`.
theorem countdown_scraped :
  ∃ k : Int → Prop,
    k 5
    ∧ (∀ i, k i → 1 ≤ i → k (i - 1))
    ∧ (∀ i, k i → 0 ≤ i ∧ i ≤ 5) := by
  fix (scrape := basic)

-- 7. Deep scraping generalizes `a + b ≤ 5` to the invariant `a + b ≤ n`.
theorem relational_bound_scraped :
  ∃ k : Int → Int → Int → Prop,
    (∀ a b, 0 ≤ a → 0 ≤ b → a + b ≤ 5 → k a b (a + b))
    ∧ (∀ a b n, k a b n → 0 < a → k (a - 1) b n)
    ∧ (∀ a b n, k a b n → a + b ≤ 5)
    ∧ (∀ a b n, k a b n → n < a + b → False) := by
  fix (scrape := deep)

-- 8. Standard scraping discovers `fib`, including its shifted recursive calls.
@[grind]
def fib (n : Int) : Int :=
  if n ≤ 1 then 1 else fib (n - 1) + fib (n - 2)
  termination_by n.toNat

theorem fib_scraped :
  ∃ k : Int → Int → Int → Int → Prop,
    ∀ n : Int, 0 ≤ n →
      ((¬ (n ≤ 1)) →
        k 2 1 2 n
        ∧ (∀ i prev curr : Int,
            k i prev curr n →
              ((¬ (i < n)) → curr = fib n)
              ∧ ((i < n) → k (i + 1) curr (prev + curr) n)))
      ∧ ((n ≤ 1) → 1 = fib n) := by
  fix (scrape := standard)

section Oracles

set_option auto.smt.solver.name "z3"
set_option auto.smt.timeout 2

-- Try Lean first; use lean-auto if it fails.
theorem countdown_auto_fallback : countdownVC := by
  fix (oracle := flex_auto [*])

-- Prefer lean-auto for synthesis; certify with Lean.
theorem countdown_auto_synth : countdownVC := by
  fix (synth := flex_auto [*])

-- Prefer lean-auto for synthesis and lean-smt for certification.
theorem countdown_smt_proof : countdownVC := by
  fix (synth := flex_auto [*]) (proof := flex_smt [*])

end Oracles
