import Flex

/-! Predicate abstraction and certificate construction with `fix`. -/

-- ─── cyc0: simplest cyclic κ — single self-loop, no acyclic κ ──────────────
-- Seeded from x (0 ≤ x), loop decrements by 1, check 0 ≤ result.
-- Expected invariant: κ[ν, x] ↦ 0 ≤ ν   (from `pc_gez` at slot 0).
@[qualif] def pc_gez (v : Int)   : Prop := 0 ≤ v
@[qualif] def pc_le  (a b : Int) : Prop := a ≤ b

def cyc0 : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x → κ ν x)                                  -- seed
    ∧ (∀ i : Int, κ i x ∧ 1 ≤ i → ∀ ν : Int, ν = i - 1 → κ ν x)  -- loop (cyclic)
    ∧ (∀ i : Int, κ i x → 0 ≤ i)                                  -- check

theorem cyc0_fix : cyc0 := by
  fix

-- ─── fibFastVC: the paper's flagship — cyclic κ with `fib` in the contract ──
-- The contract requires the return value to equal `fib n`, where `fib` is an
-- ordinary Lean def. The loop invariant
--   κ[i, prev, curr, n] ↦ prev = fib (i-1) ∧ curr = fib i ∧ i ≤ n
-- needs the `fib`-valued qualifiers below — beyond an SMT backend, but fine for
-- a Lean oracle (`grind` unfolds the `@[grind]`-tagged `fib_spec`).
@[grind]
def fib_spec (n : Int) : Int :=
  if n ≤ 1 then 1
  else fib_spec (n - 1) + fib_spec (n - 2)
  termination_by n.toNat

@[qualif] def pc_gt_one      (v : Int)   : Prop := v > 1
@[qualif] def pc_eq_fib      (v i : Int) : Prop := v = fib_spec i
@[qualif] def pc_eq_fib_pred (v i : Int) : Prop := v = fib_spec (i - 1)

def fibFastVC : Prop :=
  ∃ k : Int → Int → Int → Int → Prop,
    ∀ n : Int, n ≥ 0 →
      ((¬ (n ≤ 1)) →
        k 2 1 2 n
      ∧ (∀ i prev curr : Int,
          k i prev curr n →
            ((¬ (i < n)) → curr = fib_spec n)
          ∧ ((i < n) → k (i + 1) curr (prev + curr) n)))
    ∧ ((n ≤ 1) → 1 = fib_spec n)

theorem fibFastVC_fix : fibFastVC := by
  fix

-- The certifying bridge is kernel-re-checked: no `sorryAx`, only the standard
-- axioms (`propext`/`Classical.choice`/`Quot.sound`) that `grind`/`Int` pull in.
#print axioms cyc0_fix
#print axioms fibFastVC_fix
