import Flex
set_option Elab.async false
set_option maxHeartbeats 2000000
open Lean Elab Command

elab "bench " name:str " in" cmd:command : command => do
  let errsBefore := ((← get).messages.toList.filter (·.severity == .error)).length
  let t0 ← IO.monoMsNow
  let h0 ← IO.getNumHeartbeats
  try elabCommand (← `(command| set_option maxHeartbeats 2000000 in $cmd)) catch _ => pure ()
  let h1 ← IO.getNumHeartbeats
  let t1 ← IO.monoMsNow
  let errsAfter := ((← get).messages.toList.filter (·.severity == .error)).length
  let status := if errsAfter > errsBefore then "FAIL" else "ok"
  logInfo m!"BENCHLINE {name.getString} status={status} hb={(h1-h0)/1000} ms={t1-t0}"

-- ===== replayed defs from demo/basic.lean =====
def ex1 : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x → ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

def ex2 : Prop :=
    ∃ κx : Int → Int → Int → Int → Prop, ∃ κy : Int → Int → Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ n : Int,
        n = x - 1 →
        ∀ p : Int,
          p = x + 1 →
          ( (∀ ν : Int, ν = n → κx ν x n p)
          ∧ (∀ ν : Int, ν = p → κy ν x n p)
          ∧ (∀ ν : Int, κx ν x n p → κy ν x n p)
          ∧ (∀ y : Int, κy y x n p →
              ∀ ν : Int, ν = y + 1 → 0 ≤ ν)
          )

--  solve_fixpoint

def ex3 : Prop :=
  ∃ κa : Int → Prop, ∃ κb : Int → Prop, ∃ κc : Int → Prop,
    (∀ a : Int, κa a → ∀ ν : Int, ν = a - 1 → κb ν)
  ∧ (∀ b : Int, κb b → ∀ ν : Int, ν = b + 1 → κc ν)
  ∧ (∀ ν : Int, 0 ≤ ν → κa ν)
  ∧ (∀ ν : Int, κc ν → 0 ≤ ν)

-- ex4: Three-step chain: inc → dec → inc
-- ex4 x = inc (dec (inc x))  =  x+1 ≥ 0
-- κ1 = almost-nat (0 ≤ ν-1), κ2 = nat (0 ≤ ν)
def ex4 : Prop :=
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ y : Int, κ1 y x →
        ∀ ν : Int, ν = y - 1 → κ2 ν x)
    ∧ (∀ z : Int, κ2 z x →
        ∀ ν : Int, ν = z + 1 → 0 ≤ ν)

-- ex5: Three-step chain: dec → inc → inc
-- ex5 x = inc (inc (dec x))  =  x+1 ≥ 0
-- κ1 = almost-nat (0 ≤ ν+1), κ2 = nat
def ex5 : Prop :=
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ1 ν x)
    ∧ (∀ y : Int, κ1 y x →
        ∀ ν : Int, ν = y + 1 → κ2 ν x)
    ∧ (∀ z : Int, κ2 z x →
        ∀ ν : Int, ν = z + 1 → 0 ≤ ν)

-- ex6: Two independent paths, each checked separately
-- ex6 x = (inc x, inc (dec x))  both outputs ≥ 0
-- κ1 for the `inc x` branch (trivially nat), κ2 = almost-nat for `dec x`
def ex6 : Prop :=
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν)

-- ex7: Diamond — two sources flow into one κ, then one consumer
-- ex7 x = let ys = [inc x, dec x] in inc (last ys)  ≥ 0
-- κ = almost-nat: both (x+1) and (x-1) satisfy 0 ≤ ν+1
def ex7 : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)

-- ex8: Two Nat inputs, one intermediate binder
-- ex8 (x y : Nat) = let a = dec x in a + 1 + y  ≥ 0
-- κ = almost-nat; consumer uses both κ a and 0 ≤ y
def ex8 : Prop :=
  ∃ κ : Int → Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ y : Int,
        0 ≤ y →
        (∀ ν : Int, ν = x - 1 → κ ν x y)
      ∧ (∀ a : Int, κ a x y →
          ∀ ν : Int, ν = a + 1 + y → 0 ≤ ν)

-- ex9: Four-step chain: inc → dec → inc → dec
-- ex9 x = dec (inc (dec (inc x)))  =  x  ≥ 0
-- κ1=almost-nat, κ2=nat, κ3=almost-nat, final check 0 ≤ ν
def ex9 : Prop :=
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop, ∃ κ3 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ a : Int, κ1 a x →
        ∀ ν : Int, ν = a - 1 → κ2 ν x)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → κ3 ν x)
    ∧ (∀ c : Int, κ3 c x →
        ∀ ν : Int, ν = c - 1 → 0 ≤ ν)

-- ex10: Three-way merge into one κ, stronger consumer (needs inc inc)
-- ex10 x = let ys = [dec x, x, inc x] in inc (inc (last ys))  ≥ 0
-- κ = almost-nat: weakest common refinement is 0 ≤ ν+1 (from dec x)
-- consumer: 0 ≤ y+2, follows from 0 ≤ y+1
def ex10 : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ ν : Int, ν = x     → κ ν x)
    ∧ (∀ ν : Int, ν = x + 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 2 → 0 ≤ ν)

-- ex11: Three-κ chain with multi-producer merge at κ2
-- Given 0 ≤ x, produce x into κ1. Then κ1 feeds two values (a-2) and (a+1)
-- both into κ2. κ2 feeds into κ3 via +2. κ3 must be ≥ 0.
-- κ1(z) = 0 ≤ z, κ2(z) = 0 ≤ z + 2 (weakest from a-2 path), κ3(z) = 0 ≤ z
def ex11 : Prop :=
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop, ∃ κ3 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x → κ1 ν x)
    ∧ (∀ a : Int, κ1 a x →
          (∀ ν : Int, ν = a - 2 → κ2 ν x)
        ∧ (∀ ν : Int, ν = a + 1 → κ2 ν x))
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 2 → κ3 ν x)
    ∧ (∀ c : Int, κ3 c x → 0 ≤ c)

-- ex12: Four-κ diamond — two independent processing paths rejoin at κ3
-- Given 0 ≤ x:
--   Path 1: (x-1) → κ1, then κ1 → (+3) → κ3
--   Path 2: (x+1) → κ2, then κ2 → (-1) → κ3
-- κ3 feeds into κ4 via identity, κ4 must be ≥ 0.
-- κ1(z) = 0 ≤ z+1, κ2(z) = 0 ≤ z-1
-- Path 1 into κ3: z = a+3 where 0≤a+1 → z ≥ 2
-- Path 2 into κ3: z = b-1 where 0≤b-1 → z ≥ 0
-- κ3(z) = 0 ≤ z (disjunction, weaker path dominates)
-- κ4(z) = 0 ≤ z
def ex12 : Prop :=
  ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
  ∃ κ3 : Int → Int → Prop, ∃ κ4 : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x + 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x →
        ∀ ν : Int, ν = a + 3 → κ3 ν x)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b - 1 → κ3 ν x)
    ∧ (∀ c : Int, κ3 c x →
        ∀ ν : Int, ν = c → κ4 ν x)
    ∧ (∀ d : Int, κ4 d x → 0 ≤ d)

-- ex13: 3-κ chain with nested binders and cross-flow
-- Given 0 ≤ x, let a = x-1, b = x+1:
--   a → κ1, b → κ2, κ1 flows into κ2 (cross-flow)
--   κ2 → (+1) → κ3, κ3 must be ≥ 0
-- κ1(z) = 0 ≤ z+1, κ2(z) = 0 ≤ z+1 (disjunction of b and κ1), κ3(z) = 0 ≤ z
def ex13 : Prop :=
  ∃ κ1 : Int → Int → Int → Int → Prop,
  ∃ κ2 : Int → Int → Int → Int → Prop,
  ∃ κ3 : Int → Int → Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ a : Int,
        a = x - 1 →
        ∀ b : Int,
          b = x + 1 →
          (∀ ν : Int, ν = a → κ1 ν x a b)
        ∧ (∀ ν : Int, ν = b → κ2 ν x a b)
        ∧ (∀ v : Int, κ1 v x a b → κ2 v x a b)
        ∧ (∀ y : Int, κ2 y x a b →
            ∀ ν : Int, ν = y + 1 → κ3 ν x a b)
        ∧ (∀ z : Int, κ3 z x a b → 0 ≤ z)

-- ex14: 4-κ chain with nested binders, cross-flow, and merge
-- Given 0 ≤ x, let a = x-1, b = x+1, c = x:
--   a → κ1, b → κ2, κ1 flows into κ2 (cross-flow)
--   κ2 → (+1) → κ3, also c → κ3 directly (merge at κ3)
--   κ3 → (+2) → κ4, κ4 must be ≥ 0
-- κ1(z) = 0 ≤ z+1
-- κ2(z) = 0 ≤ z+1 (disjunction: b gives 0≤z-1, κ1 gives 0≤z+1; weaker wins)
-- κ3(z) = 0 ≤ z (merge: κ2 path gives 0≤z, c path gives 0≤z; both yield 0≤z)
-- κ4(z) = 0 ≤ z (from w+2 where 0≤w, z≥2≥0)
def ex14 : Prop :=
  ∃ κ1 : Int → Int → Int → Int → Int → Prop,
  ∃ κ2 : Int → Int → Int → Int → Int → Prop,
  ∃ κ3 : Int → Int → Int → Int → Int → Prop,
  ∃ κ4 : Int → Int → Int → Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ a : Int,
        a = x - 1 →
        ∀ b : Int,
          b = x + 1 →
          ∀ c : Int,
            c = x →
            (∀ ν : Int, ν = a → κ1 ν x a b c)
          ∧ (∀ ν : Int, ν = b → κ2 ν x a b c)
          ∧ (∀ v : Int, κ1 v x a b c → κ2 v x a b c)
          ∧ (∀ y : Int, κ2 y x a b c →
              ∀ ν : Int, ν = y + 1 → κ3 ν x a b c)
          ∧ (∀ ν : Int, ν = c → κ3 ν x a b c)
          ∧ (∀ w : Int, κ3 w x a b c →
              ∀ ν : Int, ν = w + 2 → κ4 ν x a b c)
          ∧ (∀ z : Int, κ4 z x a b c → 0 ≤ z)

-- Nat refinement: predecessor is less than input
def ex_nat : Prop :=
  ∃ κ : Nat → Nat → Prop,
    ∀ n : Nat,
      0 < n →
      (∀ m : Nat, m = n - 1 → κ m n)
    ∧ (∀ m : Nat, κ m n → m < n)

-- Bool-sorted κ: tracking a boolean property
def ex_bool : Prop :=
  ∃ κ : Bool → Int → Prop,
    ∀ x : Int,
      0 < x →
      (∀ b : Bool, b = decide (x > 0) → κ b x)
    ∧ (∀ b : Bool, κ b x → b = true)

@[grind]
structure Point where
  x : Int
  y : Int

def ex_pair : Prop :=
  ∃ κ : Point → Prop,
    ∀ a : Int,
      0 ≤ a →
      ∀ b : Int,
        0 ≤ b →
        (∀ p : Point, p = ⟨a, b⟩ → κ p)
      ∧ (∀ p : Point, κ p → 0 ≤ p.x ∧ 0 ≤ p.y)

def ex_prod : Prop :=
  ∃ κ : (Int × Int) → Prop,
    ∀ a : Int,
      0 ≤ a →
      ∀ b : Int,
        0 ≤ b →
        (∀ p : Int × Int, p = (a, b) → κ p)
      ∧ (∀ p : Int × Int, κ p → 0 ≤ p.1 ∧ 0 ≤ p.2)

-- User-defined function in refinement
@[simp]
def double (x : Int) : Int := x + x

def ex_userfn : Prop :=
  ∃ κ : Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = double x → κ x ν)
    ∧ (∀ y : Int, κ x y → 0 ≤ y)

-- ex_stress: 5-κ extreme test — chain + diamond + 3-way merge + cross-flow + nested binders
--
-- Topology (10 conjuncts):
--   κ1: 2-way merge        (a=x-1) and (b=x+2) both feed κ1
--   κ2: chain from κ1      κ1(v) → v-1 → κ2
--   κ3: 3-way merge        κ2(w) via +1, κ1 cross-flow, direct x → κ3
--   κ4: chain from κ3      κ3(u) → u+1 → κ4
--   κ5: 2-way merge        κ4 identity + κ3 via +2 → κ5
--   consumer: κ5(s) ⇒ 0 ≤ s
--
-- Dependency graph (DAG, no cycles):
--   κ1 ──→ κ2 ──→ κ3 ──→ κ4 ──→ κ5 ──→ 0 ≤ s
--   κ1 ─────────→ κ3 ─────────→ κ5
--          (cross-flow)    (diamond)
--              x ──→ κ3
--             (direct)
--
-- Solutions (strongest refinements):
--   κ1(z) ≡ 0 ≤ z + 1     weakest producer: a = x-1
--   κ2(z) ≡ 0 ≤ z + 2     from κ1(v) with v = z+1: 0 ≤ (z+1)+1
--   κ3(z) ≡ 0 ≤ z + 1     three paths all give z ≥ -1
--     path κ2+1: w=z-1, 0≤w+2 → 0≤z+1 ✓
--     path κ1:   v=z,   0≤v+1 → 0≤z+1 ✓
--     path x:    z=x,   0≤x   → 0≤z   ✓ (strictly stronger, disjunction stays 0≤z+1)
--   κ4(z) ≡ 0 ≤ z         from κ3(u) with z=u+1: 0≤u+1 → 0≤z
--   κ5(z) ≡ 0 ≤ z         both paths give z ≥ 0
--     path κ4:   t=z,   0≤t → 0≤z       ✓
--     path κ3+2: u=z-2, 0≤u+1 → 0≤z-1 → z≥1≥0 ✓
--
-- Final: κ5(s) ⇒ 0 ≤ s  →  0 ≤ s ⇒ 0 ≤ s  ✓
def ex_stress : Prop :=
  ∃ κ1 : Int → Int → Int → Int → Prop,
  ∃ κ2 : Int → Int → Int → Int → Prop,
  ∃ κ3 : Int → Int → Int → Int → Prop,
  ∃ κ4 : Int → Int → Int → Int → Prop,
  ∃ κ5 : Int → Int → Int → Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      ∀ a : Int,
        a = x - 1 →
        ∀ b : Int,
          b = x + 2 →
          -- κ1: 2-way merge
          (∀ ν : Int, ν = a → κ1 ν x a b)
        ∧ (∀ ν : Int, ν = b → κ1 ν x a b)
          -- κ2: chain from κ1 via -1
        ∧ (∀ v : Int, κ1 v x a b →
            ∀ ν : Int, ν = v - 1 → κ2 ν x a b)
          -- κ3: 3-way merge (κ2 chain, κ1 cross-flow, direct)
        ∧ (∀ w : Int, κ2 w x a b →
            ∀ ν : Int, ν = w + 1 → κ3 ν x a b)
        ∧ (∀ v : Int, κ1 v x a b → κ3 v x a b)
        ∧ (∀ ν : Int, ν = x → κ3 ν x a b)
          -- κ4: chain from κ3 via +1
        ∧ (∀ u : Int, κ3 u x a b →
            ∀ ν : Int, ν = u + 1 → κ4 ν x a b)
          -- κ5: diamond merge (κ4 identity + κ3 via +2)
        ∧ (∀ t : Int, κ4 t x a b → κ5 t x a b)
        ∧ (∀ u : Int, κ3 u x a b →
            ∀ ν : Int, ν = u + 2 → κ5 ν x a b)
          -- consumer
        ∧ (∀ s : Int, κ5 s x a b → 0 ≤ s)


-- ===== benchmarked proof pairs =====
bench "ex1_A" in
theorem ex1_A_bench : ex1 := by
  unfold ex1
  solve_fixpoint

bench "ex1_B" in
theorem ex1_B_bench : ex1 := by
  unfold ex1
  zap
  all_goals solve_fixpoint

bench "ex2_A" in
theorem ex2_A_bench : ex2 := by
  unfold ex2
  solve_fixpoint

bench "ex2_B" in
theorem ex2_B_bench : ex2 := by
  unfold ex2
  zap
  all_goals solve_fixpoint

bench "ex3_A" in
theorem ex3_A_bench : ex3 := by
  unfold ex3
  solve_fixpoint

bench "ex3_B" in
theorem ex3_B_bench : ex3 := by
  unfold ex3
  zap
  all_goals solve_fixpoint

bench "ex4_A" in
theorem ex4_A_bench : ex4 := by
  unfold ex4
  solve_fixpoint

bench "ex4_B" in
theorem ex4_B_bench : ex4 := by
  unfold ex4
  zap
  all_goals solve_fixpoint

bench "ex5_A" in
theorem ex5_A_bench : ex5 := by
  unfold ex5
  solve_fixpoint

bench "ex5_B" in
theorem ex5_B_bench : ex5 := by
  unfold ex5
  zap
  all_goals solve_fixpoint

bench "ex6_A" in
theorem ex6_A_bench : ex6 := by
  unfold ex6
  solve_fixpoint

bench "ex6_B" in
theorem ex6_B_bench : ex6 := by
  unfold ex6
  zap
  all_goals solve_fixpoint

bench "ex7_A" in
theorem ex7_A_bench : ex7 := by
  unfold ex7
  solve_fixpoint

bench "ex7_B" in
theorem ex7_B_bench : ex7 := by
  unfold ex7
  zap
  all_goals solve_fixpoint

bench "ex8_A" in
theorem ex8_A_bench : ex8 := by
  unfold ex8
  solve_fixpoint

bench "ex8_B" in
theorem ex8_B_bench : ex8 := by
  unfold ex8
  zap
  all_goals solve_fixpoint

bench "ex9_A" in
theorem ex9_A_bench : ex9 := by
  unfold ex9
  solve_fixpoint

bench "ex9_B" in
theorem ex9_B_bench : ex9 := by
  unfold ex9
  zap
  all_goals solve_fixpoint

bench "ex10_A" in
theorem ex10_A_bench : ex10 := by
  unfold ex10
  solve_fixpoint

bench "ex10_B" in
theorem ex10_B_bench : ex10 := by
  unfold ex10
  zap
  all_goals solve_fixpoint

bench "ex11_A" in
theorem ex11_A_bench : ex11 := by
  unfold ex11
  solve_fixpoint

bench "ex11_B" in
theorem ex11_B_bench : ex11 := by
  unfold ex11
  zap
  all_goals solve_fixpoint

bench "ex12_A" in
theorem ex12_A_bench : ex12 := by
  unfold ex12
  solve_fixpoint

bench "ex12_B" in
theorem ex12_B_bench : ex12 := by
  unfold ex12
  zap
  all_goals solve_fixpoint

bench "ex13_A" in
theorem ex13_A_bench : ex13 := by
  unfold ex13
  solve_fixpoint

bench "ex13_B" in
theorem ex13_B_bench : ex13 := by
  unfold ex13
  zap
  all_goals solve_fixpoint

bench "ex14_A" in
theorem ex14_A_bench : ex14 := by
  unfold ex14
  solve_fixpoint

bench "ex14_B" in
theorem ex14_B_bench : ex14 := by
  unfold ex14
  zap
  all_goals solve_fixpoint

bench "ex_nat_A" in
theorem ex_nat_A_bench : ex_nat := by
  unfold ex_nat
  solve_fixpoint

bench "ex_nat_B" in
theorem ex_nat_B_bench : ex_nat := by
  unfold ex_nat
  zap
  all_goals solve_fixpoint

bench "ex_bool_A" in
theorem ex_bool_A_bench : ex_bool := by
  unfold ex_bool
  solve_fixpoint

bench "ex_bool_B" in
theorem ex_bool_B_bench : ex_bool := by
  unfold ex_bool
  zap
  all_goals solve_fixpoint

bench "ex_pair_A" in
theorem ex_pair_A_bench : ex_pair := by
  unfold ex_pair
  solve_fixpoint

bench "ex_pair_B" in
theorem ex_pair_B_bench : ex_pair := by
  unfold ex_pair
  zap
  all_goals solve_fixpoint

bench "ex_prod_A" in
theorem ex_prod_A_bench : ex_prod := by
  unfold ex_prod
  solve_fixpoint

bench "ex_prod_B" in
theorem ex_prod_B_bench : ex_prod := by
  unfold ex_prod
  zap
  all_goals solve_fixpoint

bench "ex_userfn_A" in
theorem ex_userfn_A_bench : ex_userfn := by
  unfold ex_userfn
  solve_fixpoint

bench "ex_userfn_B" in
theorem ex_userfn_B_bench : ex_userfn := by
  unfold ex_userfn
  zap
  all_goals solve_fixpoint

bench "ex_stress_A" in
theorem ex_stress_A_bench : ex_stress := by
  unfold ex_stress
  solve_fixpoint

bench "ex_stress_B" in
theorem ex_stress_B_bench : ex_stress := by
  unfold ex_stress
  zap
  all_goals solve_fixpoint
