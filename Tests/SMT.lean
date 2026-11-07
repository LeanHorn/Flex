import Flex.PA.Smt

/-! Exact SMT encoding (`Flex.SMT`) as used by the PA synthesis oracle. -/

namespace SMTEncodingTests

open Lean Meta Elab Term

private structure Buffer where
  values : Int → Int
  bound : Int

private structure Box (α : Type) where
  val : α

private abbrev Map (α β : Type) := α → β
private abbrev Map.store (m : Map Int Int) (k v : Int) : Map Int Int :=
  fun x => if x == k then v else m x

private def double (x : Int) : Int := x + x
private def limit : Int := 18446744073709551615
private def square (x : Int) : Int := x * x
private def allPositive (f : Int → Int) (n : Int) : Prop := ∀ i, 0 ≤ i → i < n → 0 < f i
private def sumTo : Nat → Int
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

private def decide (input : TSyntax `term) : TermElabM PASynthResult := do
  let target ← elabTerm input none
  synthesizeSyntheticMVarsNoPostponing
  return (← Flex.PA.smtOracle 2000 #[← instantiateMVars target])[0]!

private def isUnknown : PASynthResult → Bool
  | .unknown _ => true
  | _ => false

private def expect (input : TSyntax `term) (expected : PASynthResult) : TermElabM Unit := do
  let actual ← decide input
  unless actual == expected do
    throwError "expected {repr expected}, got {repr actual} for{indentD input}"

private def expectUnknown (input : TSyntax `term) : TermElabM Unit := do
  let actual ← decide input
  unless isUnknown actual do throwError "expected unknown, got {repr actual} for{indentD input}"

-- Arrays: function-valued inputs, `store` updates, constant arrays and extensionality.
run_elab do
  expect (← `(∀ (m : Map Int Int) (k v : Int), Map.store m k v k = v)) .valid
  expect (← `(∀ (m : Map Int Int) (k v j : Int), j ≠ k → Map.store m k v j = m j)) .valid
  expect (← `(∀ (m : Map Int Int) (k v : Int), Map.store m k v = m)) .invalid
  expect (← `(∀ (f : Int → Int), (fun _ : Int => (3 : Int)) = f → f 7 = 3)) .valid
  -- Extensionality needs the quantified premise, which is omitted unless quantifiers are encoded.
  expectUnknown (← `(∀ (f g : Int → Bool), (∀ x, f x = g x) → f = g))
  expect (← `(∀ (p : Int → Prop) (x : Int), p x → p x)) .valid

-- Records, Option and parametric structures are monomorphized datatypes.
run_elab do
  expect (← `(∀ (b : Buffer) (x : Int), (Buffer.mk b.values x).bound = x)) .valid
  expect (← `(∀ (b c : Buffer), b.bound = c.bound → b = c)) .invalid
  expect (← `(∀ (b c : Buffer), b.bound = c.bound → b.values = c.values → b = c)) .valid
  expect (← `(∀ (o : Option Int) (x : Int), o = some x → o ≠ none)) .valid
  expect (← `(∀ (b : Box Int) (c : Box Bool), b.val + 0 = b.val ∧ (c.val = true ∨ c.val = false)))
    .valid
  expect (← `(∀ (p : Int × Int), p.1 = p.2 → p = (p.2, p.1))) .valid
  expect (← `(∀ (xs : List Int) (x : Int), x :: xs ≠ [])) .valid

-- Definitions: interpreted unless recursive, flagged, or using a construct not encoded.
run_elab do
  expect (← `(∀ x : Int, double x = 2 * x)) .valid
  expect (← `(∀ x : Int, double x = 3 * x)) .invalid
  expect (← `(limit = 18446744073709551615)) .valid
  withOptions (·.setBool `flex.smt.uninterpretedDefs true) do
    expectUnknown (← `(∀ x : Int, double x = 2 * x))
    expect (← `(∀ x y : Int, x = y → double x = double y)) .valid
  -- Recursive definitions are always uninterpreted.
  expectUnknown (← `(sumTo 0 = 0))
  expect (← `(∀ n m : Nat, n = m → sumTo n = sumTo m)) .valid
  -- A quantified body makes the definition uninterpreted unless quantifiers are encoded.
  expect (← `(∀ f n, allPositive f n → allPositive f n)) .valid
  expectUnknown (← `(∀ f n, allPositive f n → n ≤ 0 ∨ 0 < f 0))
  withOptions (·.setBool `flex.smt.encodeQuantifiers true) do
    expect (← `(∀ f n, allPositive f n → n ≤ 0 ∨ 0 < f 0)) .valid
  -- Likewise a non-linear body.
  expect (← `(∀ x : Int, square x = square x)) .valid
  expectUnknown (← `(∀ x : Int, 0 ≤ square x))
  withOptions (·.setBool `flex.smt.encodeNonlinear true) do
    expect (← `(∀ x : Int, 0 ≤ square x)) .valid

-- Non-linear queries bail unless encoded; Lean's division by zero is kept exactly.
run_elab do
  expectUnknown (← `(∀ x y : Int, x * y = y * x))
  expect (← `(∀ x : Int, 3 * x = x * 3)) .valid
  expect (← `(∀ x : Int, x / 0 = 0 ∧ x % 0 = x)) .valid
  expect (← `(∀ x : Int, (-7 : Int) / 2 = -4 ∧ (7 : Int) % (-2) = 1)) .valid
  withOptions (·.setBool `flex.smt.encodeNonlinear true) do
    expect (← `(∀ x y : Int, x * y = y * x)) .valid
    expect (← `(∀ x y : Int, y = 0 → x / y = 0 ∧ x % y = x)) .valid

-- Operator notation unfolds through its instances to theory operations, exactly.
run_elab do
  expect (← `(∀ x y : Int, min x y ≤ max x y)) .valid
  expect (← `(∀ x y : Int, min x y = x)) .invalid
  expect (← `(∀ x y : Int, x > y → x ≥ y)) .valid
  expect (← `(∀ x y : Int, x ≥ y → x > y)) .invalid
  expect (← `(∀ x y : Int, (x == y) = true → x = y)) .valid
  expect (← `(∀ x y : Int, (x != y) = true → x ≠ y)) .valid
  expect (← `(∀ x : Int, -x + x = 0 ∧ x - 3 < x)) .valid
  expect (← `(∀ n : Nat, min n 3 ≤ 3 ∧ n + 1 > 0)) .valid
  expect (← `(∀ n : Nat, max n 3 = n)) .invalid

-- Nat is a nonnegative Int, with truncated subtraction.
run_elab do
  expect (← `(∀ n m : Nat, n - m ≤ n)) .valid
  expect (← `(∀ n m : Nat, n - m + m = n)) .invalid
  expect (← `(∀ n : Nat, (n : Int) ≥ 0)) .valid
  expect (← `(∀ x : Int, (x.toNat : Int) ≥ x)) .valid
  -- Nat values inside arrays may be negative in SMT: such a sat is inconclusive.
  expectUnknown (← `(∀ f : Nat → Nat, f 0 = 1))

-- Quantifiers: clause variables become constants. Quantifiers the solver can skolemize, existentials
-- in premises and universals in the head, are always encoded; others need the flag.
run_elab do
  -- Existential premises, including under a disjunction as in Zap's solutions.
  expect (← `(∀ x : Int, (∃ y : Int, x = 2 * y) → x ≠ 1)) .valid
  expect (← `(∀ x : Int, (∃ y : Int, x = 2 * y + 1) → x ≠ 1)) .invalid
  expect (← `(∀ x : Int, (False ∨ (∃ y : Int, x = 2 * y) ∨ x = 4) → x ≠ 1)) .valid
  expect (← `(∀ x : Int, ((∃ y : Int, x = 2 * y) ∨ x = 1) → x ≠ 1)) .invalid
  expect (← `(∀ n : Int, (∃ k : Nat, n = k) → 0 ≤ n)) .valid
  -- Universals in the head, and existentials under its negations.
  expect (← `(∀ x : Int, 0 ≤ x → (∀ y : Int, y = x → 0 ≤ y) ∨ x = 5)) .valid
  expect (← `(∀ x : Int, 0 ≤ x → (∀ y : Int, y ≤ x → 0 ≤ y) ∨ x = 5)) .invalid
  expect (← `(¬∃ x : Int, x < x)) .valid
  -- The other polarities: an existential head and a universal premise.
  expectUnknown (← `(∀ x : Int, ∃ y : Int, y = x + 1))
  expectUnknown (← `(∀ x : Int, (∀ y : Int, y ≤ x) → False))
  -- Mixed polarity: under `↔` a quantifier is both asserted and negated.
  expectUnknown (← `(∀ x : Int, (∃ y : Int, x = 2 * y) ↔ (∃ y : Int, x = 2 * y)))
  withOptions (·.setBool `flex.smt.encodeQuantifiers true) do
    expect (← `(∀ x : Int, ∃ y : Int, y = x + 1)) .valid
    expect (← `(∃ y : Int, ∀ x : Int, y = x + 1)) .invalid
    expect (← `(∀ x : Int, (∃ y : Int, x = 2 * y) ↔ (∃ y : Int, x = 2 * y))) .valid
  -- A premise that is not encoded is omitted: unsat stays valid, sat is unknown.
  expect (← `(∀ x : Int, (∀ y : Int, y ≤ x) → 0 ≤ 1)) .valid
  -- Conjunctions of clauses are checked clause by clause.
  expect (← `(0 ≤ 1 ∧ (∀ i : Int, 0 ≤ i → 0 ≤ i + 1) ∧ ∀ i : Int, 0 ≤ i → i ≠ -1)) .valid
  expect (← `(0 ≤ 1 ∧ ∀ i : Int, 0 ≤ i → i ≠ 0)) .invalid

-- Nonempty opaque types are uninterpreted sorts, exactly; possibly empty ones are not encoded.
opaque TokenCarrier : (α : Type) × Inhabited α := ⟨Unit, ⟨()⟩⟩
private def Token : Type := TokenCarrier.1
private instance : Inhabited Token := TokenCarrier.2
opaque Unknown : Type
run_elab do
  expect (← `(∀ (a b c : Token), a = b → b = c → a = c)) .valid
  expect (← `(∀ (a b : Token), a = b)) .invalid
  expect (← `(∀ (a : Token) (x : Int), (∃ b : Token, a = b ∧ x = 1) → x = 1)) .valid
  expectUnknown (← `(∀ (a b : Unknown), a = b))

-- Direct `Int.le`/`Int.lt` calls are exact.
run_elab do
  expect (← `(∀ (i n : Int), Int.le i n → Int.lt n i → False)) .valid
  expect (← `(∀ (i n : Int), Int.le i n → Int.lt i n)) .invalid

end SMTEncodingTests
