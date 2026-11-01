import Flex.VCG.Imp
import Std

/-! Curated native-Lean Imp case studies: 25 programs, with programs before contracts.
Retains all 15 successes from the 50-program exploratory run and two open challenges
per family. This is a post-selection case-study suite, not an unbiased coverage sample.
The 2026-10-31 full result remains 15/50; this selected suite was 15/25.
Original IDs are stable. Full sources and measurements are archived under
`evaluation/Imp/results/20261031-before-cleanup/` and `20261031-eight-steps-final/`.
No invariant or qualifier is supplied by these programs.

Open challenges, two per family:
* Factorial / GCD: shifted products and Euclidean measure preservation.
* Minimum / FirstMatch: quantified bounds and optional witnesses.
* TakeWhile / Flatten: guarded completion and nested-loop fragments.
* FillRange / PrefixSums: array frames and mutable prefix observations.
* CountNodes / EvaluateExpr: worklist measures and evaluation frames. -/

namespace ImpBench

inductive Tree where
  | empty
  | node (left : Tree) (value : Int) (right : Tree)
  deriving Repr, BEq, DecidableEq

inductive BinOp where
  | add | sub | mul
  deriving Repr, BEq, DecidableEq

def BinOp.apply : BinOp → Int → Int → Int
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

inductive Expr where
  | lit (value : Int)
  | bin (op : BinOp) (left right : Expr)
  deriving Repr, BEq, DecidableEq

end ImpBench

namespace ImpBench.ArrayOps

def read (a : Array Int) (i : Nat) : Option Int := a[i]?

def write (a : Array Int) (i : Nat) (x : Int) : Option (Array Int) :=
  if h : i < a.size then some (a.set i x h) else none

end ImpBench.ArrayOps


-- BEGIN PROGRAM 1: SumRange

namespace ImpBench.SumRange
abbrev Store := Imp.State [Nat, Nat]

def program (n : Nat) : Imp.Cmd Store :=
  imp (i, total) {
    set (0, 0);
    while i < n do { set (i + 1, total + i) }
  }
end ImpBench.SumRange

-- END PROGRAM 1: SumRange

-- BEGIN PROGRAM 2: SumSquares

namespace ImpBench.SumSquares
abbrev Store := Imp.State [Nat, Nat]

def program (n : Nat) : Imp.Cmd Store :=
  imp (i, total) {
    set (0, 0);
    while i < n do { set (i + 1, total + i * i) }
  }
end ImpBench.SumSquares

-- END PROGRAM 2: SumSquares

-- BEGIN PROGRAM 3: ArithmeticProgression

namespace ImpBench.ArithmeticProgression
abbrev Store := Imp.State [Nat, Int, Int]

def program (a d : Int) (n : Nat) : Imp.Cmd Store :=
  imp (i, term, total) {
    set (0, a, 0);
    while i < n do { set (i + 1, term + d, total + term) }
  }
end ImpBench.ArithmeticProgression

-- END PROGRAM 3: ArithmeticProgression

-- BEGIN PROGRAM 4: Multiply

namespace ImpBench.Multiply
abbrev Store := Imp.State [Nat, Nat]

def program (a b : Nat) : Imp.Cmd Store :=
  imp (i, product) {
    set (0, 0);
    while i < b do { set (i + 1, product + a) }
  }
end ImpBench.Multiply

-- END PROGRAM 4: Multiply

-- BEGIN PROGRAM 5: Power

namespace ImpBench.Power
abbrev Store := Imp.State [Nat, Nat]

def program (base exponent : Nat) : Imp.Cmd Store :=
  imp (i, result) {
    set (0, 1);
    while i < exponent do { set (i + 1, result * base) }
  }
end ImpBench.Power

-- END PROGRAM 5: Power

-- BEGIN PROGRAM 6: Factorial

namespace ImpBench.Factorial
abbrev Store := Imp.State [Nat, Nat]

def program (n : Nat) : Imp.Cmd Store :=
  imp (i, result) {
    set (1, 1);
    while i ≤ n do { set (i + 1, result * i) }
  }
end ImpBench.Factorial

-- END PROGRAM 6: Factorial

-- BEGIN PROGRAM 7: Fibonacci

namespace ImpBench.Fibonacci
abbrev Store := Imp.State [Nat, Nat, Nat]

def program (n : Nat) : Imp.Cmd Store :=
  imp (i, a, b) {
    set (0, 0, 1);
    while i < n do { set (i + 1, b, a + b) }
  }
end ImpBench.Fibonacci

-- END PROGRAM 7: Fibonacci

-- BEGIN PROGRAM 8: Divide

namespace ImpBench.Divide
abbrev Store := Imp.State [Nat, Nat]

def program (a b : Nat) : Imp.Cmd Store :=
  imp (quotient, remainder) {
    set (0, a);
    while b ≤ remainder do { set (quotient + 1, remainder - b) }
  }
end ImpBench.Divide

-- END PROGRAM 8: Divide

-- BEGIN PROGRAM 9: GCD

namespace ImpBench.GCD
abbrev Store := Imp.State [Nat, Nat]

def program (a b : Nat) : Imp.Cmd Store :=
  imp (x, y) {
    set (a, b);
    while y != 0 do { set (y, x % y) }
  }
end ImpBench.GCD

-- END PROGRAM 9: GCD

-- BEGIN PROGRAM 11: ListSum

namespace ImpBench.ListSum
abbrev Store := Imp.State [List Int, Int]
def advance : Store → Store
  | ([], total, _) => ([], total, ())
  | (x :: xs, total, _) => (xs, total + x, ())
def program (input : List Int) : Imp.Cmd Store :=
  imp (remaining, total) {
    set (input, 0);
    while !remaining.isEmpty do { modify advance }
  }
end ImpBench.ListSum

-- END PROGRAM 11: ListSum

-- BEGIN PROGRAM 12: CountPredicate

namespace ImpBench.CountPredicate
abbrev Store := Imp.State [List Int, Nat]
def advance (p : Int → Bool) : Store → Store
  | ([], count, _) => ([], count, ())
  | (x :: xs, count, _) => (xs, count + if p x then 1 else 0, ())
def program (input : List Int) (p : Int → Bool) : Imp.Cmd Store :=
  imp (remaining, count) {
    set (input, 0);
    while !remaining.isEmpty do { modify (advance p) }
  }
end ImpBench.CountPredicate

-- END PROGRAM 12: CountPredicate

-- BEGIN PROGRAM 13: Minimum

namespace ImpBench.Minimum
abbrev Store := Imp.State [List Int, Int]
def seed : Store → Option Store
  | ([], _, _) => none
  | (x :: xs, _, _) => some (xs, x, ())
def advance : Store → Store
  | ([], best, _) => ([], best, ())
  | (x :: xs, best, _) => (xs, min best x, ())
def program (input : List Int) : Imp.Cmd Store :=
  imp (remaining, best) {
    set (input, 0);
    step seed;
    while !remaining.isEmpty do { modify advance }
  }
end ImpBench.Minimum

-- END PROGRAM 13: Minimum

-- BEGIN PROGRAM 15: FirstMatch

namespace ImpBench.FirstMatch
abbrev Store := Imp.State [List Int, Nat, Option Nat]
def advance (p : Int → Bool) : Store → Store
  | ([], i, found, _) => ([], i, found, ())
  | (x :: xs, i, found, _) => (xs, i + 1, if p x then some i else found, ())
def program (input : List Int) (p : Int → Bool) : Imp.Cmd Store :=
  imp (remaining, i, found) {
    set (input, 0, none);
    while !remaining.isEmpty && found.isNone do { modify (advance p) }
  }
end ImpBench.FirstMatch

-- END PROGRAM 15: FirstMatch

-- BEGIN PROGRAM 17: AllPredicate

namespace ImpBench.AllPredicate
abbrev Store := Imp.State [List Int, Bool]
def advance (p : Int → Bool) : Store → Store
  | ([], result, _) => ([], result, ())
  | (x :: xs, result, _) => (xs, result && p x, ())
def program (input : List Int) (p : Int → Bool) : Imp.Cmd Store :=
  imp (remaining, result) {
    set (input, true);
    while !remaining.isEmpty && result do { modify (advance p) }
  }
end ImpBench.AllPredicate

-- END PROGRAM 17: AllPredicate

-- BEGIN PROGRAM 21: CopyList

namespace ImpBench.CopyList
abbrev Store := Imp.State [List Int, Array Int]
def advance : Store → Store
  | ([], output, _) => ([], output, ())
  | (x :: xs, output, _) => (xs, output.push x, ())
def program (input : List Int) : Imp.Cmd Store :=
  imp (remaining, output) {
    set (input, #[]);
    while !remaining.isEmpty do { modify advance }
  }
end ImpBench.CopyList

-- END PROGRAM 21: CopyList

-- BEGIN PROGRAM 22: MapList

namespace ImpBench.MapList
abbrev Store := Imp.State [List Int, Array Int]
def advance (f : Int → Int) : Store → Store
  | ([], output, _) => ([], output, ())
  | (x :: xs, output, _) => (xs, output.push (f x), ())
def program (input : List Int) (f : Int → Int) : Imp.Cmd Store :=
  imp (remaining, output) {
    set (input, #[]);
    while !remaining.isEmpty do { modify (advance f) }
  }
end ImpBench.MapList

-- END PROGRAM 22: MapList

-- BEGIN PROGRAM 23: ReverseList

namespace ImpBench.ReverseList
abbrev Store := Imp.State [List Int, List Int]
def advance : Store → Store
  | ([], output, _) => ([], output, ())
  | (x :: xs, output, _) => (xs, x :: output, ())
def program (input : List Int) : Imp.Cmd Store :=
  imp (remaining, output) {
    set (input, []);
    while !remaining.isEmpty do { modify advance }
  }
end ImpBench.ReverseList

-- END PROGRAM 23: ReverseList

-- BEGIN PROGRAM 24: FilterList

namespace ImpBench.FilterList
abbrev Store := Imp.State [List Int, Array Int]
def advance (p : Int → Bool) : Store → Store
  | ([], output, _) => ([], output, ())
  | (x :: xs, output, _) => (xs, if p x then output.push x else output, ())
def program (input : List Int) (p : Int → Bool) : Imp.Cmd Store :=
  imp (remaining, output) {
    set (input, #[]);
    while !remaining.isEmpty do { modify (advance p) }
  }
end ImpBench.FilterList

-- END PROGRAM 24: FilterList

-- BEGIN PROGRAM 25: StablePartition

namespace ImpBench.StablePartition
abbrev Store := Imp.State [List Int, Array Int, Array Int]
def advance (p : Int → Bool) : Store → Store
  | ([], yes, no, _) => ([], yes, no, ())
  | (x :: xs, yes, no, _) =>
      if p x then (xs, yes.push x, no, ()) else (xs, yes, no.push x, ())
def program (input : List Int) (p : Int → Bool) : Imp.Cmd Store :=
  imp (remaining, yes, no) {
    set (input, #[], #[]);
    while !remaining.isEmpty do { modify (advance p) }
  }
end ImpBench.StablePartition

-- END PROGRAM 25: StablePartition

-- BEGIN PROGRAM 26: TakeWhile

namespace ImpBench.TakeWhile
abbrev Store := Imp.State [List Int, Array Int, Bool]
def advance (p : Int → Bool) : Store → Store
  | ([], output, taking, _) => ([], output, taking, ())
  | (x :: xs, output, _, _) =>
      if p x then (xs, output.push x, true, ()) else (xs, output, false, ())
def program (input : List Int) (p : Int → Bool) : Imp.Cmd Store :=
  imp (remaining, output, taking) {
    set (input, #[], true);
    while !remaining.isEmpty && taking do { modify (advance p) }
  }
end ImpBench.TakeWhile

-- END PROGRAM 26: TakeWhile

-- BEGIN PROGRAM 28: Flatten

namespace ImpBench.Flatten
abbrev Store := Imp.State [List (List Int), List Int, Array Int]
def nextChunk : Store → Store
  | ([], current, output, _) => ([], current, output, ())
  | (xs :: rest, _, output, _) => (rest, xs, output, ())
def appendHead : Store → Store
  | (rest, [], output, _) => (rest, [], output, ())
  | (rest, x :: xs, output, _) => (rest, xs, output.push x, ())
def program (input : List (List Int)) : Imp.Cmd Store :=
  imp (remaining, current, output) {
    set (input, [], #[]);
    while !remaining.isEmpty do {
      modify nextChunk;
      while !current.isEmpty do { modify appendHead }
    }
  }
end ImpBench.Flatten

-- END PROGRAM 28: Flatten

-- BEGIN PROGRAM 31: FillRange

namespace ImpBench.FillRange
open ArrayOps
abbrev Store := Imp.State [Array Int, Nat]

def advance (value : Int) : Store → Option Store := fun (a, i, _) => do
  let a ← write a i value
  return (a, i + 1, ())

def program (original : Array Int) (lo hi : Nat) (value : Int) : Imp.Cmd Store :=
  imp (a, i) {
    set (original, lo);
    while i < hi do { step (advance value) }
  }
end ImpBench.FillRange

-- END PROGRAM 31: FillRange

-- BEGIN PROGRAM 35: PrefixSums

namespace ImpBench.PrefixSums
open ArrayOps
abbrev Store := Imp.State [Array Int, Nat, Int]

def advance : Store → Option Store := fun (a, i, total, _) => do
  let x ← read a i
  let a ← write a i (total + x)
  return (a, i + 1, total + x, ())

def program (original : Array Int) : Imp.Cmd Store :=
  imp (a, i, total) {
    set (original, 0, 0);
    while i < a.size do { step advance }
  }
end ImpBench.PrefixSums

-- END PROGRAM 35: PrefixSums

-- BEGIN PROGRAM 41: CountNodes

namespace ImpBench.CountNodes

abbrev Store := Imp.State [List Tree, Nat]

def advance : Store → Option Store
  | ([], _, _) => none
  | (.empty :: todo, count, _) => some (todo, count, ())
  | (.node l _ r :: todo, count, _) => some (l :: r :: todo, count + 1, ())

def program (input : Tree) : Imp.Cmd Store :=
  imp (todo, count) {
    set ([input], 0);
    while !todo.isEmpty do { step advance }
  }

end ImpBench.CountNodes

-- END PROGRAM 41: CountNodes

-- BEGIN PROGRAM 48: EvaluateExpr

namespace ImpBench.EvaluateExpr

inductive Frame where
  | visit (expression : Expr)
  | apply (op : BinOp)
  deriving Repr

abbrev Store := Imp.State [List Frame, List Int, Int]

def advance : Store → Option Store
  | (.visit (.lit value) :: todo, values, result, _) =>
      some (todo, value :: values, result, ())
  | (.visit (.bin op l r) :: todo, values, result, _) =>
      some (.visit l :: .visit r :: .apply op :: todo, values, result, ())
  | (.apply op :: todo, right :: left :: values, result, _) =>
      some (todo, op.apply left right :: values, result, ())
  | _ => none

def finish : Store → Option Store
  | ([], [value], _, _) => some ([], [value], value, ())
  | _ => none

def program (input : Expr) : Imp.Cmd Store :=
  imp (todo, values, result) {
    set ([Frame.visit input], [], 0);
    while !todo.isEmpty do { step advance };
    step finish
  }

end ImpBench.EvaluateExpr

-- END PROGRAM 48: EvaluateExpr

/-! ## Independent contracts and generated CHCs
`Imp.generate_sound` turns a proof of a generated VC into safe partial correctness;
it does not assert termination. -/

namespace ImpBench.Tree

def nodes : Tree → Nat
  | .empty => 0
  | .node l _ r => nodes l + nodes r + 1

end ImpBench.Tree

namespace ImpBench.Expr

def eval : Expr → Int
  | .lit value => value
  | .bin op l r => op.apply (eval l) (eval r)

end ImpBench.Expr

namespace ImpBench.SumRange
def pre : Store → Prop := fun _ => True
def post (n : Nat) (s : Store) : Prop :=
  s.1 = n ∧ s.2.1 = (List.range n).sum
def generated (n : Nat) : Prop :=
  Imp.generate pre (program n) (post n)
end ImpBench.SumRange


namespace ImpBench.SumSquares
def pre : Store → Prop := fun _ => True
def post (n : Nat) (s : Store) : Prop :=
  s.1 = n ∧ s.2.1 = ((List.range n).map (fun i => i * i)).sum
def generated (n : Nat) : Prop :=
  Imp.generate pre (program n) (post n)
end ImpBench.SumSquares


namespace ImpBench.ArithmeticProgression
def pre : Store → Prop := fun _ => True
def post (a d : Int) (n : Nat) (s : Store) : Prop :=
  s.1 = n ∧ s.2.1 = a + d * (n : Int) ∧
    s.2.2.1 = ((List.range n).map (fun (i : Nat) => a + d * (i : Int))).sum
def generated (a d : Int) (n : Nat) : Prop :=
  Imp.generate pre (program a d n) (post a d n)
end ImpBench.ArithmeticProgression


namespace ImpBench.Multiply
def pre : Store → Prop := fun _ => True
def post (a b : Nat) (s : Store) : Prop := s.1 = b ∧ s.2.1 = a * b
def generated (a b : Nat) : Prop :=
  Imp.generate pre (program a b) (post a b)
end ImpBench.Multiply


namespace ImpBench.Power
def pre : Store → Prop := fun _ => True
def post (base exponent : Nat) (s : Store) : Prop :=
  s.1 = exponent ∧ s.2.1 = base ^ exponent
def generated (base exponent : Nat) : Prop :=
  Imp.generate pre (program base exponent) (post base exponent)
end ImpBench.Power


namespace ImpBench.Factorial
def pre : Store → Prop := fun _ => True
/-- Product 1 · 2 · ... · n, expressed using the native list specification. -/
def post (n : Nat) (s : Store) : Prop :=
  s.1 = n + 1 ∧ s.2.1 = ((List.range n).map (· + 1)).prod
def generated (n : Nat) : Prop :=
  Imp.generate pre (program n) (post n)
end ImpBench.Factorial


namespace ImpBench.Fibonacci
/-- The native Nat recurrence used in Demo/Imp.lean. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def pre : Store → Prop := fun _ => True
def post (n : Nat) (s : Store) : Prop :=
  s.1 = n ∧ s.2.1 = fib n ∧ s.2.2.1 = fib (n + 1)
def generated (n : Nat) : Prop :=
  Imp.generate pre (program n) (post n)
end ImpBench.Fibonacci


namespace ImpBench.Divide
def pre (b : Nat) : Store → Prop := fun _ => 0 < b
def post (a b : Nat) (s : Store) : Prop := a = s.1 * b + s.2.1 ∧ s.2.1 < b
def generated (a b : Nat) : Prop :=
  Imp.generate (pre b) (program a b) (post a b)
end ImpBench.Divide


namespace ImpBench.GCD
def pre : Store → Prop := fun _ => True
def post (a b : Nat) (s : Store) : Prop := s.1 = Nat.gcd a b ∧ s.2.1 = 0
def generated (a b : Nat) : Prop :=
  Imp.generate pre (program a b) (post a b)
end ImpBench.GCD


namespace ImpBench.ListSum
def post (input : List Int) (s : Store) : Prop := s.2.1 = input.sum
def generated (input : List Int) : Prop :=
  Imp.generate (fun _ => True) (program input) (post input)
theorem sound (input : List Int) :
    generated input → Imp.Valid (fun _ => True) (program input) (post input) :=
  Imp.generate_sound
end ImpBench.ListSum


namespace ImpBench.CountPredicate
def post (input : List Int) (p : Int → Bool) (s : Store) : Prop :=
  s.2.1 = input.countP p
def generated (input : List Int) (p : Int → Bool) : Prop :=
  Imp.generate (fun _ => True) (program input p) (post input p)
theorem sound (input : List Int) (p : Int → Bool) :
    generated input p → Imp.Valid (fun _ => True) (program input p) (post input p) :=
  Imp.generate_sound
end ImpBench.CountPredicate


namespace ImpBench.Minimum
def pre (input : List Int) : Prop := input ≠ []
def post (input : List Int) (s : Store) : Prop :=
  s.2.1 ∈ input ∧ ∀ x ∈ input, s.2.1 ≤ x
def generated (input : List Int) : Prop :=
  Imp.generate (fun _ => pre input) (program input) (post input)
theorem sound (input : List Int) :
    generated input → Imp.Valid (fun _ => pre input) (program input) (post input) :=
  Imp.generate_sound
end ImpBench.Minimum


namespace ImpBench.FirstMatch
def post (input : List Int) (p : Int → Bool) (s : Store) : Prop :=
  s.2.2.1 = input.findIdx? p
def generated (input : List Int) (p : Int → Bool) : Prop :=
  Imp.generate (fun _ => True) (program input p) (post input p)
theorem sound (input : List Int) (p : Int → Bool) :
    generated input p → Imp.Valid (fun _ => True) (program input p) (post input p) :=
  Imp.generate_sound
end ImpBench.FirstMatch


namespace ImpBench.AllPredicate
def post (input : List Int) (p : Int → Bool) (s : Store) : Prop :=
  s.2.1 = input.all p
def generated (input : List Int) (p : Int → Bool) : Prop :=
  Imp.generate (fun _ => True) (program input p) (post input p)
theorem sound (input : List Int) (p : Int → Bool) :
    generated input p → Imp.Valid (fun _ => True) (program input p) (post input p) :=
  Imp.generate_sound
end ImpBench.AllPredicate


namespace ImpBench.CopyList
def post (input : List Int) (s : Store) : Prop := s.2.1.toList = input
def generated (input : List Int) : Prop :=
  Imp.generate (fun _ => True) (program input) (post input)
theorem sound (input : List Int) :
    generated input → Imp.Valid (fun _ => True) (program input) (post input) :=
  Imp.generate_sound
end ImpBench.CopyList


namespace ImpBench.MapList
def post (input : List Int) (f : Int → Int) (s : Store) : Prop :=
  s.2.1.toList = input.map f
def generated (input : List Int) (f : Int → Int) : Prop :=
  Imp.generate (fun _ => True) (program input f) (post input f)
theorem sound (input : List Int) (f : Int → Int) :
    generated input f → Imp.Valid (fun _ => True) (program input f) (post input f) :=
  Imp.generate_sound
end ImpBench.MapList


namespace ImpBench.ReverseList
def post (input : List Int) (s : Store) : Prop := s.2.1 = input.reverse
def generated (input : List Int) : Prop :=
  Imp.generate (fun _ => True) (program input) (post input)
theorem sound (input : List Int) :
    generated input → Imp.Valid (fun _ => True) (program input) (post input) :=
  Imp.generate_sound
end ImpBench.ReverseList


namespace ImpBench.FilterList
def post (input : List Int) (p : Int → Bool) (s : Store) : Prop :=
  s.2.1.toList = input.filter p
def generated (input : List Int) (p : Int → Bool) : Prop :=
  Imp.generate (fun _ => True) (program input p) (post input p)
theorem sound (input : List Int) (p : Int → Bool) :
    generated input p → Imp.Valid (fun _ => True) (program input p) (post input p) :=
  Imp.generate_sound
end ImpBench.FilterList


namespace ImpBench.StablePartition
def post (input : List Int) (p : Int → Bool) (s : Store) : Prop :=
  s.2.1.toList = input.filter p ∧ s.2.2.1.toList = input.filter (fun x => !p x)
def generated (input : List Int) (p : Int → Bool) : Prop :=
  Imp.generate (fun _ => True) (program input p) (post input p)
theorem sound (input : List Int) (p : Int → Bool) :
    generated input p → Imp.Valid (fun _ => True) (program input p) (post input p) :=
  Imp.generate_sound
end ImpBench.StablePartition


namespace ImpBench.TakeWhile
def post (input : List Int) (p : Int → Bool) (s : Store) : Prop :=
  s.2.1.toList = input.takeWhile p
def generated (input : List Int) (p : Int → Bool) : Prop :=
  Imp.generate (fun _ => True) (program input p) (post input p)
theorem sound (input : List Int) (p : Int → Bool) :
    generated input p → Imp.Valid (fun _ => True) (program input p) (post input p) :=
  Imp.generate_sound
end ImpBench.TakeWhile


namespace ImpBench.Flatten
def post (input : List (List Int)) (s : Store) : Prop := s.2.2.1.toList = input.flatten
def generated (input : List (List Int)) : Prop :=
  Imp.generate (fun _ => True) (program input) (post input)
theorem sound (input : List (List Int)) :
    generated input → Imp.Valid (fun _ => True) (program input) (post input) :=
  Imp.generate_sound
end ImpBench.Flatten


namespace ImpBench.FillRange
def pre (original : Array Int) (lo hi : Nat) : Store → Prop :=
  fun _ => lo ≤ hi ∧ hi ≤ original.size

def post (original : Array Int) (lo hi : Nat) (value : Int) (s : Store) : Prop :=
  s.1.size = original.size ∧ s.2.1 = hi ∧
    ∀ j, s.1[j]? = if lo ≤ j ∧ j < hi then some value else original[j]?

def generated (original : Array Int) (lo hi : Nat) (value : Int) : Prop :=
  Imp.generate (pre original lo hi) (program original lo hi value) (post original lo hi value)
end ImpBench.FillRange


namespace ImpBench.PrefixSums
def pre : Store → Prop := fun _ => True
def post (original : Array Int) (s : Store) : Prop :=
  s.1.size = original.size ∧ s.2.1 = original.size ∧ s.2.2.1 = original.toList.sum ∧
    ∀ j, j < original.size → s.1[j]? = some ((original.toList.take (j + 1)).sum)
def generated (original : Array Int) : Prop :=
  Imp.generate pre (program original) (post original)
end ImpBench.PrefixSums


namespace ImpBench.CountNodes
def post (input : Tree) (s : Store) : Prop := s.1 = [] ∧ s.2.1 = input.nodes
def generated (input : Tree) : Prop := Imp.generate (fun _ => True) (program input) (post input)
end ImpBench.CountNodes


namespace ImpBench.EvaluateExpr
def post (input : Expr) (s : Store) : Prop :=
  s.1 = [] ∧ s.2.1 = [input.eval] ∧ s.2.2.1 = input.eval
def generated (input : Expr) : Prop := Imp.generate (fun _ => True) (program input) (post input)
end ImpBench.EvaluateExpr


namespace ImpBench

structure Benchmark where
  id : Nat
  family : String
  program : Lean.Name
  generated : Lean.Name
  deriving Repr

/-- Retained cases, using their original exploratory-run IDs. -/
def corpus : Array Benchmark := #[
  ⟨1, "Arithmetic", ``ImpBench.SumRange.program, ``ImpBench.SumRange.generated⟩,
  ⟨2, "Arithmetic", ``ImpBench.SumSquares.program, ``ImpBench.SumSquares.generated⟩,
  ⟨3, "Arithmetic", ``ImpBench.ArithmeticProgression.program, ``ImpBench.ArithmeticProgression.generated⟩,
  ⟨4, "Arithmetic", ``ImpBench.Multiply.program, ``ImpBench.Multiply.generated⟩,
  ⟨5, "Arithmetic", ``ImpBench.Power.program, ``ImpBench.Power.generated⟩,
  ⟨6, "Arithmetic", ``ImpBench.Factorial.program, ``ImpBench.Factorial.generated⟩,
  ⟨7, "Arithmetic", ``ImpBench.Fibonacci.program, ``ImpBench.Fibonacci.generated⟩,
  ⟨8, "Arithmetic", ``ImpBench.Divide.program, ``ImpBench.Divide.generated⟩,
  ⟨9, "Arithmetic", ``ImpBench.GCD.program, ``ImpBench.GCD.generated⟩,
  ⟨11, "Scans", ``ImpBench.ListSum.program, ``ImpBench.ListSum.generated⟩,
  ⟨12, "Scans", ``ImpBench.CountPredicate.program, ``ImpBench.CountPredicate.generated⟩,
  ⟨13, "Scans", ``ImpBench.Minimum.program, ``ImpBench.Minimum.generated⟩,
  ⟨15, "Scans", ``ImpBench.FirstMatch.program, ``ImpBench.FirstMatch.generated⟩,
  ⟨17, "Scans", ``ImpBench.AllPredicate.program, ``ImpBench.AllPredicate.generated⟩,
  ⟨21, "Lists", ``ImpBench.CopyList.program, ``ImpBench.CopyList.generated⟩,
  ⟨22, "Lists", ``ImpBench.MapList.program, ``ImpBench.MapList.generated⟩,
  ⟨23, "Lists", ``ImpBench.ReverseList.program, ``ImpBench.ReverseList.generated⟩,
  ⟨24, "Lists", ``ImpBench.FilterList.program, ``ImpBench.FilterList.generated⟩,
  ⟨25, "Lists", ``ImpBench.StablePartition.program, ``ImpBench.StablePartition.generated⟩,
  ⟨26, "Lists", ``ImpBench.TakeWhile.program, ``ImpBench.TakeWhile.generated⟩,
  ⟨28, "Lists", ``ImpBench.Flatten.program, ``ImpBench.Flatten.generated⟩,
  ⟨31, "Arrays", ``ImpBench.FillRange.program, ``ImpBench.FillRange.generated⟩,
  ⟨35, "Arrays", ``ImpBench.PrefixSums.program, ``ImpBench.PrefixSums.generated⟩,
  ⟨41, "Worklists", ``ImpBench.CountNodes.program, ``ImpBench.CountNodes.generated⟩,
  ⟨48, "Worklists", ``ImpBench.EvaluateExpr.program, ``ImpBench.EvaluateExpr.generated⟩
]

end ImpBench
