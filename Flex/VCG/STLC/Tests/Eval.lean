import Flex.VCG.STLC.Interp
import Flex.VCG.STLC.Examples.Data
import Flex.VCG.STLC.Examples.Ord
import Flex.VCG.STLC.Examples.Measure

open STLC

/-! # Evaluation tests

  One or more tests per construct of the calculus, run with the definitional
  interpreter (`Interp.lean`): each `by_interp` runs the program and turns the
  result into an `Eval`/`Run` derivation (`interp_sound`), and each
  `stuck_interp` shows a program has no derivation at all (`interp_stuck`).

  The outcomes record the fuel left over, which pins down the cost model: only
  β-steps (application) and matching consume fuel, one unit each. -/

namespace STLC.Tests.Eval

/-! ## Literals, arithmetic and comparison -/

example : Eval 0 <| 5 |> (.val (.iconst 5) 0) := by by_interp

example : Eval 0 <| -3 |> (.val (.iconst (-3)) 0) := by by_interp

example : Eval 0 <| true |> (.val (.bconst true) 0) := by by_interp

/-- The unit `()` is the integer `0`. -/
example : Eval 0 <| () |> (.val (.iconst 0) 0) := by by_interp

example : Eval 0 <| 3 + -5 |> (.val (.iconst (-2)) 0) := by by_interp

example : Eval 0 <| 2 ≤ 3 |> (.val (.bconst true) 0) := by by_interp

example : Eval 0 <| 3 ≤ 2 |> (.val (.bconst false) 0) := by by_interp

/-- Comparison is polymorphic: on booleans, `false < true`. -/
example : Eval 0 <| false ≤ true |> (.val (.bconst true) 0) := by by_interp

example : Eval 0 <| true ≤ false |> (.val (.bconst false) 0) := by by_interp

/-! ## Boolean connectives and conditionals -/

example : Eval 0 <| ¬true |> (.val (.bconst false) 0) := by by_interp

example : Eval 0 <| true ∧ false |> (.val (.bconst false) 0) := by by_interp

/-- `∧` is strict: both sides are evaluated (here the right one is stuck). -/
example : ¬ ∃ o, Eval 5 <| false ∧ unreachable |> o := by stuck_interp

example : Eval 0 <| if 1 ≤ 2 then 10 else 20 |> (.val (.iconst 10) 0) := by by_interp

example : Eval 0 <| if 2 ≤ 1 then 10 else 20 |> (.val (.iconst 20) 0) := by by_interp

/-- Only the branch taken is evaluated. -/
example : Eval 0 <| if true then 1 else unreachable |> (.val (.iconst 1) 0) := by by_interp

/-! ## `let` -/

example : Eval 0 <| let x = 3 in let y = 4 in x + y |> (.val (.iconst 7) 0) := by by_interp

/-- Inner bindings shadow outer ones. -/
example : Eval 0 <| let x = 1 in let x = 2 in x |> (.val (.iconst 2) 0) := by by_interp

/-! ## Functions -/

/-- A `λ` is a value: it evaluates to a closure, without touching its body. -/
example : Eval 0 <| λ x, unreachable |> (.val (.clos .unreach) 0) := by by_interp

/-- Application costs one unit of fuel. -/
example : Eval 1 <| (λ x, x + 1) 4 |> (.val (.iconst 5) 0) := by by_interp

/-- With no fuel left, a β-step times out. -/
example : Eval 0 <| (λ x, x + 1) 4 |> .timeout := by by_interp

/-- Call-by-value: the argument is evaluated before the call. -/
example : ¬ ∃ o, Eval 5 <| (λ x, 0) unreachable |> o := by stuck_interp

/-- Currying and higher-order functions: `twice inc 0` is three β-steps for
    `twice` (two arguments, one call of `f` per application) plus two for `inc`. -/
example : Eval 10
    <| let twice = λ f x, f (f x) in let inc = λ x, x + 1 in twice inc 0 |>
    (.val (.iconst 2) 6) := by by_interp

/-- Closures capture their environment (by substitution). -/
example : Eval 10 <| let k = (λ x y, x) 1 in let x = 2 in k x |> (.val (.iconst 1) 8) := by
  by_interp

/-! ## Recursion -/

/-- `fix f x, e` is a value — a recursive closure. -/
example : Eval 0 <| fix f x, f x |> (.val (.fclos (.app (.bvar 1) (.bvar 0))) 0) := by by_interp

/-- `sum 10 = 55`, in eleven calls. -/
example : Run 20 <| let sum : ⌜sumTy⌝ = ⌜sumE⌝ in let ten = 10 in sum ten |>
    (.val (.iconst 55) 9) := by by_interp

/-- Fibonacci, non-ANF: the runtime does not need let-normal form. -/
abbrev fibE : Exp :=
  <| fix fib n, if n ≤ 1 then n else fib (n + -1) + fib (n + -2) |>

set_option maxRecDepth 4000 in
example : Eval 1000 <| ⌜fibE⌝ 10 |> (.val (.iconst 55) 823) := by by_interp

/-- A diverging loop exhausts any fuel budget. -/
example : Run 0 loopMain .timeout := by by_interp
example : Run 7 loopMain .timeout := by by_interp
example : Run 30 loopMain .timeout := by by_interp

/-! ## Types are erased -/

/-- Annotations, type abstraction and type application do not affect evaluation. -/
example : Run 1 <| (((Λ α, λ x, x) : ∀ α : B, α -> α)[Int]) 3 |> (.val (.iconst 3) 0) := by
  by_interp

/-- `Λ` is not a value of its own: under it the body is evaluated (types are
    erased), so a stuck body makes the abstraction stuck. -/
example : ¬ ∃ o, Eval 5 <| Λ α, unreachable |> o := by stuck_interp

/-! ## Pairs -/

example : Eval 0 <| (1, true) |> (.val (.pair (.iconst 1) (.bconst true)) 0) := by by_interp

/-- Tuples nest to the right. -/
example : Eval 0 <| (1, 2, 3) |>
    (.val (.pair (.iconst 1) (.pair (.iconst 2) (.iconst 3))) 0) := by by_interp

example : Eval 0 <| let (x, y) = (1, 2) in y + x |> (.val (.iconst 3) 0) := by by_interp

example : Eval 0 <| let (x, (y, z)) = (1, 2, 3) in x + z |> (.val (.iconst 4) 0) := by
  by_interp

/-! ## Datatypes -/

/-- A constructor builds its fields into a payload ending in a unit. -/
example : Run 0 <| Some[Int] 7 |>
    (.val (.ctor "option" 1 (.pair (.iconst 7) (.iconst 0))) 0) := by by_interp

example : Run 0 <| let n = Nil[Int] in Cons[Int] 1 n |>
    (.val (.ctor "list" 1 (.pair (.iconst 1) (.pair (.ctor "list" 0 (.iconst 0)) (.iconst 0)))) 0) := by
  by_interp

/-- Matching costs one unit of fuel, and selects the alternative by constructor. -/
example : Run 1 <| match Some[Int] 7 with | None => 0 | Some x => x |> (.val (.iconst 7) 0) := by
  by_interp

example : Run 0 <| match Some[Int] 7 with | None => 0 | Some x => x |> .timeout := by by_interp

/-- The alternatives may be written in any order. -/
example : Run 1 <| match None[Int] with | Some x => x | None => 42 |> (.val (.iconst 42) 0) := by
  by_interp

/-- `sum [1, 2] = 3` (the `Data` example): three calls and three matches. -/
example : Run 20 sumClientE (.val (.iconst 3) 14) := by by_interp

/-- `head [1, 2] = 1` (the `Measure` example). -/
example : Run 20 headClientE (.val (.iconst 1) 18) := by by_interp

/-- Sorting `[3, 1, 2]` yields an ordered list (the `Ord` example). -/
example : Run 200 sortClientE (.val (.bconst true) 174) := by by_interp

/-! ## Stuck states -/

example : ¬ ∃ o, Eval 5 .unreach o := by stuck_interp

/-- A free variable has no value. -/
example : ¬ ∃ o, Eval 5 (.fvar "x") o := by stuck_interp

/-- An unbound de Bruijn index. -/
example : ¬ ∃ o, Eval 5 (.bvar 0) o := by stuck_interp

example : ¬ ∃ o, Eval 5 <| 1 + true |> o := by stuck_interp

/-- Comparison needs two values of the same sort. -/
example : ¬ ∃ o, Eval 5 <| 1 ≤ true |> o := by stuck_interp

example : ¬ ∃ o, Eval 5 <| ¬1 |> o := by stuck_interp

example : ¬ ∃ o, Eval 5 <| if 0 then 1 else 2 |> o := by stuck_interp

/-- Applying a non-function. -/
example : ¬ ∃ o, Eval 5 <| 3 4 |> o := by stuck_interp

/-- Splitting a non-pair. -/
example : ¬ ∃ o, Eval 5 <| let (x, y) = 3 in x |> o := by stuck_interp

/-- Matching a non-constructor, and a constructor without an alternative. -/
example : ¬ ∃ o, Eval 5 (caseL (.iconst 0) [.iconst 1]) o := by stuck_interp
example : ¬ ∃ o, Eval 5 (caseL (.ctor "D" 1 [] (.iconst 0)) [.iconst 1]) o := by stuck_interp

/-- Stuckness takes priority over running out of fuel only if it comes first. -/
example : Eval 0 <| let x = (λ y, y) 0 in unreachable |> .timeout := by by_interp
example : ¬ ∃ o, Eval 0 <| let x = unreachable in (λ y, y) 0 |> o := by stuck_interp

/-! ## The interpreter agrees with the derivations -/

/-- Gas bounds only the interpreter's recursion depth: too little and it gives
    up, more than enough and the answer no longer changes. -/
example : interp 1 0 <| 1 + 2 |> = .outOfGas := rfl
example : interp 2 0 <| 1 + 2 |> = .ok (.val (.iconst 3) 0) := rfl
example (g : Nat) : interp (g + 2) 0 <| 1 + 2 |> = .ok (.val (.iconst 3) 0) :=
  (interp_mono (g := 2) (by omega) (fun h => by cases h)).trans rfl

/-- …and the outcome is unique: the program cannot also evaluate to `4`. -/
example : ¬ Eval 0 <| 1 + 2 |> (.val (.iconst 4) 0) := fun h => by
  cases Eval.det h (by by_interp : Eval 0 <| 1 + 2 |> (.val (.iconst 3) 0))

end STLC.Tests.Eval
