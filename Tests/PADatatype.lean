import Flex.PA.Smt

/-! PA SMT datatype encoding: records, enums, recursive inductives and uninterpreted
functions reach z3 instead of being omitted. -/

namespace PADatatypeTests

open Lean Meta Elab Term Flex.PA

structure Rec (t0 : Type) [Inhabited t0] where
  mkRec ::
    a : t0
    b : Int
    ok : Prop

inductive E where
  | A
  | B (n : Int)

structure WithMap where
  m : Int → Int

structure WithNat where
  n : Nat

def len : List Int → Int
  | [] => 0
  | _ :: xs => 1 + len xs

private def queries (terms : Array (TSyntax `term)) : TermElabM (Array Expr) :=
  terms.mapM fun term => do
    let e ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

private def expect (terms : Array (TSyntax `term)) (expected : Array PASynthResult) :
    TermElabM Unit := do
  let actual ← smtOracle 2000 (← queries terms)
  unless actual == expected do throwError "PA SMT: expected {repr expected}, got {repr actual}"

private def isUnknown : PASynthResult → Bool
  | .unknown _ => true
  | _ => false

run_elab do
  -- Record fields, extensionality, and parametric instantiation.
  expect #[← `(∀ r : Rec Int, r.b > 0 → r.b ≥ 1),
           ← `(∀ r : Rec Int, r.a > 0 → r.b ≥ 1),
           ← `(∀ r s : Rec Int, r.a = s.a → r.b = s.b → (r.ok ↔ s.ok) → r = s),
           ← `(∀ r : Rec Int, r.ok → r = Rec.mkRec r.a r.b True)]
    #[.valid, .invalid, .valid, .valid]
  -- Pattern matching on an enum-like inductive.
  expect #[← `(∀ e : E, (match e with | .A => 0 | .B n => n * n) ≥ 0),
           ← `(∀ e : E, (match e with | .A => 1 | .B n => n) ≥ 0),
           ← `(∀ e : E, e ≠ E.A → ∃ n : Int, e = E.B n)]
    #[.valid, .invalid, .valid]
  -- Recursive datatypes and standard inductives.
  expect #[← `(∀ l : List Int, l = [] ∨ ∃ x xs, l = x :: xs),
           ← `(∀ o : Option Int, o ≠ none → ∃ x : Int, o = some x),
           ← `(∀ p : Int × Bool, p.1 > 0 → p.2 = true → p = (p.1, true))]
    #[.valid, .valid, .valid]
  -- Uninterpreted functions prove what congruence proves; sat is inconclusive.
  let results ← smtOracle 2000 (← queries #[
    ← `(∀ l : List Int, len l ≥ 0 → len l ≥ 0),
    ← `(∀ l m : List Int, l = m → len l = len m),
    ← `(∀ l : List Int, len l ≥ 1)])
  unless results[0]! == .valid && results[1]! == .valid && isUnknown results[2]! do
    throwError "PA SMT: uninterpreted functions: {repr results}"
  -- Function and Nat fields are not encoded.
  let results ← smtOracle 2000 (← queries #[
    ← `(∀ w : WithMap, w.m 0 > 0 → w.m 0 > 0),
    ← `(∀ w : WithNat, w = w)])
  unless results.all isUnknown do throwError "PA SMT: unsupported fields: {repr results}"
  logInfo "datatype tests passed"

end PADatatypeTests
