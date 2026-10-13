import Flex.VCG.LambdaRK.VCGen

/-!
# The two λRK development examples

These examples run the draft checker and display its generated constraints.
This file displays generated constraints; `Demo.LambdaRK.SolvedMap` also proves
source-program total correctness using a solver certificate.
The same two programs are intended to accompany the later proof PRs.
-/

namespace LambdaRK.Examples

/-- The shared signature contains one parameterized datatype, one total measure,
and the unknown two-place integer predicate used by `map`. -/
def signature : Signature := {
  datatypes := [{
    name := "List"
    params := 1
    ctors := [
      { name := "nil", fields := [] },
      { name := "cons", fields := [.var 0, .data "List" [.var 0]] }
    ]
  }]
  measures := [{
    name := "len"
    datatype := "List"
    cases := [
      { ctor := "nil", body := .literal 0 },
      { ctor := "cons", body := .add (.literal 1) (.recur 1) }
    ]
  }]
  kvars := [{ name := "mapLength", args := [.int, .int] }]
}

/-! ## 1. Explicit, impredicative System F identity -/

def identityTy : Ty := .all (.arrow "x" (.var 0) (.var 0))

def identity : Expr := .tyLam (.lam "x" (.var 0) (.var "x"))

/-- `id [∀α. α → α] id`: the type argument is itself polymorphic. -/
def identityAtPolymorphicType : Expr :=
  .letE "id" identity (.app (.tyApp (.var "id") identityTy) (.var "id"))

def identityVC : Except String Cstr := generate signature identity identityTy

def impredicativeIdentityVC : Except String Cstr :=
  generate signature identityAtPolymorphicType identityTy

/-! ## 2. Polymorphic `map` with an inferred length summary

The recursive function is annotated with `mapLength (len xs) (len result)`.
The requested outer type states `len result = len input`. Consequently the
checker must generate initialization/preservation heads for `mapLength` and
a final obligation establishing the requested equality from that summary.

Under the two type binders, index 1 is the input element type and index 0 is
the output element type. Named lets make dependent applications explicit.
-/

private def listTy (element : Ty) : Ty := .data "List" [element]

private def lengthOf (name : String) : LTerm := .measure "len" (.var name)

private def mapSummary : Ty :=
  .refine (listTy (.var 0))
    (.kvar "mapLength" [lengthOf "xs", lengthOf valueName])

def mapTy : Ty :=
  .all (.all (
    .arrow "f" (.arrow "item" (.var 1) (.var 0)) (
      .arrow "input" (listTy (.var 1)) (
        .refine (listTy (.var 0))
          (.theory (.eq (lengthOf valueName) (lengthOf "input")))))))

def map : Expr :=
  .tyLam (.tyLam (
    .lam "f" (.arrow "item" (.var 1) (.var 0)) (
      .lam "input" (listTy (.var 1)) (
        .letE "output"
          (.app
            (.structRec "xs" (listTy (.var 1)) mapSummary
              (.matchE (.var "xs") [
                ("nil", [], .ctor "nil" [.var 0] []),
                ("cons", ["x", "tail"],
                  .letE "y" (.app (.var "f") (.var "x")) (
                    .letE "mapped" (.recur (.var "tail")) (
                      .ctor "cons" [.var 0] [.var "y", .var "mapped"])))
              ]))
            (.var "input"))
          (.var "output")))))

def mapVC : Except String Cstr := generate signature map mapTy

/-- Rendering is local to the demo: it flattens conjunctions and omits `True`
leaves while retaining all quantifiers, premises, and nontrivial heads. -/
private def termText : LTerm → String
  | .var name => name
  | .int value => toString value
  | .bool value => toString value
  | .add left right => s!"({termText left} + {termText right})"
  | .ctor name [] => name
  | .ctor name fields => s!"{name}({String.intercalate ", " (fields.map termText)})"
  | .measure name argument => s!"{name}({termText argument})"

private def formulaText : Formula → String
  | .truth => "True"
  | .falsity => "False"
  | .eq left right => s!"{termText left} = {termText right}"
  | .le left right => s!"{termText left} ≤ {termText right}"
  | .and left right => s!"({formulaText left} ∧ {formulaText right})"
  | .or left right => s!"({formulaText left} ∨ {formulaText right})"
  | .not body => s!"¬({formulaText body})"

private def atomText : Atom → String
  | .theory formula => formulaText formula
  | .kvar name args => s!"{name}({String.intercalate ", " (args.map termText)})"

private def sortText : LSort → String
  | .int => "Int"
  | .bool => "Bool"
  | .value => "Value"

private def clauseLines (binders premises : List String) : Cstr → List String
  | .truth => []
  | .head atom =>
      let quantifiers := if binders.isEmpty then "" else
        s!"∀ {String.intercalate ", " binders}, "
      let body := String.intercalate " → " (premises ++ [atomText atom])
      [quantifiers ++ body]
  | .guard atom body => clauseLines binders (premises ++ [atomText atom]) body
  | .all name sort body =>
      clauseLines (binders ++ [s!"{name}: {sortText sort}"]) premises body
  | .conj left right => clauseLines binders premises left ++ clauseLines binders premises right

private def display (name : String) (result : Except String Cstr) : IO Unit := do
  match result with
  | .error message => IO.println s!"{name}: rejected: {message}"
  | .ok constraints =>
      let lines := clauseLines [] [] constraints
      IO.println s!"{name}: accepted; {lines.length} nontrivial clauses"
      for line in lines do IO.println s!"  {line}"

-- The output is computed from the source programs above, not hand-written CHCs.
#eval display "identity" identityVC
#eval display "identity at a polymorphic type" impredicativeIdentityVC
#eval display "map" mapVC

end LambdaRK.Examples
