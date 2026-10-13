import Demo.SystemFRK

/-!
Focused executable checks for the draft frontend. These are implementation
regressions complementing the proved soundness theorems.
-/

namespace SystemFRK.Checks

open Examples

private def succeeds : Except String α → Bool
  | .ok _ => true
  | .error _ => false

private def rejects (result : Except String α) : Bool := !succeeds result

private def countHeads (name : String) : Cstr → Nat
  | .truth => 0
  | .head (.kvar headName _) => if headName == name then 1 else 0
  | .head _ => 0
  | .guard _ body | .all _ _ body => countHeads name body
  | .conj left right => countHeads name left + countHeads name right

private def usesSummary : Cstr → Bool
  | .truth | .head _ => false
  | .guard (.kvar "mapLength" _) _ => true
  | .guard _ body | .all _ _ body => usesSummary body
  | .conj left right => usesSummary left || usesSummary right

private def hasMeasureEquality : Cstr → Bool
  | .head (.theory (.eq (.measure "len" _) (.measure "len" _))) => true
  | .truth | .head _ => false
  | .guard _ body | .all _ _ body => hasMeasureEquality body
  | .conj left right => hasMeasureEquality left || hasMeasureEquality right

#guard succeeds identityVC
#guard succeeds impredicativeIdentityVC

-- `map` must generate both constructor cases and consume the recursive summary
-- in a safety query. A successful checker returning `True` would fail this test.
#guard match mapVC with
  | .ok constraints =>
      countHeads "mapLength" constraints == 2 &&
      usesSummary constraints && hasMeasureEquality constraints
  | .error _ => false

private def intList : Ty := .data "List" [.int]

-- Type application and type-variable scoping.
#guard rejects (generate signature (.tyApp (.int 0) .int) .int)
#guard rejects (generate signature
  (.tyLam (.lam "x" (.var 1) (.var "x")))
  (.all (.arrow "x" (.var 1) (.var 1))))

-- Matching must cover constructors exactly and use the correct field arity.
#guard rejects (generate signature
  (.lam "xs" intList (.matchE (.var "xs") [("nil", [], .int 0)]))
  (.arrow "xs" intList .int))
#guard rejects (generate signature
  (.lam "xs" intList (.matchE (.var "xs") [
    ("nil", [], .int 0), ("cons", ["tail"], .int 1)]))
  (.arrow "xs" intList .int))

-- The recursion construct is structural, rather than a general fixpoint.
#guard rejects (generate signature
  (.structRec "xs" intList intList (.recur (.var "xs")))
  (.arrow "xs" intList intList))
#guard rejects (generate signature (.recur (.var "xs")) intList)

-- Named source binders cannot shadow an in-scope binder.
#guard rejects (generate signature
  (.lam "x" .int (.lam "x" .int (.var "x")))
  (.arrow "x" .int (.arrow "y" .int .int)))

-- Signature validation runs before the checker accepts even a simple literal.
private def duplicateSignature : Signature :=
  { signature with datatypes := signature.datatypes ++ signature.datatypes }

#guard rejects (generate duplicateSignature (.int 0) .int)

private def negativeDatatype : Signature := {
  datatypes := [{
    name := "Bad", params := 0,
    ctors := [{ name := "bad", fields := [.arrow "x" (.data "Bad" []) .int] }]
  }]
}

#guard rejects (generate negativeDatatype (.int 0) .int)

-- Calling a measure recursively on a nonrecursive constructor field is invalid.
private def unsafeMeasure : Signature := {
  signature with measures := [{
    name := "len", datatype := "List",
    cases := [
      { ctor := "nil", body := .literal 0 },
      { ctor := "cons", body := .recur 0 }
    ]
  }]
}

#guard rejects (generate unsafeMeasure (.int 0) .int)
#guard rejects (generate signature (.measure "len" (.int 0)) .int)

-- A logical constructor must have recursive fields from the right family.
#guard rejects (generate signature (.int 0)
  (.refine .int (.theory (.eq (.var valueName)
    (.measure "len" (.ctor "cons" [.int 1, .bool true]))))))

-- Unknown predicates retain their declared argument sorts.
#guard rejects (generate signature (.int 0)
  (.refine .int (.kvar "mapLength" [.bool true, .int 0])))

-- Substituting a caller's free `y` must not capture it beneath a stored type's
-- arrow binder named `y`. This is distinct from source-level shadowing.
private def captureType : Ty :=
  .arrow "y" .int (.refine .int (.theory (.eq (.var valueName) (.var "x"))))

#guard (captureType.substTerm "x" (.var "y")).freeVars.contains "y"
#guard match captureType.substTerm "x" (.var "y") with
  | .arrow binder _ _ => binder != "y"
  | _ => false

-- Type substitution also preserves free term names inside refinement arguments.
#guard (Ty.substType (.refine .int (.theory (.eq (.var valueName) (.var "x")))) 0
  (.arrow "x" .int (.var 0))).freeVars.contains "x"
#guard succeeds (wfTy signature {} 512
  (Ty.substType identityTy 0 (.arrow "x" (.var 0) (.var 0))))

private def captureProgram : Expr :=
  .letE "f" (.lam "x" .int (.lam "y" .int (.var "x"))) (
    .letE "y" (.int 0) (
      .letE "g" (.app (.var "f") (.var "y")) (
        .letE "z" (.int 1) (.app (.var "g") (.var "z")))))

-- A small test interpreter chooses concrete witnesses for the generated
-- universal quantifiers. It only handles integer/theory constraints and returns
-- `none` for anything outside that fragment. A false result exposes a concrete
-- failing obligation; it is never used to accept or certify a program.
private def intTerm (environment : List (String × Int)) : LTerm → Option Int
  | .var name => environment.lookup name
  | .int n => some n
  | .add left right => return (← intTerm environment left) + (← intTerm environment right)
  | _ => none

private def intFormula (environment : List (String × Int)) : Formula → Option Bool
  | .truth => some true
  | .falsity => some false
  | .eq left right => return (← intTerm environment left) == (← intTerm environment right)
  | .le left right => return (← intTerm environment left) ≤ (← intTerm environment right)
  | .and left right => return (← intFormula environment left) && (← intFormula environment right)
  | .or left right => return (← intFormula environment left) || (← intFormula environment right)
  | .not body => return !(← intFormula environment body)

private def atWitnesses (environment : List (String × Int)) : Cstr → Option Bool
  | .truth => some true
  | .head (.theory formula) => intFormula environment formula
  | .head (.kvar _ _) | .guard (.kvar _ _) _ => none
  | .guard (.theory formula) body => do
      if ← intFormula environment formula then atWitnesses environment body else some true
  | .all _ .bool _ => none
  | .all name _ body =>
      atWitnesses ((name, if name == "z" then 1 else 0) :: environment) body
  | .conj left right => return (← atWitnesses environment left) && (← atWitnesses environment right)

-- The program returns 0. Checking it against {ν | ν = 1} must therefore leave
-- a failing VC, even though its two occurrences of `y` are in disjoint scopes.
#guard match generate signature captureProgram
    (.refine .int (.theory (.eq (.var valueName) (.int 1)))) with
  | .ok constraints => atWitnesses [] constraints == some false
  | .error _ => false

end SystemFRK.Checks

namespace SystemFRK.Checks

-- A branch-local name must not escape into the match's result refinement.
-- The declarative match rule also requires `result.InScope context`.
private def escapingResult : Ty :=
  .refine .int (.theory (.eq (.var valueName) (.var "head")))

#guard !(escapingResult.freeVars.all (· ∈ (["xs"] : List String)))
#guard rejects (check Examples.signature { vars := [("xs", .data "List" [.int])] }
  (.matchE (.var "xs") [
    ("nil", [], .int 0), ("cons", ["head", "tail"], .var "head")])
  escapingResult)

end SystemFRK.Checks
