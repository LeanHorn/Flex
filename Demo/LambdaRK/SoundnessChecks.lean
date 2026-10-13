import Demo.LambdaRK

/-! Focused regressions for proof-driven fixes: generated witness freshness and
scope checks at recursive synthesis/checking boundaries. These are checker
regressions, not additional frontend case-study programs. -/
namespace LambdaRK.SoundnessChecks

private def rejects : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def refersTo (name : String) : Ty :=
  .refine .int (.theory (.eq (.var valueName) (.var name)))

-- Either generated counter value can collide with a source or target free
-- logical name. The fresh binder must change while those references survive.
private def subtypePreservesNames (start : Nat) : Bool :=
  match subtype {} {} 16 (refersTo "$g0") (refersTo "$g1") start with
  | .ok (.all binder .int (.guard (.theory (.eq (.var lhs) (.var source)))
        (.head (.theory (.eq (.var rhs) (.var target))))), finish) =>
      binder != "$g0" && binder != "$g1" && lhs == binder && rhs == binder &&
        source == "$g0" && target == "$g1" && finish == start + 1
  | _ => false

#guard subtypePreservesNames 0
#guard subtypePreservesNames 1

-- Public low-level entry points may receive malformed contexts. Successful
-- variable synthesis must still run finishSynth's formation certificate.
#guard rejects (synth {} { vars := [("x", .var 0)] } (.var "x"))
#guard rejects (synth {} { vars := [("x", refersTo "missing")] } (.var "x"))

-- Checking directly, rather than through the outer wfTy wrapper, must reject
-- a result refinement mentioning a branch-local name outside that branch.
#guard rejects (checkFuel Examples.signature
  { vars := [("xs", .data "List" [.int])] } 16 (.int 0) (refersTo "head") 0)

-- The certificate accepts all measure-body forms: constants, integer fields,
-- direct recursive fields, and their sums, over a parameterized datatype.
private def measuredSignature : Signature := {
  datatypes := [{ name := "Measured", params := 1, ctors := [
    { name := "end", fields := [] },
    { name := "step", fields := [.int, .var 0, .data "Measured" [.var 0]] }
  ] }]
  measures := [{ name := "weight", datatype := "Measured", cases := [
    { ctor := "end", body := .literal 0 },
    { ctor := "step", body := .add (.field 0) (.recur 2) }
  ] }]
}

#guard match measuredSignature.validate with | .ok () => true | .error _ => false

end LambdaRK.SoundnessChecks
