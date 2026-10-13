import Demo.LambdaRK

/-!
A readable quotation of the actual polymorphic `map` VC, with a kernel-checked
equation connecting it to the generator. Scalarization, measure handling, and
proof reconstruction now live in the reusable `LambdaRK.Bridge` frontend.
-/
namespace LambdaRK.Examples.MapVC

private def length (name : String) : LTerm := .measure "len" (.var name)
private def summary (left right : String) : Atom :=
  .kvar "mapLength" [length left, length right]
private def equation (name : String) (term : LTerm) : Atom := .theory (.eq (.var name) term)

private def nilCase : Cstr :=
  .guard (equation "xs" (.ctor "nil" [])) (
    .all "$g1" .value (
      .guard (equation "$g1" (.ctor "nil" [])) (.head (summary "xs" "$g1"))))

private def consCase : Cstr :=
  .all "x" .value (.all "tail" .value (
    .guard (equation "xs" (.ctor "cons" [.var "x", .var "tail"])) (
      .all "y" .value (.all "mapped" .value (
        .guard (summary "tail" "mapped") (
          .all "$g2" .value (
            .guard (equation "$g2" (.ctor "cons" [.var "y", .var "mapped"]))
              (.head (summary "xs" "$g2")))))))))

private def query : Cstr :=
  .all "output" .value (.guard (summary "input" "output") (
    .all "$g3" .value (.guard (summary "input" "$g3") (
      .guard (equation "$g3" (.var "output"))
        (.head (.theory (.eq (length "$g3") (length "input"))))))))

/-- All the actual generator's clauses, including its administrative `True`
leaf. The checked equation `generated` ties this readable form to `mapVC`. -/
def raw : Cstr :=
  .conj (.all "$g0" .value .truth) (
    .all "f" .value (.all "input" .value (
      .conj (.all "xs" .value (.conj nilCase consCase)) query)))


set_option maxRecDepth 16384 in
set_option maxHeartbeats 500000 in
theorem generated : generate signature map mapTy = .ok raw := by
  -- These unconditional equations also expose recursive calls whose generated
  -- case lemmas have side conditions. One call at a time keeps the fuel-indexed
  -- mutual recursion small; `cbv` produces ordinary kernel-checked equalities.
  cbv
  repeat
    first
    | rw [checkFuel.eq_def]; cbv
    | rw [synthFuel.eq_def]; cbv
    | rw [subtype.eq_def]; cbv

end LambdaRK.Examples.MapVC
