import Demo.LambdaRK
import Flex.VCG.LambdaRK.SemanticsLemmas

/-!
The solver gate for the actual polymorphic `map` example.  The logical measure
is a partial evaluation relation: scalarization must prove its constructor
facts and preserve the original generated constraint, including its guards.
No source-language fundamental theorem or datatype-model axiom is used here.
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


/-- A scalar candidate is lifted only at the declared two-integer κ signature. -/
def assignment (candidate : Int → Int → Prop) : KAssignment
  | "mapLength", [.int input, .int output] => candidate input output
  | _, _ => False

/-- The nil case, cons case, and length query obtained by eliminating constructor
and measure guards from `raw`. The theorem `lowering_sound` below checks this
particular lowering against the actual generator result in Lean. It is a sound
overapproximation: integer clauses also cover negative values, whereas actual
list lengths are nonnegative. No converse/equivalence is claimed. -/
def Scalar (candidate : Int → Int → Prop) : Prop :=
  candidate 0 0 ∧
  (∀ input output, candidate input output → candidate (1 + input) (1 + output)) ∧
  (∀ input output, candidate input output → output = input)

theorem len_nil : MeasureEval signature "len" (.ctor "nil" []) 0 :=
  .constructor rfl rfl .literal

theorem len_cons {head tail : Value} {n : Int}
    (tailLength : MeasureEval signature "len" tail n) :
    MeasureEval signature "len" (.ctor "cons" [head, tail]) (1 + n) :=
  .constructor rfl rfl (.add .literal (.recur rfl tailLength))

@[simp] theorem logical_var {environment : Environment} {name : String} {value : Value} :
    LogicalEval signature environment (.var name) value ↔ environment.lookup name = some value := by
  constructor
  · intro h; cases h; assumption
  · exact .var

@[simp] theorem logical_nil {environment : Environment} {value : Value} :
    LogicalEval signature environment (.ctor "nil" []) value ↔ value = .ctor "nil" [] := by
  constructor
  · intro h; cases h with | ctor h => cases h; rfl
  · intro h; subst value; exact .ctor .nil

@[simp] theorem logical_cons {environment : Environment} {head tail : LTerm} {value : Value} :
    LogicalEval signature environment (.ctor "cons" [head, tail]) value ↔
      ∃ x xs, LogicalEval signature environment head x ∧
        LogicalEval signature environment tail xs ∧ value = .ctor "cons" [x, xs] := by
  constructor
  · intro h
    cases h with
    | ctor h => cases h with
      | cons hx h => cases h with
        | cons hxs h => cases h; exact ⟨_, _, hx, hxs, rfl⟩
  · rintro ⟨x, xs, hx, hxs, rfl⟩
    exact .ctor (.cons hx (.cons hxs .nil))

@[simp] theorem logical_len {environment : Environment} {term : LTerm} {value : Value} :
    LogicalEval signature environment (.measure "len" term) value ↔
      ∃ argument n, LogicalEval signature environment term argument ∧
        MeasureEval signature "len" argument n ∧ value = .int n := by
  constructor
  · intro h; cases h with | measure he hm => exact ⟨_, _, he, hm, rfl⟩
  · rintro ⟨argument, n, he, hm, rfl⟩; exact .measure he hm

@[simp] theorem kvar_lengths {candidate : Int → Int → Prop} {environment : Environment}
    {left right : LTerm} :
    Atom.denote signature (assignment candidate) environment
      (.kvar "mapLength" [.measure "len" left, .measure "len" right]) ↔
      ∃ x y n m, LogicalEval signature environment left x ∧
        LogicalEval signature environment right y ∧
        MeasureEval signature "len" x n ∧ MeasureEval signature "len" y m ∧ candidate n m := by
  constructor
  · rintro ⟨values, h, hk⟩
    cases h with
    | cons hx h => cases h with
      | cons hy h =>
        cases h
        obtain ⟨x,n,hleft,hn,rfl⟩ := logical_len.mp hx
        obtain ⟨y,m,hright,hm,rfl⟩ := logical_len.mp hy
        exact ⟨x,y,n,m,hleft,hright,hn,hm,hk⟩
  · rintro ⟨x,y,n,m,hx,hy,hn,hm,hk⟩
    exact ⟨_, .cons (.measure hx hn) (.cons (.measure hy hm) .nil), hk⟩

@[simp] theorem theory_denote {candidate : Int → Int → Prop}
    {environment : Environment} {formula : Formula} :
    Atom.denote signature (assignment candidate) environment (.theory formula) ↔
      formula.denote signature environment := Iff.rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem lowering_sound (candidate : Int → Int → Prop) (scalar : Scalar candidate) :
    raw.Valid signature (assignment candidate) := by
  intro environment
  unfold raw nilCase consCase query equation summary length
  simp [Cstr.denote, LSort.contains, Formula.denote, Environment.bind, List.lookup_cons]
  obtain ⟨initial, step, safe⟩ := scalar
  intro input
  constructor
  · intro xs
    constructor
    · rintro rfl
      exact ⟨0, len_nil, 0, len_nil, initial⟩
    · rintro head tail rfl mappedHead mappedTail n tailLength m mappedLength related
      exact ⟨1 + n, len_cons tailLength, 1 + m, len_cons mappedLength, step n m related⟩
  · intro output _ _ _ _ _ result n inputLength m resultLength related _
    have same := safe n m related
    subst m
    exact ⟨.int n, ⟨n, resultLength, rfl⟩, ⟨n, inputLength, rfl⟩⟩

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
