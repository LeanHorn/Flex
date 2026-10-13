import Flex.VCG.SystemFRK
import Flex.VCG.SystemFRK.Bridge
import Flex.VCG.SystemFRK.Notation

/-!
Ten mechanized SystemFRK examples. Successful examples prove that the actual
executable generator returns their VC, prove its validity, and use the public
total-correctness theorem. Operational witnesses and the final negative example
check that the claims have content. Only example 6 uses an external solver (Z3).

Programs use `[frk| ...]`; types use `[frkTy| ...]`. Type binders are named,
and `⌜...⌝` embeds an existing definition. Both expand to the original core syntax.

Run: `lake lean Demo/SystemFRK.lean`.
-/
namespace SystemFRK.Examples

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

private def noPredicates : KAssignment := fun _ _ => False

/-- The generation equation in each example rules out the error branch. -/
private def computedVC (sig : Signature) (expression : Expr) (type : Ty) : Cstr :=
  match generate sig expression type with
  | .ok constraint => constraint
  | .error _ => .head (.theory .falsity)

macro "frk_compute" : tactic => `(tactic| (cbv; repeat first
  | rw [checkFuel.eq_def]; cbv
  | rw [synthFuel.eq_def]; cbv
  | rw [subtype.eq_def]; cbv))

macro "frk_reduce_vc" : tactic => `(tactic| (conv =>
  arg 3
  cbv
  repeat first
    | rw [checkFuel.eq_def]; cbv
    | rw [synthFuel.eq_def]; cbv
    | rw [subtype.eq_def]; cbv))

macro "frk_valid" : tactic => `(tactic| (
  simp (config := { contextual := true })
    [Cstr.Valid, system_frk_bridge, Environment.bind, List.lookup_cons,
      Bridge.measure_ctor, Signature.findMeasure]
    <;> grind [MeasureEval.deterministic]))

/-- The map signature contains one parameterized datatype, one total measure,
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

/-! ## 1. Polymorphic identity, applied to every integer -/

def identityTy : Ty := [frkTy| ∀ α, (x : α) → α]
def identity : Expr := [frk| Λ α => fun (x : α) => x]

namespace Identity

def vc : Cstr := computedVC {} identity identityTy

theorem generated : generate {} identity identityTy = .ok vc := by frk_compute

theorem valid : vc.Valid {} noPredicates := by
  unfold vc
  frk_reduce_vc
  frk_valid

theorem total_correct : ∃ value, Eval {} [] none identity value ∧
    identityTy.denote {} (({} : Signature).datatypeModel noPredicates) noPredicates [] [] value :=
  generated_total_correctness {} noPredicates identity identityTy vc generated valid

/-- Eliminate the universal type at an inhabited singleton candidate, then
apply the resulting function. Merely returning a closure would not suffice. -/
theorem applied (n : Int) :
    Eval {} [] none (.app (.tyApp identity .int) (.int n)) (.int n) := by
  obtain ⟨value, evaluated, typed⟩ := total_correct
  simp only [identityTy, Ty.denote, List.getElem?_cons_zero, Option.getD_some] at typed
  obtain ⟨function, instantiated, functionTyped⟩ := typed (fun value => value = .int n)
  obtain ⟨result, applied, resultTyped⟩ := functionTyped.2 (.int n) rfl
  cases resultTyped
  exact .app (.tyApp evaluated instantiated) .int applied

end Identity

/-! ## 2. Impredicative identity: id [∀α. α → α] id -/
namespace Impredicative

def program : Expr := [frk|
  let id := ⌜identity⌝;
  id[⌜identityTy⌝] id
]
def vc : Cstr := computedVC {} program identityTy

theorem generated : generate {} program identityTy = .ok vc := by frk_compute

theorem valid : vc.Valid {} noPredicates := by
  unfold vc
  frk_reduce_vc
  frk_valid

theorem total_correct : ∃ value, Eval {} [] none program value ∧
    identityTy.denote {} (({} : Signature).datatypeModel noPredicates) noPredicates [] [] value :=
  generated_total_correctness {} noPredicates program identityTy vc generated valid

end Impredicative

/-! ## 3. Higher-order polymorphic composition -/
namespace Composition

def type : Ty := [frkTy| ∀ α β γ,
  (f : (b : β) → γ) → (g : (a : α) → β) → (x : α) → γ
]

def program : Expr := [frk|
  Λ α β γ =>
  fun (f : (b : β) → γ) (g : (a : α) → β) (x : α) =>
    let y := g x;
    f y
]
def vc : Cstr := computedVC {} program type

theorem generated : generate {} program type = .ok vc := by frk_compute

theorem valid : vc.Valid {} noPredicates := by
  unfold vc
  frk_reduce_vc
  frk_valid

theorem total_correct : ∃ value, Eval {} [] none program value ∧
    type.denote {} (({} : Signature).datatypeModel noPredicates) noPredicates [] [] value :=
  generated_total_correctness {} noPredicates program type vc generated valid

end Composition

/-! ## 4. Dependent application without capturing a caller's free name -/
namespace Capture

def program : Expr := [frk|
  let f := fun (x : Int) (y : Int) => x;
  let y := 0;
  let g := f y;
  let z := 1;
  g z
]
def type : Ty := [frkTy| {v : Int | v = 0}]
def vc : Cstr := computedVC {} program type

theorem generated : generate {} program type = .ok vc := by frk_compute

theorem valid : vc.Valid {} noPredicates := by
  unfold vc
  frk_reduce_vc
  frk_valid

theorem total_correct : ∃ value, Eval {} [] none program value ∧
    type.denote {} (({} : Signature).datatypeModel noPredicates) noPredicates [] [] value :=
  generated_total_correctness {} noPredicates program type vc generated valid

theorem returns_zero : Eval {} [] none program (.int 0) := by
  obtain ⟨value, evaluated, typed⟩ := total_correct
  simp only [type, Ty.denote, Atom.denote, Formula.denote] at typed
  obtain ⟨_, common, observed, literal⟩ := typed
  cases literal
  cases observed with
  | var lookup =>
      have same : value = .int 0 := Option.some.inj lookup
      exact same ▸ evaluated

end Capture

/-! ## 5. A constructor program with a singleton-length refinement -/
namespace Singleton

def sig : Signature := { signature with kvars := [] }
def program : Expr := [frk|
  let empty := ctor nil[Int]();
  ctor cons[Int](7, empty)
]
def type : Ty := [frkTy| {v : List[Int] | len(v) = 1}]
def vc : Cstr := computedVC sig program type

theorem generated : generate sig program type = .ok vc := by frk_compute

theorem valid : vc.Valid sig noPredicates := by
  unfold vc
  frk_reduce_vc
  simp only [sig, signature]
  frk_valid

theorem total_correct : ∃ value, Eval sig [] none program value ∧
    type.denote sig (sig.datatypeModel noPredicates) noPredicates [] [] value :=
  generated_total_correctness sig noPredicates program type vc generated valid

end Singleton

/-! ## 6. Polymorphic structural map with a solver-inferred length invariant -/

def mapTy : Ty := [frkTy| ∀ α β,
  (f : (item : α) → β) →
  (input : List[α]) → {v : List[β] | len(v) = len(input)}
]

def map : Expr := [frk|
  Λ α β =>
  fun (f : (item : α) → β) (input : List[α]) =>
    let output :=
      (fix (xs : List[α]) : {v : List[β] | κ mapLength(len(xs), len(v))} =>
        match xs with
        | nil => ctor nil[β]()
        | cons x tail =>
          let y := f x;
          let mapped := recur tail;
          ctor cons[β](y, mapped)
        end) input;
    output
]

namespace MapVC

private def length (name : String) : LTerm := .measure "len" (.var name)
private def summary (left right : String) : Atom :=
  .kvar "mapLength" [length left, length right]
private def equation (name : String) (term : LTerm) : Atom := .theory (.eq (.var name) term)
private def defined (name : String) (body : Cstr) : Cstr :=
  .guard (.theory (.eq (length name) (length name))) body

private def nilCase : Cstr :=
  .guard (equation "xs" (.ctor "nil" [])) (
    .all "$g1" .value (
      .guard (equation "$g1" (.ctor "nil" [])) (.head (summary "xs" "$g1"))))

private def consCase : Cstr :=
  .all "x" .value (.all "tail" .value (defined "tail" (
    .guard (equation "xs" (.ctor "cons" [.var "x", .var "tail"])) (
      .all "y" .value (.all "mapped" .value (defined "mapped" (
        .guard (summary "tail" "mapped") (
          .all "$g2" .value (
            .guard (equation "$g2" (.ctor "cons" [.var "y", .var "mapped"]))
              (.head (summary "xs" "$g2")))))))))))

private def query : Cstr :=
  .all "output" .value (defined "output" (.guard (summary "input" "output") (
    .all "$g3" .value (.guard (summary "input" "$g3") (
      .guard (equation "$g3" (.var "output"))
        (.head (.theory (.eq (length "$g3") (length "input")))))))))

/-- All the actual generator's clauses, including its administrative `True`
leaf and measure-definedness guards. `generated` ties this readable form to the program. -/
def raw : Cstr :=
  .conj (.all "$g0" .value .truth) (
    .all "f" .value (.all "input" .value (defined "input" (
      .conj (.all "xs" .value (defined "xs" (.conj nilCase consCase))) query))))


set_option maxRecDepth 16384 in
set_option maxHeartbeats 500000 in
theorem generated : generate signature map mapTy = .ok raw := by frk_compute

end MapVC

namespace MapVC

open Lean Meta Elab Tactic

elab "synthesize_map_invariant" : tactic => withMainContext do
  let config : Flex.CHC.Config := match ← IO.getEnv "CHC_ELDARICA" with
    | some executable => { backend := .eldarica, executable := some executable }
    | none => { backend := .spacer }
  let report ← match ← SystemFRK.Bridge.solveGoal (← getMainGoal) config with
    | .solved report => pure report
    | .partial report =>
      throwError "map invariant left {report.obligations.size} obligations: {repr report.diagnostics}"
    | .failed message => throwError "map synthesis failed: {message}"
  unless report.checkedClauses == 4 && report.diagnostics.isEmpty do
    throwError "map source lowering unexpectedly changed: {repr report.diagnostics}"
  let some solver := report.solver
    | throwError "map synthesis unexpectedly bypassed the external solver"
  unless solver.problem.relations.size == 1 && solver.problem.clauseCount == 3 do
    throwError "map scalarization unexpectedly changed its relation or clause count"
  for (name, value) in report.witnesses do
    logInfo m!"map invariant {name} ({repr config.backend}): {value}"
  for timing in solver.timings do
    logInfo m!"map {repr timing.stage}: {timing.elapsedNs / 1000000} ms"
  setGoals []

/-- The witness is imported from the actual solver response and every clause
is then certified; no handwritten predicate is supplied by this theorem. -/
theorem raw_solved : ∃ assignment, raw.Valid signature assignment := by
  synthesize_map_invariant

/-- The proof targets `generate signature map mapTy`, not a handwritten scalar
toy. Its only solver dependency is the checked witness in `raw_solved`. -/
theorem generated_valid : ∃ κ constraints,
    generate signature map mapTy = .ok constraints ∧ constraints.Valid signature κ := by
  obtain ⟨assignment, certified⟩ := raw_solved
  exact ⟨assignment, raw, generated, certified⟩

/-- Both real solver paths certify the source program's semantic type, including
its impredicative function and length-preservation specification. -/
theorem map_total_correct : ∃ κ value,
    Eval signature [] none map value ∧
      mapTy.denote signature (signature.datatypeModel κ) κ [] [] value := by
  obtain ⟨κ, constraint, generated, valid⟩ := generated_valid
  obtain ⟨value, evaluated, typed⟩ := generated_total_correctness
    signature κ map mapTy constraint generated valid
  exact ⟨κ, value, evaluated, typed⟩

end MapVC

namespace MapBehavior

def encode : List Int → Value
  | [] => .ctor "nil" []
  | head :: tail => .ctor "cons" [.int head, encode tail]

def inputExpr : List Int → Expr
  | [] => .ctor "nil" [.int] []
  | head :: tail => .ctor "cons" [.int] [.int head, inputExpr tail]

theorem input_evaluates (values : List Int) :
    Eval signature [] none (inputExpr values) (encode values) := by
  induction values with
  | nil => exact .ctor .nil
  | cons head tail ih => exact .ctor (.cons .int (.cons ih .nil))

def intLists (assignment : KAssignment) : Candidate :=
  (signature.datatypeModel assignment).datatype "List" [LSort.int.contains]

/-- The canonical datatype interpretation contains every finite integer list,
including nonempty lists. No datatype-inhabitation premise is assumed. -/
theorem input_typed (assignment : KAssignment) (values : List Int) :
    intLists assignment (encode values) := by
  have laws := signature.datatypeModel_laws assignment (by cbv)
  induction values with
  | nil =>
      apply (laws "List" [LSort.int.contains] _).mpr
      refine ⟨signature.datatypes[0]!, by simp [signature], rfl, rfl,
        { name := "nil", fields := [] }, by simp [signature], [], rfl, .nil⟩
  | cons head tail ih =>
      apply (laws "List" [LSort.int.contains] _).mpr
      refine ⟨signature.datatypes[0]!, by simp [signature], rfl, rfl,
        { name := "cons", fields := [.var 0, .data "List" [.var 0]] },
        by simp [signature], [.int head, encode tail], rfl, ?_⟩
      refine .cons ?_ (.cons ?_ .nil)
      · simpa only [Ty.denote, List.getElem?_cons_zero, Option.getD_some] using
          (show LSort.int.contains (.int head) from ⟨head, rfl⟩)
      · simpa only [Ty.denote, List.map_cons, List.map_nil,
          List.getElem?_cons_zero, Option.getD_some, intLists] using ih

theorem input_length (values : List Int) :
    MeasureEval signature "len" (encode values) (Int.ofNat values.length) := by
  induction values with
  | nil => exact .constructor rfl rfl .literal
  | cons head tail ih =>
      have evaluation : MeasureEval signature "len" (encode (head :: tail))
          (1 + Int.ofNat tail.length) :=
        .constructor rfl rfl (.add .literal (.recur rfl ih))
      have same : 1 + Int.ofNat tail.length = Int.ofNat (head :: tail).length := by
        simp [Int.ofNat_eq_natCast, Int.add_comm]
      exact same ▸ evaluation

/-- Invoke the actual certified map, instantiated twice and applied to a total
constant function and any finite integer list. The application shows both type
instantiations and both runtime arguments. -/
theorem map_runs_on_every_int_list (values : List Int) :
    ∃ assignment result,
      Eval signature [] none
        [frk| ⌜map⌝[Int][Int] (fun (auditElement : Int) => 7) ⌜inputExpr values⌝] result ∧
      intLists assignment result ∧
      MeasureEval signature "len" result (Int.ofNat values.length) := by
  obtain ⟨assignment, polymorphic, evaluated, typed⟩ := MapVC.map_total_correct
  simp only [mapTy, Ty.denote, List.map_cons, List.map_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at typed
  obtain ⟨once, firstApplication, onceTyped⟩ := typed LSort.int.contains
  obtain ⟨twice, secondApplication, twiceTyped⟩ := onceTyped LSort.int.contains
  let function : Value := .closure "auditElement" (.int 7) [] none
  obtain ⟨partialMap, functionApplication, partialTyped⟩ := twiceTyped.2 function
    (by refine ⟨True.intro, ?_⟩; intro _ _; exact ⟨.int 7, .closure .int, 7, rfl⟩)
  obtain ⟨result, listApplication, resultTyped⟩ :=
    partialTyped.2 (encode values) (input_typed assignment values)
  obtain ⟨listTyped, measured⟩ := resultTyped
  refine ⟨assignment, result,
    .app (.app (.tyApp (.tyApp evaluated firstApplication) secondApplication) .lam
      functionApplication) (input_evaluates values) listApplication,
    listTyped, ?_⟩
  simp only [Atom.denote, Formula.denote] at measured
  obtain ⟨common, outputObservation, inputObservation⟩ := measured
  have inputObservation' : LogicalEval signature
      (Environment.bind (Environment.bind (Environment.bind [] "f" function)
        "input" (encode values)) valueName result)
      (.measure "len" (.var "input")) (.int (Int.ofNat values.length)) :=
    .measure (.var rfl) (input_length values)
  have same := inputObservation.deterministic inputObservation'
  subst common
  cases outputObservation with
  | measure observed length =>
      cases observed with
      | var lookup =>
          have same : result = _ := Option.some.inj lookup
          subst_vars
          exact length

end MapBehavior

/-! ## 7. A recursive measure combining integer fields and a recursive tail -/
namespace WeightedMeasure

def sig : Signature := {
  datatypes := [{ name := "Weighted", params := 0, ctors := [
    { name := "end", fields := [] },
    { name := "step", fields := [.int, .data "Weighted" []] }
  ] }]
  measures := [{ name := "weight", datatype := "Weighted", cases := [
    { ctor := "end", body := .literal 0 },
    { ctor := "step", body := .add (.field 0) (.recur 1) }
  ] }]
}

def program : Expr := [frk|
  let empty := ctor «end»[]();
  let tail := ctor step[](5, empty);
  let input := ctor step[](7, tail);
  measure weight input
]
def type : Ty := [frkTy| {v : Int | v = 12}]
def vc : Cstr := computedVC sig program type

theorem generated : generate sig program type = .ok vc := by frk_compute

theorem valid : vc.Valid sig noPredicates := by
  unfold vc
  frk_reduce_vc
  simp only [sig]
  frk_valid

theorem total_correct : ∃ value, Eval sig [] none program value ∧
    type.denote sig (sig.datatypeModel noPredicates) noPredicates [] [] value :=
  generated_total_correctness sig noPredicates program type vc generated valid

end WeightedMeasure

/-! ## 8. Positive recursive datatypes with function and polymorphic fields -/
namespace HigherOrderData

def sig : Signature := {
  datatypes := [{ name := "Suspended", params := 1, ctors := [
    { name := "stop", fields := [] },
    { name := "function", fields := [.arrow "argument" .int (.data "Suspended" [.var 0])] },
    { name := "polymorphic", fields := [.all (.data "Suspended" [.var 1])] }
  ] }]
}

def type : Ty := [frkTy| Suspended[Int]]
def program : Expr := [frk|
  let thunk := fun (argument : Int) => ctor stop[Int]();
  let functionNode := ctor function[Int](thunk);
  let poly := Λ α => ctor stop[Int]();
  ctor polymorphic[Int](poly)
]
def vc : Cstr := computedVC sig program type

theorem generated : generate sig program type = .ok vc := by frk_compute

theorem valid : vc.Valid sig noPredicates := by
  unfold vc
  frk_reduce_vc
  frk_valid

theorem total_correct : ∃ value, Eval sig [] none program value ∧
    type.denote sig (sig.datatypeModel noPredicates) noPredicates [] [] value :=
  generated_total_correctness sig noPredicates program type vc generated valid

end HigherOrderData

/-! ## 9. Recursive calls delayed through both type and ordinary closures -/
namespace DelayedRecursion

def nilCode : Expr := [frk| fun (ignored : Int) => 0]
def consCode : Expr := [frk|
  fun (ignored : Int) =>
    let later := recur tail;
    let call := later[Int];
    call 0
]
def body : Expr := [frk|
  match xs with
  | nil => Λ α => ⌜nilCode⌝
  | cons head tail => Λ α => ⌜consCode⌝
  end
]
def loop : Value := .recursiveClosure "xs" body []
def singleton : Value := .ctor "cons" [.int 7, .ctor "nil" []]
def rootEnv : Environment :=
  [("head", .int 7), ("tail", .ctor "nil" []), ("xs", singleton)]
def emptyEnv : Environment := [("xs", .ctor "nil" [])]
def deferred : Value := .typeClosure consCode rootEnv (some loop)

theorem root_returns : Apply {} loop singleton deferred := by
  apply Apply.recursiveClosure
  exact .matchE (.var rfl) rfl rfl .tyLam

theorem empty_returns : Apply {} loop (.ctor "nil" [])
    (.typeClosure nilCode emptyEnv (some loop)) := by
  apply Apply.recursiveClosure
  exact .matchE (.var rfl) rfl rfl .tyLam

/-- Both captured frames survive returning from the root call. In particular,
the `none` caller frame cannot accidentally replace the captured function. -/
theorem delayed_recursion_evaluates :
    Eval {} [("loop", loop), ("input", singleton)] none
      [frk|
        let deferred := loop input;
        let instantiated := deferred[Int];
        instantiated 99
      ] (.int 0) := by
  apply Eval.letE (.app (.var rfl) (.var rfl) root_returns)
  apply Eval.letE (.tyApp (.var rfl) (.closure .lam))
  apply Eval.app (.var rfl) .int
  apply Apply.closure
  apply Eval.letE (.recur rfl (.var rfl) empty_returns)
  apply Eval.letE (.tyApp (.var rfl) (.closure .lam))
  exact .app (.var rfl) .int (.closure .int)


def sig : Signature := { signature with kvars := [] }
def program : Expr := [frk|
  let loop := fix (xs : List[Int]) : ∀ α, (ignored : Int) → Int => ⌜body⌝;
  let empty := ctor nil[Int]();
  let input := ctor cons[Int](7, empty);
  let deferred := loop input;
  let instantiated := deferred[Int];
  instantiated 99
]
def vc : Cstr := computedVC sig program .int

theorem generated : generate sig program .int = .ok vc := by frk_compute

theorem valid : vc.Valid sig noPredicates := by
  unfold vc
  frk_reduce_vc
  frk_valid

theorem total_correct : ∃ value, Eval sig [] none program value ∧
    Ty.int.denote sig (sig.datatypeModel noPredicates) noPredicates [] [] value :=
  generated_total_correctness sig noPredicates program .int vc generated valid

end DelayedRecursion

/-! ## 10. A generated false specification has no certificate -/
namespace Nonvacuity

/-- An impredicative universal type cannot manufacture an arbitrary value. -/
theorem forall_alpha_alpha_empty (signature : Signature) (model : DataModel)
    (assignment : KAssignment) (types : TypeEnvironment) (environment : Environment)
    (value : Value) : ¬ ([frkTy| ∀ α, α]).denote signature model assignment types environment value := by
  intro typed
  simp only [Ty.denote, List.getElem?_cons_zero, Option.getD_some] at typed
  obtain ⟨_, _, impossible⟩ := typed (fun _ => False)
  exact impossible

def zeroAsOne : Ty := [frkTy| {v : Int | v = 1}]

def zeroAsOneVC : Cstr := .all "$g0" .int
  (.guard (.theory (.eq (.var "$g0") (.int 0)))
    (.head (.theory (.eq (.var "$g0") (.int 1)))))

set_option maxRecDepth 16384 in
theorem false_spec_generated : generate {} (.int 0) zeroAsOne = .ok zeroAsOneVC := by frk_compute

/-- Refute the actual generated obligation directly, independently of the
soundness theorem. In particular its guard has a satisfying witness. -/
theorem false_spec_invalid (assignment : KAssignment) :
    ¬ zeroAsOneVC.Valid {} assignment := by
  intro valid
  have guardHolds : (Atom.theory (.eq (.var "$g0") (.int 0))).denote {}
      assignment [("$g0", .int 0)] := ⟨.int 0, .var rfl, .int⟩
  obtain ⟨value, variableEval, literal⟩ := valid [] (.int 0) ⟨0, rfl⟩ guardHolds
  cases variableEval with
  | var lookup =>
    have equal : Value.int 0 = value := Option.some.inj lookup
    subst value
    cases literal

/-- No successfully generated closed program can certify a false refinement. -/
theorem false_refinement_uncertifiable (signature : Signature) (expression : Expr)
    (base : Ty) (constraint : Cstr) (assignment : KAssignment)
    (generated : generate signature expression (.refine base (.theory .falsity)) = .ok constraint) :
    ¬ constraint.Valid signature assignment := by
  intro valid
  obtain ⟨_, _, typed⟩ := generated_total_correctness signature assignment expression
    (.refine base (.theory .falsity)) constraint generated valid
  simp only [Ty.denote, Atom.denote, Formula.denote, and_false] at typed

/-- The evaluation relation cannot apply an integer as a function. -/
theorem stuck_does_not_evaluate (signature : Signature) (value : Value) :
    ¬ Eval signature [] none [frk| 0 1] value := by
  intro evaluated
  cases evaluated with
  | app function _ applied => cases function; cases applied

theorem stuck_uncertifiable (signature : Signature) (type : Ty) :
    ¬ ∃ assignment constraint,
      generate signature [frk| 0 1] type = .ok constraint ∧
      constraint.Valid signature assignment := by
  rintro ⟨assignment, constraint, generated, valid⟩
  obtain ⟨value, evaluated, _⟩ := generated_total_correctness signature assignment
    [frk| 0 1] type constraint generated valid
  exact stuck_does_not_evaluate signature value evaluated

end Nonvacuity

/-! Check transitive axiom dependencies of the mechanization and these examples. -/
open Lean Meta Elab in
run_elab do
  let mut checked : Nat := 0
  for (name, info) in (← getEnv).constants.toList do
    let userName := (privateToUserName? name).getD name
    if (`SystemFRK).isPrefixOf userName then
      let logical ← match info with
        | .thmInfo _ | .axiomInfo _ => pure true
        | .defnInfo _ | .opaqueInfo _ =>
            if info.isUnsafe then pure false else isProp info.type
        | _ => pure false
      if logical then
        let axioms ← collectAxioms name
        unless axioms.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do
          throwError "nonstandard axioms in {name}: {axioms}"
        checked := checked + 1
  logInfo m!"SystemFRK: checked {checked} logical declarations; only standard Lean axioms"

end SystemFRK.Examples
