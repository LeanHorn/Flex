import Flex.VCG.SystemFRK.Semantics.Measures
import Flex.VCG.SystemFRK.Bridge.Attributes

/-! Semantic normalization in the opt-in `system_frk_bridge` simp set.
Measure observations retain their evaluation witnesses. -/

namespace SystemFRK.Bridge

/-- Curried predicates over the declared Int, Bool, or residual Value arguments. -/
@[reducible] def PredicateType : List LSort → Type
  | [] => Prop
  | .int :: sorts => Int → PredicateType sorts
  | .bool :: sorts => Bool → PredicateType sorts
  | .value :: sorts => Value → PredicateType sorts

/-- Decode runtime arguments; reject wrong arities and sorts. -/
def applyPredicate : (sorts : List LSort) → PredicateType sorts → List Value → Prop
  | [], predicate, values => match values with
      | [] => predicate
      | _ => False
  | .int :: sorts, predicate, values => match values with
      | .int integer :: values => applyPredicate sorts (predicate integer) values
      | _ => False
  | .bool :: sorts, predicate, values => match values with
      | .bool boolean :: values => applyPredicate sorts (predicate boolean) values
      | _ => False
  | .value :: sorts, predicate, values => match values with
      | value :: values => applyPredicate sorts (predicate value) values
      | _ => False

/-- Extend a κ-assignment by a typed predicate. -/
def bindPredicate (name : String) (sorts : List LSort)
    (predicate : PredicateType sorts) (rest : KAssignment) : KAssignment :=
  fun other values => if other == name then applyPredicate sorts predicate values else rest other values

theorem bindPredicate_self :
    bindPredicate name sorts predicate rest name values ↔
      applyPredicate sorts predicate values := by
  simp [bindPredicate]

theorem bindPredicate_other (different : other ≠ name) :
    bindPredicate name sorts predicate rest other values ↔ rest other values := by
  simp [bindPredicate, different]

@[system_frk_bridge] theorem applyPredicate_nil_nil :
    applyPredicate [] predicate [] ↔ predicate := Iff.rfl

@[system_frk_bridge] theorem applyPredicate_nil_cons :
    applyPredicate [] predicate (value :: values) ↔ False := Iff.rfl

@[system_frk_bridge] theorem applyPredicate_cons_nil :
    applyPredicate (sort :: sorts) predicate [] ↔ False := by
  cases sort <;> exact Iff.rfl

@[system_frk_bridge] theorem applyPredicate_int_cons :
    applyPredicate (.int :: sorts) predicate (value :: values) ↔
      ∃ integer, value = .int integer ∧ applyPredicate sorts (predicate integer) values := by
  cases value with
  | int integer =>
    constructor
    · intro h; exact ⟨integer, rfl, h⟩
    · rintro ⟨_, equal, h⟩; cases equal; exact h
  | bool | ctor | closure | typeClosure | recursiveClosure =>
    constructor
    · exact False.elim
    · rintro ⟨_, equal, _⟩; cases equal

@[system_frk_bridge] theorem applyPredicate_bool_cons :
    applyPredicate (.bool :: sorts) predicate (value :: values) ↔
      ∃ boolean, value = .bool boolean ∧ applyPredicate sorts (predicate boolean) values := by
  cases value with
  | bool boolean =>
    constructor
    · intro h; exact ⟨boolean, rfl, h⟩
    · rintro ⟨_, equal, h⟩; cases equal; exact h
  | int | ctor | closure | typeClosure | recursiveClosure =>
    constructor
    · exact False.elim
    · rintro ⟨_, equal, _⟩; cases equal

@[system_frk_bridge] theorem applyPredicate_value_cons :
    applyPredicate (.value :: sorts) predicate (value :: values) ↔
      applyPredicate sorts (predicate value) values := Iff.rfl

attribute [system_frk_bridge] bindPredicate

@[system_frk_bridge] theorem logical_var :
    LogicalEval signature environment (.var name) value ↔
      environment.lookup name = some value := by
  constructor
  · intro evaluation; cases evaluation; assumption
  · exact .var

@[system_frk_bridge] theorem logical_int :
    LogicalEval signature environment (.int integer) value ↔ value = .int integer := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · rintro rfl; exact .int

@[system_frk_bridge] theorem logical_bool :
    LogicalEval signature environment (.bool boolean) value ↔ value = .bool boolean := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · rintro rfl; exact .bool

@[system_frk_bridge] theorem logical_add :
    LogicalEval signature environment (.add left right) value ↔
      ∃ m n, LogicalEval signature environment left (.int m) ∧
        LogicalEval signature environment right (.int n) ∧ value = .int (m + n) := by
  constructor
  · intro evaluation; cases evaluation with
    | add left right => exact ⟨_, _, left, right, rfl⟩
  · rintro ⟨_, _, left, right, rfl⟩; exact .add left right

@[system_frk_bridge] theorem logical_ctor :
    LogicalEval signature environment (.ctor name fields) value ↔
      ∃ values, LogicalListEval signature environment fields values ∧
        value = .ctor name values := by
  constructor
  · intro evaluation; cases evaluation with | ctor fields => exact ⟨_, fields, rfl⟩
  · rintro ⟨_, fields, rfl⟩; exact .ctor fields

@[system_frk_bridge] theorem logical_measure :
    LogicalEval signature environment (.measure name term) value ↔
      ∃ argument result, LogicalEval signature environment term argument ∧
        MeasureEval signature name argument result ∧ value = .int result := by
  constructor
  · intro evaluation; cases evaluation with
    | measure term measure => exact ⟨_, _, term, measure, rfl⟩
  · rintro ⟨_, _, term, measure, rfl⟩; exact .measure term measure

@[system_frk_bridge] theorem logical_list_nil :
    LogicalListEval signature environment [] values ↔ values = [] := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · rintro rfl; exact .nil

@[system_frk_bridge] theorem logical_list_cons :
    LogicalListEval signature environment (term :: terms) values ↔
      ∃ head tail, LogicalEval signature environment term head ∧
        LogicalListEval signature environment terms tail ∧ values = head :: tail := by
  constructor
  · intro evaluation; cases evaluation with
    | cons head tail => exact ⟨_, _, head, tail, rfl⟩
  · rintro ⟨_, _, head, tail, rfl⟩; exact .cons head tail

/-- Eliminate evaluation witnesses before list inversion introduces intermediate equalities. -/
@[system_frk_bridge ↓] theorem logical_exists_var {predicate : Value → Prop} :
    (∃ value, LogicalEval signature environment (.var name) value ∧ predicate value) ↔
      ∃ value, environment.lookup name = some value ∧ predicate value := by
  simp only [logical_var]

@[system_frk_bridge ↓] theorem logical_exists_int {predicate : Value → Prop} :
    (∃ value, LogicalEval signature environment (.int integer) value ∧ predicate value) ↔
      predicate (.int integer) := by
  simp only [logical_int, exists_eq_left]

@[system_frk_bridge ↓] theorem logical_exists_bool {predicate : Value → Prop} :
    (∃ value, LogicalEval signature environment (.bool boolean) value ∧ predicate value) ↔
      predicate (.bool boolean) := by
  simp only [logical_bool, exists_eq_left]

@[system_frk_bridge ↓] theorem logical_exists_add {predicate : Value → Prop} :
    (∃ value, LogicalEval signature environment (.add left right) value ∧ predicate value) ↔
      ∃ m n, LogicalEval signature environment left (.int m) ∧
        LogicalEval signature environment right (.int n) ∧ predicate (.int (m + n)) := by
  constructor
  · rintro ⟨_, evaluation, holds⟩
    cases evaluation with | add left right => exact ⟨_, _, left, right, holds⟩
  · rintro ⟨_, _, left, right, holds⟩; exact ⟨_, .add left right, holds⟩

@[system_frk_bridge ↓] theorem logical_exists_ctor {predicate : Value → Prop} :
    (∃ value, LogicalEval signature environment (.ctor name fields) value ∧ predicate value) ↔
      ∃ values, LogicalListEval signature environment fields values ∧ predicate (.ctor name values) := by
  constructor
  · rintro ⟨_, evaluation, holds⟩
    cases evaluation with | ctor fields => exact ⟨_, fields, holds⟩
  · rintro ⟨_, fields, holds⟩; exact ⟨_, .ctor fields, holds⟩

@[system_frk_bridge ↓] theorem logical_exists_measure {predicate : Value → Prop} :
    (∃ value, LogicalEval signature environment (.measure name term) value ∧ predicate value) ↔
      ∃ argument, LogicalEval signature environment term argument ∧
        ∃ result, MeasureEval signature name argument result ∧ predicate (.int result) := by
  constructor
  · rintro ⟨_, evaluation, holds⟩
    cases evaluation with | measure term measure => exact ⟨_, term, _, measure, holds⟩
  · rintro ⟨_, term, _, measure, holds⟩; exact ⟨_, .measure term measure, holds⟩

@[system_frk_bridge ↓] theorem logical_list_exists_nil {predicate : List Value → Prop} :
    (∃ values, LogicalListEval signature environment [] values ∧ predicate values) ↔
      predicate [] := by
  simp only [logical_list_nil, exists_eq_left]

@[system_frk_bridge ↓] theorem logical_list_exists_cons {predicate : List Value → Prop} :
    (∃ values, LogicalListEval signature environment (term :: terms) values ∧ predicate values) ↔
      ∃ value, LogicalEval signature environment term value ∧
        ∃ values, LogicalListEval signature environment terms values ∧ predicate (value :: values) := by
  constructor
  · rintro ⟨_, evaluation, holds⟩
    cases evaluation with | cons head tail => exact ⟨_, head, _, tail, holds⟩
  · rintro ⟨_, head, _, tail, holds⟩; exact ⟨_, .cons head tail, holds⟩

/-- Opt-in measure inversion using the selected declaration equation. -/
theorem measure_ctor :
    MeasureEval signature name (.ctor ctor fields) result ↔
      ∃ declaration branch,
        signature.findMeasure name = some declaration ∧
        declaration.cases.find? (fun c => c.ctor == ctor) = some branch ∧
        MeasureBodyEval signature name fields branch.body result := by
  constructor
  · intro evaluation; cases evaluation with
    | constructor declared selected body => exact ⟨_, _, declared, selected, body⟩
  · rintro ⟨_, _, declared, selected, body⟩; exact .constructor declared selected body

@[system_frk_bridge] theorem atom_theory :
    Atom.denote signature assignment environment (.theory formula) ↔
      formula.denote signature environment := Iff.rfl

@[system_frk_bridge] theorem atom_kvar :
    Atom.denote signature assignment environment (.kvar name arguments) ↔
      ∃ values, LogicalListEval signature environment arguments values ∧
        assignment name values := Iff.rfl

@[system_frk_bridge] theorem cstr_truth :
    Cstr.denote signature assignment environment .truth ↔ True := Iff.rfl

@[system_frk_bridge] theorem cstr_head :
    Cstr.denote signature assignment environment (.head atom) ↔
      atom.denote signature assignment environment := Iff.rfl

@[system_frk_bridge] theorem cstr_guard :
    Cstr.denote signature assignment environment (.guard antecedent consequent) ↔
      (antecedent.denote signature assignment environment →
        consequent.denote signature assignment environment) := Iff.rfl

@[system_frk_bridge] theorem cstr_conj :
    Cstr.denote signature assignment environment (.conj left right) ↔
      (left.denote signature assignment environment ∧
        right.denote signature assignment environment) := Iff.rfl

@[system_frk_bridge] theorem cstr_all_value :
    Cstr.denote signature assignment environment (.all name .value body) ↔
      ∀ value, body.denote signature assignment (environment.bind name value) := by
  simp [Cstr.denote, LSort.contains]

@[system_frk_bridge] theorem cstr_all_int :
    Cstr.denote signature assignment environment (.all name .int body) ↔
      ∀ integer, body.denote signature assignment (environment.bind name (.int integer)) := by
  simp [Cstr.denote, LSort.contains]

@[system_frk_bridge] theorem cstr_all_bool :
    Cstr.denote signature assignment environment (.all name .bool body) ↔
      ∀ boolean, body.denote signature assignment (environment.bind name (.bool boolean)) := by
  simp [Cstr.denote, LSort.contains]

attribute [system_frk_bridge] Formula.denote
  MeasureBodyEval.literal_iff MeasureBodyEval.field_iff
  MeasureBodyEval.recur_iff MeasureBodyEval.add_iff

end SystemFRK.Bridge
