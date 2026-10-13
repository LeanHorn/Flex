import Flex.VCG.LambdaRK.SemanticsLemmas

/-! Logical substitution and environment agreement, proved independently of
all draft binding and semantic type substitution obligations. -/

namespace LambdaRK

private theorem LogicalEval.transport
    (evaluation : LogicalEval signature left term value)
    (agree : ∀ name ∈ term.freeVars, left.lookup name = right.lookup name) :
    LogicalEval signature right term value := by
  induction evaluation using LogicalEval.rec
      (motive_2 := fun terms values _ =>
        (∀ name ∈ terms.flatMap LTerm.freeVars, left.lookup name = right.lookup name) →
          LogicalListEval signature right terms values) with
  | var lookup =>
    apply LogicalEval.var
    rw [← agree _ (by simp [LTerm.freeVars])]
    exact lookup
  | int => exact LogicalEval.int
  | bool => exact LogicalEval.bool
  | add left right ihLeft ihRight =>
    exact LogicalEval.add
      (ihLeft (fun name mem => agree name (by simp [LTerm.freeVars, mem])))
      (ihRight (fun name mem => agree name (by simp [LTerm.freeVars, mem])))
  | ctor fields ih => exact LogicalEval.ctor (ih (by simpa only [LTerm.freeVars] using agree))
  | measure argument measure ih => exact LogicalEval.measure (ih (by simpa only [LTerm.freeVars] using agree)) measure
  | nil => exact LogicalListEval.nil
  | cons head tail ihHead ihTail =>
    rename_i agree
    exact LogicalListEval.cons
      (ihHead (fun name mem => agree name (by simp [mem])))
      (ihTail (fun name mem => agree name (by simp [mem])))

theorem LogicalEval.environment_congr
    (signature : Signature) (left right : Environment) (term : LTerm) (value : Value)
    (agree : ∀ name ∈ term.freeVars, left.lookup name = right.lookup name) :
    LogicalEval signature left term value ↔ LogicalEval signature right term value := by
  constructor
  · intro evaluation; exact evaluation.transport agree
  · intro evaluation; exact evaluation.transport (fun name mem => (agree name mem).symm)

@[simp] theorem LogicalEval.var_iff :
    LogicalEval signature environment (.var name) value ↔
      environment.lookup name = some value := by
  constructor
  · intro evaluation; cases evaluation with | var lookup => exact lookup
  · exact LogicalEval.var

theorem LogicalEval.substitution
    (signature : Signature) (environment : Environment)
    (name : String) (replacement term : LTerm) (replacementValue value : Value)
    (evaluates : LogicalEval signature environment replacement replacementValue) :
    LogicalEval signature environment (term.substTerm name replacement) value ↔
      LogicalEval signature (Environment.bind environment name replacementValue) term value := by
  induction term using LTerm.rec
      (motive_2 := fun terms => ∀ values,
        LogicalListEval signature environment (terms.map (·.substTerm name replacement)) values ↔
          LogicalListEval signature (environment.bind name replacementValue) terms values)
      generalizing value with
  | var x =>
    by_cases same : x = name
    · subst x
      simp only [LTerm.substTerm, beq_self_eq_true, ite_true, LogicalEval.var_iff,
        Environment.bind, List.lookup_cons, beq_self_eq_true]
      constructor
      · intro evaluation; exact congrArg some (evaluates.deterministic evaluation)
      · intro equality; cases Option.some.inj equality; exact evaluates
    · have different : (x == name) = false := by simpa using same
      simp [LTerm.substTerm, different, LogicalEval.var_iff, Environment.bind, List.lookup_cons]
  | int n =>
    simp only [LTerm.substTerm]
    constructor <;> intro evaluation <;> cases evaluation <;> exact LogicalEval.int
  | bool b =>
    simp only [LTerm.substTerm]
    constructor <;> intro evaluation <;> cases evaluation <;> exact LogicalEval.bool
  | add left right ihLeft ihRight =>
    simp only [LTerm.substTerm]
    constructor
    · intro evaluation
      cases evaluation with
      | add left right => exact LogicalEval.add ((ihLeft _).mp left) ((ihRight _).mp right)
    · intro evaluation
      cases evaluation with
      | add left right => exact LogicalEval.add ((ihLeft _).mpr left) ((ihRight _).mpr right)
  | ctor name fields ih =>
    simp only [LTerm.substTerm]
    constructor
    · intro evaluation
      cases evaluation with | ctor fields => exact LogicalEval.ctor ((ih _).mp fields)
    · intro evaluation
      cases evaluation with | ctor fields => exact LogicalEval.ctor ((ih _).mpr fields)
  | measure name argument ih =>
    simp only [LTerm.substTerm]
    constructor
    · intro evaluation
      cases evaluation with
      | measure argument measure => exact LogicalEval.measure ((ih _).mp argument) measure
    · intro evaluation
      cases evaluation with
      | measure argument measure => exact LogicalEval.measure ((ih _).mpr argument) measure
  | nil =>
    rename_i values
    constructor <;> intro evaluation <;> cases evaluation <;> exact LogicalListEval.nil
  | cons term terms ihHead ihTail =>
    rename_i values
    constructor
    · intro evaluation
      cases evaluation with
      | cons head tail => exact LogicalListEval.cons ((ihHead _).mp head) ((ihTail _).mp tail)
    · intro evaluation
      cases evaluation with
      | cons head tail => exact LogicalListEval.cons ((ihHead _).mpr head) ((ihTail _).mpr tail)

end LambdaRK
