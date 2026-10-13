import Flex.VCG.SystemFRK.Model

/-! Evaluation determinism and inversion; no typing or termination premise. -/

namespace SystemFRK

theorem MeasureEval.deterministic
    (first : MeasureEval signature name value result)
    (second : MeasureEval signature name value other) : result = other := by
  induction first using MeasureEval.rec
      (motive_2 := fun fields body result _ =>
        ∀ other, MeasureBodyEval signature name fields body other → result = other)
      generalizing other with
  | constructor declarationLookup branchLookup body ih =>
    cases second with
    | constructor otherDeclarationLookup otherBranchLookup otherBody =>
      cases Option.some.inj (declarationLookup.symm.trans otherDeclarationLookup)
      cases Option.some.inj (branchLookup.symm.trans otherBranchLookup)
      exact ih _ otherBody
  | literal => rename_i other second; cases second; rfl
  | field lookup =>
    rename_i other second
    cases second with
    | field otherLookup =>
      exact Value.int.inj (Option.some.inj (lookup.symm.trans otherLookup))
  | recur lookup measure ih =>
    rename_i other second
    cases second with
    | recur otherLookup otherMeasure =>
      cases Option.some.inj (lookup.symm.trans otherLookup)
      exact ih otherMeasure
  | add left right ihLeft ihRight =>
    rename_i other second
    cases second with
    | add otherLeft otherRight => rw [ihLeft _ otherLeft, ihRight _ otherRight]

theorem MeasureBodyEval.deterministic
    (first : MeasureBodyEval signature name fields body result)
    (second : MeasureBodyEval signature name fields body other) : result = other := by
  induction body generalizing result other with
  | literal n => cases first; cases second; rfl
  | field index =>
    cases first with
    | field lookup =>
      cases second with
      | field otherLookup =>
        exact Value.int.inj (Option.some.inj (lookup.symm.trans otherLookup))
  | recur index =>
    cases first with
    | recur lookup measure =>
      cases second with
      | recur otherLookup otherMeasure =>
        cases Option.some.inj (lookup.symm.trans otherLookup)
        exact MeasureEval.deterministic measure otherMeasure
  | add left right ihLeft ihRight =>
    cases first with
    | add firstLeft firstRight =>
      cases second with
      | add otherLeft otherRight =>
        rw [ihLeft firstLeft otherLeft, ihRight firstRight otherRight]

/-- Simultaneous determinism of evaluation and closure application. -/
theorem Eval.deterministic
    (first : Eval signature environment frame expression result)
    (second : Eval signature environment frame expression other) : result = other := by
  refine Eval.rec
    (motive_1 := fun environment frame expression result _ =>
      ∀ other, Eval signature environment frame expression other → result = other)
    (motive_2 := fun function argument result _ =>
      ∀ other, Apply signature function argument other → result = other)
    (motive_3 := fun function result _ =>
      ∀ other, TypeApply signature function other → result = other)
    (motive_4 := fun environment frame expressions results _ =>
      ∀ others, EvalList signature environment frame expressions others → results = others)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ first other second
  · intro environment frame name value lookup other second
    cases second with
    | var otherLookup => exact Option.some.inj (lookup.symm.trans otherLookup)
  · intro environment frame n other second
    cases second; rfl
  · intro environment frame b other second
    cases second; rfl
  · intro environment frame name domain body other second
    cases second; rfl
  · intro environment frame body other second
    cases second; rfl
  · intro environment frame name domain codomain body other second
    cases second; rfl
  · intro environment frame fn arg function argument result fnEval argEval app ihFn ihArg ihApp
    intro other second
    cases second with
    | app otherFn otherArg otherApp =>
      cases ihFn _ otherFn
      cases ihArg _ otherArg
      exact ihApp _ otherApp
  · intro environment frame fn argument function result fnEval app ihFn ihApp other second
    cases second with
    | tyApp otherFn otherApp =>
      cases ihFn _ otherFn
      exact ihApp _ otherApp
  · intro environment frame name rhs body value result rhsEval bodyEval ihRhs ihBody other second
    cases second with
    | letE otherRhs otherBody =>
      cases ihRhs _ otherRhs
      exact ihBody _ otherBody
  · intro environment frame name arguments fields values fieldsEval ihFields other second
    cases second with
    | ctor otherFields => exact congrArg _ (ihFields _ otherFields)
  · intro environment frame scrutinee branches name fields names body result
    intro scrutineeEval branchLookup length bodyEval ihScrutinee ihBody other second
    cases second with
    | matchE otherScrutinee otherBranchLookup otherLength otherBody =>
      cases ihScrutinee _ otherScrutinee
      cases Option.some.inj (branchLookup.symm.trans otherBranchLookup)
      exact ihBody _ otherBody
  · intro environment frame argument value function result frameLookup argumentEval app
    intro ihArgument ihApp other second
    cases second with
    | recur otherFrameLookup otherArgument otherApp =>
      cases Option.some.inj (frameLookup.symm.trans otherFrameLookup)
      cases ihArgument _ otherArgument
      exact ihApp _ otherApp
  · intro environment frame name argument value result argumentEval measure ihArgument other second
    cases second with
    | measure otherArgument otherMeasure =>
      cases ihArgument _ otherArgument
      exact congrArg Value.int (measure.deterministic otherMeasure)
  · intro environment frame expression type result expressionEval ih other second
    cases second with | ann otherExpression => exact ih _ otherExpression
  · intro name body environment frame argument result bodyEval ih other second
    cases second with | closure otherBody => exact ih _ otherBody
  · intro name body environment argument result bodyEval ih other second
    cases second with | recursiveClosure otherBody => exact ih _ otherBody
  · intro body environment frame result bodyEval ih other second
    cases second with | closure otherBody => exact ih _ otherBody
  · intro environment frame other second
    cases second; rfl
  · intro environment frame expression expressions value values head tail ihHead ihTail other second
    cases second with
    | cons otherHead otherTail =>
      cases ihHead _ otherHead
      cases ihTail _ otherTail
      rfl

theorem Apply.deterministic
    (first : Apply signature function argument result)
    (second : Apply signature function argument other) : result = other := by
  cases first with
  | closure body => cases second with | closure otherBody => exact body.deterministic otherBody
  | recursiveClosure body =>
    cases second with | recursiveClosure otherBody => exact body.deterministic otherBody

theorem TypeApply.deterministic
    (first : TypeApply signature function result)
    (second : TypeApply signature function other) : result = other := by
  cases first with
  | closure body => cases second with | closure otherBody => exact body.deterministic otherBody

theorem EvalList.deterministic
    (first : EvalList signature environment frame expressions results)
    (second : EvalList signature environment frame expressions others) : results = others := by
  induction expressions generalizing results others with
  | nil => cases first; cases second; rfl
  | cons expression expressions ih =>
    cases first with
    | cons head tail =>
      cases second with
      | cons otherHead otherTail =>
        cases head.deterministic otherHead
        cases ih tail otherTail
        rfl

theorem LogicalEval.deterministic
    (first : LogicalEval signature environment term value)
    (second : LogicalEval signature environment term other) : value = other := by
  induction first using LogicalEval.rec
      (motive_2 := fun terms values _ =>
        ∀ others, LogicalListEval signature environment terms others → values = others)
      generalizing other with
  | var lookup =>
    cases second with
    | var otherLookup => exact Option.some.inj (lookup.symm.trans otherLookup)
  | int => cases second; rfl
  | bool => cases second; rfl
  | add left right ihLeft ihRight =>
    cases second with
    | add otherLeft otherRight =>
      cases ihLeft otherLeft
      cases ihRight otherRight
      rfl
  | ctor fields ih =>
    cases second with | ctor otherFields => exact congrArg _ (ih _ otherFields)
  | measure argument measure ih =>
    cases second with
    | measure otherArgument otherMeasure =>
      cases ih otherArgument
      exact congrArg Value.int (measure.deterministic otherMeasure)
  | nil => rename_i other second; cases second; rfl
  | cons head tail ihHead ihTail =>
    rename_i other second
    cases second with
    | cons otherHead otherTail =>
      cases ihHead otherHead
      cases ihTail _ otherTail
      rfl

theorem LogicalListEval.deterministic
    (first : LogicalListEval signature environment terms values)
    (second : LogicalListEval signature environment terms others) : values = others := by
  induction terms generalizing values others with
  | nil => cases first; cases second; rfl
  | cons term terms ih =>
    cases first with
    | cons head tail =>
      cases second with
      | cons otherHead otherTail =>
        cases head.deterministic otherHead
        cases ih tail otherTail
        rfl

@[simp] theorem Apply.closure_iff :
    Apply signature (.closure name body environment frame) argument result ↔
      Eval signature (Environment.bind environment name argument) frame body result := by
  constructor
  · intro evaluation
    cases evaluation with | closure body => exact body
  · exact Apply.closure

@[simp] theorem Apply.recursiveClosure_iff :
    Apply signature (.recursiveClosure name body environment) argument result ↔
      Eval signature (Environment.bind environment name argument)
        (some (.recursiveClosure name body environment)) body result := by
  constructor
  · intro evaluation
    cases evaluation with | recursiveClosure body => exact body
  · exact Apply.recursiveClosure

@[simp] theorem TypeApply.closure_iff :
    TypeApply signature (.typeClosure body environment frame) result ↔
      Eval signature environment frame body result := by
  constructor
  · intro evaluation
    cases evaluation with | closure body => exact body
  · exact TypeApply.closure

@[simp] theorem Eval.var_iff :
    Eval signature environment frame (.var name) value ↔
      environment.lookup name = some value := by
  constructor
  · intro evaluation
    cases evaluation with | var lookup => exact lookup
  · exact Eval.var

@[simp] theorem Eval.int_iff :
    Eval signature environment frame (.int n) value ↔ value = .int n := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · intro equality; cases equality; exact Eval.int

@[simp] theorem Eval.bool_iff :
    Eval signature environment frame (.bool b) value ↔ value = .bool b := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · intro equality; cases equality; exact Eval.bool

@[simp] theorem Eval.lam_iff :
    Eval signature environment frame (.lam name domain body) value ↔
      value = .closure name body environment frame := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · intro equality; cases equality; exact Eval.lam

@[simp] theorem Eval.tyLam_iff :
    Eval signature environment frame (.tyLam body) value ↔
      value = .typeClosure body environment frame := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · intro equality; cases equality; exact Eval.tyLam

@[simp] theorem Eval.structRec_iff :
    Eval signature environment frame (.structRec name domain codomain body) value ↔
      value = .recursiveClosure name body environment := by
  constructor
  · intro evaluation; cases evaluation; rfl
  · intro equality; cases equality; exact Eval.structRec

@[simp] theorem Eval.ann_iff :
    Eval signature environment frame (.ann expression type) value ↔
      Eval signature environment frame expression value := by
  constructor
  · intro evaluation
    cases evaluation with | ann expression => exact expression
  · exact Eval.ann

theorem Eval.recur_iff :
    Eval signature environment frame (.recur argument) result ↔
      ∃ function value, frame = some function ∧
        Eval signature environment frame argument value ∧
        Apply signature function value result := by
  constructor
  · intro evaluation
    cases evaluation with | recur lookup argument apply => exact ⟨_, _, lookup, argument, apply⟩
  · rintro ⟨_, _, lookup, argument, apply⟩
    exact Eval.recur lookup argument apply

end SystemFRK
