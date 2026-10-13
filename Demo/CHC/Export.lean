import Flex.CHC
import Smt2Lean.Translate

/-! Regression checks for the CHC exporter. Native parsing and reconstruction are
in-process; these tests need neither Spacer nor Eldarica installed. -/
namespace CHCExportDemo

open Lean Meta Qq Flex.CHC

-- Several fixtures deliberately retain unused and shadowed source names.
set_option linter.unusedVariables false

private def check (condition : Bool) (message : String) : MetaM Unit :=
  unless condition do throwError message

private def exportFormula (formula : Expr) : MetaM ExportedProblem := do
  let goal ← mkFreshExprMVar formula
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
  let body ← bodyGoal.getType
  let before ← getEnv
  let handlers := (Smt.Attribute.smtExt.getState before).getD ``Smt.Translator {}
  let result ← exportConstraints kvars body
  let again ← exportConstraints kvars body
  check (result.toSMTLib == again.toSMTLib) "export is not deterministic"
  check (!(← bodyGoal.isAssigned)) "export assigned the constraint goal"
  for kvar in kvars do
    check (!(← kvar.mvarId.isAssigned)) "export assigned a witness"
  let after := (Smt.Attribute.smtExt.getState (← getEnv)).getD ``Smt.Translator {}
  check (after.size == handlers.size && after.toList.all handlers.contains)
    "export leaked translator registrations"
  check (result.relations.map (·.kvar.mvarId) == kvars.toArray.map (·.mvarId))
    "relation mapping changed witness order"
  return result

/-- Check meaning through the independent SMT-to-Lean path after export locals
are gone. Expected expressions bind predicates in their declaration order. -/
private def roundTrip (problem : ExportedProblem) (expected : Expr) : MetaM Unit := do
  let env ← getEnv
  let output ← IO.mkRef (none : Option Expr)
  (Smt2Lean.Backend.parseAndInspectQuery problem.toSMTLib (mode := .chc) fun query => do
    let action : MetaM Expr := Smt2Lean.Translate.withAssertions query fun predicates assertions => do
      let mut body := assertions.back?.getD (mkConst ``True)
      for assertion in assertions.pop.reverse do body ← mkAppM ``And #[assertion, body]
      mkLambdaFVars predicates body (usedOnly := false)
    let (value, _, _) ← action.toIO { fileName := "chc-round-trip", fileMap := default } { env }
    output.set (some value)
  ).runIO
  let some actual ← output.get | throwError "round trip returned no expression"
  let proof ← Smt2Lean.Equivalence.prove actual expected (fun _ => false)
  checkWithKernel proof

private def rejects (formula : Expr) (fragment : String) : MetaM Unit := do
  let goal ← mkFreshExprMVar formula
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
  let before := (Smt.Attribute.smtExt.getState (← getEnv)).getD ``Smt.Translator {}
  let error? ← try
    discard <| exportConstraints kvars (← bodyGoal.getType)
    pure none
  catch error => pure (some error)
  let some error := error? | throwError "export accepted unsupported input: {formula}"
  let text ← error.toMessageData.toString
  check (text.contains fragment) s!"expected '{fragment}', got: {text}"
  check (!(← bodyGoal.isAssigned)) "failed export assigned the goal"
  for kvar in kvars do check (!(← kvar.mvarId.isAssigned)) "failed export assigned a witness"
  let after := (Smt.Attribute.smtExt.getState (← getEnv)).getD ``Smt.Translator {}
  check (after.size == before.size && after.toList.all before.contains)
    "failed export changed translator registrations"

run_elab do
  let problem ← exportFormula q(∃ k : Int → Prop,
    k 0 ∧ (∀ x, k x → k (x + 1)) ∧ (∀ x, k x → 0 ≤ x))
  check (problem.clauseCount == 3 && problem.relations.size == 1) "wrong counter shape"
  check (problem.toSMTLib.contains "(declare-fun k_0 (Int) Bool)") "missing relation declaration"
  check (!problem.toSMTLib.contains "Int.NonNeg") "arithmetic was exported as an unknown relation"
  roundTrip problem q(fun k : Int → Prop =>
    k 0 ∧ (∀ x, k x → k (x + 1)) ∧ (∀ x, k x → 0 ≤ x))

-- Repeated source names, mixed argument sorts, unused predicates/arguments,
-- nullary predicates, and names that are not usable as SMT identifiers.
run_elab do
  let problem ← exportFormula q(∃ «k | strange» : Int → Prop → Prop,
    ∃ «k | strange» : Int → Prop, ∃ flag : Prop,
      (∀ x : Int, ∀ p : Prop, «k | strange» x) ∧ flag)
  check (problem.relations.map (·.symbol) == #["k_0", "k_1", "k_2"]) "unstable generated names"
  check (problem.relations[0]!.argumentSorts == #[.int, .bool]) "lost argument order"
  check (problem.toSMTLib.contains "(declare-fun k_0 (Int Bool) Bool)") "unused predicate was omitted"
  check (problem.toSMTLib.contains "(declare-const k_2 Bool)") "nullary predicate was omitted"
  roundTrip problem q(fun (_unused : Int → Prop → Prop) (k : Int → Prop) (flag : Prop) =>
    (∀ x : Int, k x) ∧ flag)

-- Move a universal past an earlier guard without capturing its variable, and
-- split conjunctions below binders/guards using Flex's existing flattening.
run_elab do
  let problem ← exportFormula q(∃ k : Int → Int → Prop,
    ∀ v_0 : Int, v_0 ≥ 0 → ∀ v_0 : Int,
      k 0 v_0 ∧ (k 0 v_0 → 0 ≤ v_0))
  roundTrip problem q(fun k : Int → Int → Prop =>
    (∀ x y : Int, x ≥ 0 → k 0 y) ∧
    (∀ x y : Int, x ≥ 0 → k 0 y → 0 ≤ y))
  let problem ← exportFormula q(∃ k : Int → Prop,
    ∀ unused : Int, ∀ flag : Prop, k 0)
  roundTrip problem q(fun k : Int → Prop => k 0)

-- Simultaneous scoping of lets, negative literal coefficients, and ite.
run_elab do
  let problem ← exportFormula q(∃ k : Int → Prop,
    ∀ x : Int, let y := x + 1; x ≥ 0 → k (2 * y + (-3) * x))
  roundTrip problem q(fun k : Int → Prop => ∀ x : Int, x ≥ 0 → k (2 * (x + 1) + (-3) * x))
  let problem ← exportFormula q(∃ k : Int → Prop,
    ∀ x : Int, k (if x ≥ 0 then x else -x))
  roundTrip problem q(fun k : Int → Prop => ∀ x : Int, k (if x ≥ 0 then x else -x))
  let problem ← exportFormula q(∃ k : Bool → Int → Prop, ∀ b : Bool, k b 0)
  check (problem.relations[0]!.argumentSorts == #[.bool, .int]) "Bool signature changed"
  check (← isDefEq problem.relations[0]!.leanType q(Bool → Int → Prop)) "lost Lean Bool type"
  -- SMT Bool reconstructs as Prop; keep the original Lean type in the map for
  -- the later witness importer to adapt this domain explicitly.
  roundTrip problem q(fun k : Prop → Int → Prop => ∀ b : Prop, k b 0)
  let problem ← exportFormula q(∃ k : Bool → Prop, ∀ b : Bool, k (Bool.not b))
  roundTrip problem q(fun k : Prop → Prop => ∀ b : Prop, k (¬b))
  let problem ← exportFormula q(∃ k : Prop → Prop, ∀ p : Prop, p → k p)
  roundTrip problem q(fun k : Prop → Prop => ∀ p : Prop, p → k p)

-- Spacer rejects nested Bool/Int universals during Horn preprocessing. Keep a
-- single binder list, preserving the mixed argument order and clause meaning.
run_elab do
  let problem ← exportFormula q(∃ k : Bool → Int → Prop,
    (∀ b : Bool, k b 0) ∧
    (∀ b x, k b x → k (Bool.not b) (x + 1)) ∧
    (∀ b x, k b x → x ≥ 0))
  check (problem.toSMTLib.contains "(forall ((v_0 Bool) (v_1 Int))")
    "mixed universal binders were not grouped"
  roundTrip problem q(fun k : Prop → Int → Prop =>
    (∀ b : Prop, k b 0) ∧
    (∀ b x, k b x → k (¬b) (x + 1)) ∧
    (∀ b x, k b x → x ≥ 0))

-- Pure safety constraints and empty systems also use the shared interface.
run_elab do
  let problem ← exportFormula q(True)
  check (problem.relations.isEmpty && problem.clauseCount == 0) "empty system was changed"
  roundTrip problem q(True)
  let problem ← exportFormula q(False)
  roundTrip problem q(False)
  let problem ← exportFormula q(∀ x : Int, x < 0 → x < 1)
  roundTrip problem q(∀ x : Int, x < 0 → x < 1)

opaque external : Int → Int := fun x => x + 2

-- Export must not pick up an arbitrary registered extension, even one capable
-- of translating an otherwise unsupported function.
@[smt_translate] def customTranslator : Smt.Translator := fun expression => do
  if expression.isAppOfArity ``external 1 then return some (.literalT "0")
  return none

run_elab do
  rejects q(∃ k : Nat → Prop, ∀ x, k x) "unsupported value type"
  rejects q(∃ k : (Int → Int) → Prop, ∀ f, k f) "unsupported value type"
  rejects q(∃ k : Int → Int, ∀ x, k x = x) "must return Prop"
  rejects q(∃ k : Int → Prop, ∀ n : Nat, k (Int.ofNat n)) "unsupported value type"
  rejects q(∃ k : Int → Prop, ∀ x y : Int, k (x * y)) "nonlinear multiplication"
  rejects q(∃ k : Int → Prop, ∀ x : Int, k (x / 0)) "unsupported SMT operator 'div'"
  rejects q(∃ k : Int → Prop, ∀ x : Int, k (x % 2)) "unsupported SMT operator 'mod'"
  rejects q(∃ k : Int → Prop, ∀ x : Int, k (external x)) "unsupported constant dependencies"
  rejects q(∃ k : Int → Prop, ∀ x : Int, k x ∨ k (x + 1)) "multiple positive relations"
  rejects q(∃ k : Int → Prop, ∀ x : Int, ¬k x → k (x + 1)) "relation inside"
  rejects q(∃ k : Int → Prop, ∀ _x : Int, ∃ y : Int, k y) "unsupported"
  rejects q(∃ k : Int → Prop, (∀ x : Int, x = x) → k 0) "quantifiers must be clause binders"
  rejects q(∃ k : Int → Prop, ∀ h : True, h = h) "depending on proof terms"
  rejects q(∃ k : Bool → Prop, ∀ x y : Int, k (x == y)) "BEq comparisons"
  withLocalDeclD `ambient q(Int) fun ambient => do
    let ambient : Q(Int) := ambient
    rejects q(∃ k : Int → Prop, k $ambient) "free local variables"
  let unknown ← mkFreshExprMVar q(Int)
  let unknown : Q(Int) := unknown
  rejects q(∃ k : Int → Prop, k $unknown) "unregistered or unresolved metavariable"

-- Explicit identity/signature checks protect the model-to-witness map.
run_elab do
  let goal ← mkFreshExprMVar q(∃ k : Int → Prop, k 0)
  let (_, [kvar], bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
    | throwError "expected one predicate"
  let body ← bodyGoal.getType
  for kvars in [[kvar, kvar], [{ kvar with paramTypes := [q(Bool)] }]] do
    let failed ← try discard <| exportConstraints kvars body; pure false catch _ => pure true
    check failed "accepted inconsistent predicate metadata"
  check (!(← kvar.mvarId.isAssigned)) "metadata rejection assigned a witness"
  discard <| exportConstraints [kvar] body
  kvar.mvarId.assign q(fun (_ : Int) => True)
  let failed ← try discard <| exportConstraints [kvar] body; pure false catch _ => pure true
  check failed "accepted an already assigned predicate"

-- A global nonstandard arithmetic instance must not be erased by translation.
@[instance_reducible] def unusualAdd : HAdd Int Int Int := ⟨fun a b => a - b⟩

run_elab do
  let formula := q(∃ k : Int → Prop, ∀ x : Int, k (@HAdd.hAdd Int Int Int unusualAdd x 1))
  rejects formula "nonstandard operator instance"
  -- Recovery after failures: the ordinary exporter remains usable.
  discard <| exportFormula q(∃ k : Int → Prop, k 0)

end CHCExportDemo
