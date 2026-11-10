import Flex.CHC.Goal
import Flex.Preprocess.Witnesses
import Std.Tactic.BVDecide

/-! Small checks for model import and certification; solver coverage lives in the benchmarks. -/

open Lean Meta Elab Term Flex.CHC

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let result ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars result

private def response (model : String) : SolverResult :=
  SolverResult.ofProcess { completion := .exited 0, stdout := "sat\n" ++ model }

-- Unsupported semantics fail before invoking a solver and preserve the goal.
run_elab do
  for (input, stage) in #[
      (← `(∃ k : String → Prop, k ""), Stage.prepare),
      (← `(∃ k : Fin 3 → Prop, k 0), Stage.prepare),
      (← `(∃ k : Int → Prop, k 0 ∧ (∀ x, k x → toString x = "0")), Stage.exporting)] do
    let goal ← mkFreshExprMVar (← elaborate input)
    let result ← solveGoal goal.mvarId! { executable := some "/__flex_export_rejection_no_solver__" }
    let .failed failure := result | throwError "unsupported CHC was accepted"
    unless failure.stage == stage && failure.solver.isNone do
      throwError "unsupported CHC reached the solver: {failure.message}"
    if ← goal.mvarId!.isAssignedOrDelayedAssigned then
      throwError "failed export changed the goal"

-- A κ-free safety clause must reach the solver too.
run_elab do
  let goal ← mkFreshExprMVar (← elaborate (← `(∃ k : Int → Prop,
    k 0 ∧ (∀ x, k x → k (x + 1)) ∧ False)))
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  unless problem.clauseCount == 3 && problem.clauses.any (·.head == "false") do
    throwError "export omitted the κ-free safety clause"

-- The normalization bridge must prove the original existential/disjunctive guard.
run_elab do
  let target ← elaborate (← `(∃ k : Int → Prop,
    k 0 ∧ (∀ x : Int, (∃ y : Int, (k y ∨ y = 0) ∧ y = x) → k x) ∧
    (∀ x : Int, k x → 0 ≤ x)))
  let goal ← mkFreshExprMVar target
  let cleaned ← Flex.Preprocess.compactGoal goal.mvarId! []
  let expected ← elaborate (← `(∃ k : Int → Prop,
    k 0 ∧ (∀ x : Int, (k x ∨ x = 0) → k x) ∧ (∀ x : Int, k x → 0 ≤ x)))
  unless ← isDefEq (← cleaned.getType) expected do
    throwError "witness compaction did not remove the equality-bound witness"
  let prepared ← prepareGoal cleaned
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let witnesses ← importWitnesses problem
    (response "(model (define-fun k_0 ((x Int)) Bool (<= 0 x)))")
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun target => do proveLeafWith (← `(tactic| omega)) target)
  unless certificate.goals.isEmpty do throwError "normalized clauses were not certified"
  let proof ← instantiateMVars goal
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do throwError "normalization changed the goal"

-- Import an invariant, remove its heads, and finish the original goal from the residual.
run_elab do
  let target ← elaborate
    (← `(∃ unused : Prop, ∃ k : Int → Prop,
      k 0 ∧ (∀ x : Int, (k x ∨ x = 0) → k (x + 1)) ∧
      (∀ x : Int, k x → x + 1 > 0)))
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId! (headsOnly := true)
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  unless problem.clauseCount == 4 do throwError "guard normalization lost a branch"
  let witnesses ← importWitnesses problem
    (response "(model (define-fun k_1 ((x Int)) Bool (<= 0 x)))")
  unless witnesses.map (·.defaulted) == #[true, false] do
    throwError "unused predicate completion changed witness order"
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun target => do proveLeafWith (← `(tactic| omega)) target) (headsOnly := true)
  unless certificate.provedHeads == 2 && certificate.obligations.isEmpty do
    throwError "predicate heads were not removed cleanly"
  let some residual := certificate.residualVC | throwError "missing residual VC"
  residual.withContext do
    let expected ← elaborate (← `(∀ x : Int, 0 ≤ x → x + 1 > 0))
    unless ← isDefEq (← residual.getType) expected do
      throwError "unexpected residual VC: {← residual.getType}"
    let some proof ← proveLeafWith (← `(tactic| omega)) expected
      | throwError "could not finish residual VC"
    residual.assign proof
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "certificate contains unresolved or admitted evidence"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do
    throwError "certificate changed the original proposition"

-- Missing or ill-typed model definitions must not assign predicates or the body.
run_elab do
  let goal ← mkFreshExprMVar (← elaborate (← `(∃ k : Int → Prop, k 0)))
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  for model in #["(model)", "(model (define-fun k_0 ((x Bool)) Bool true))"] do
    let accepted ← try
      discard <| importWitnesses problem (response model)
      pure true
    catch _ => pure false
    if accepted then throwError "invalid model was accepted"
    for relation in problem.relations do
      if ← relation.kvar.mvarId.isAssignedOrDelayedAssigned then
        throwError "failed import assigned a predicate"
    if ← prepared.bodyGoal.isAssignedOrDelayedAssigned then
      throwError "failed import assigned the body"

-- A claimed proof of the wrong proposition must leave the false VC unproved.
run_elab do
  let goal ← mkFreshExprMVar (← elaborate (← `(∃ k : Prop, k ∧ (k → False))))
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let witnesses ← importWitnesses problem
    (response "(model (define-fun k_0 () Bool true))")
  let certificate ← certifyWitnesses problem witnesses prepared.bodyGoal
    (fun _ => pure (some (mkConst ``True.intro)))
  unless certificate.goals.size == 1 do throwError "invalid evidence closed the VC"
  let residual := certificate.goals[0]!
  residual.withContext do
    unless ← isDefEq (← residual.getType) (mkConst ``False) do
      throwError "invalid evidence changed the residual"
    if ← residual.isAssignedOrDelayedAssigned then
      throwError "invalid evidence proved False"

/-! Datatypes in clause variables go through the exact encoder (κ arguments stay scalar). -/

private structure Vec where
  len : Int
  ok : Bool

private inductive Gib where
  | a | b

private abbrev cap : Int := 8
private def lim : Int := 8
private def twice (v : Vec) : Int := 2 * v.len
private def pow2bv (x : BitVec 64) : Prop := BitVec.and x (BitVec.sub x (BitVec.ofInt 64 1)) = BitVec.ofInt 64 0

private def z3Available : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "z3", args := #["-version"] }
    return out.exitCode == 0
  catch _ => return false

/-- Solve with Spacer and require every remaining certificate goal to close by `grind`. -/
private def expectSolved (input : TSyntax `term) : TermElabM Unit := do
  let goal ← mkFreshExprMVar (← elaborate input)
  let result ← solveGoal goal.mvarId! { backend := .spacer, executable := some "z3", timeoutMs := 20000 }
    (headsOnly := true)
  let goals ← match result with
    | .solved _ => pure #[]
    | .partial report => pure report.certificate.goals
    | .failed failure => throwError "CHC failed at {repr failure.stage}: {failure.message}{indentD input}"
  for g in goals do
    let tac ← `(tactic| ((try simp only [lim, twice, pow2bv] at *) <;> first | grind | (intros; bv_decide)))
    -- Messages from failed closer attempts mention the goal's locals; drop them, and report
    -- a plain failure instead of a tactic error.
    let messages ← Core.getMessageLog
    let rest ← try Tactic.run g (Tactic.evalTactic tac) catch _ => pure [g]
    Core.setMessageLog messages
    unless rest.isEmpty do throwError "residual goal not closed{indentD input}"
  checkWithKernel (← instantiateMVars goal)

-- Export declares the datatypes and keeps relation arguments scalar.
run_elab do
  let goal ← mkFreshExprMVar (← elaborate (← `(∃ k : Int → Prop,
    (∀ x (g : Gib), g = .a → x = 1 → k x) ∧ (∀ x (v : Vec), k x → v.len = x → 0 < twice v))))
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let script := problem.toSMTLib
  unless (script.splitOn "declare-datatypes").length == 3 && (script.splitOn "define-fun").length == 2 do
    throwError "expected two datatypes and one definition:\n{script}"
  unless problem.usedRelations.contains "k_0" do throwError "relation use not recorded"

-- End to end: records through `if`, enum equalities, constants, `Option`/`Prod`, `Nat`.
run_elab do
  unless ← z3Available do return
  -- record binder, projection through `if`, reducible and non-reducible constants
  expectSolved (← `(∃ k : Int → Prop,
    (∀ x : Int, x < cap → 0 ≤ x → k x) ∧
    (∀ x (v : Vec), k x → v = (if 0 < x then ⟨x - 1, true⟩ else ⟨0, false⟩) → v.len < lim)))
  -- enum constructors in premises
  expectSolved (← `(∃ k : Int → Prop,
    (∀ x (g : Gib), g = .a → x = 1 → k x) ∧ (∀ x (g : Gib), g = .b → x = 2 → k x) ∧
    (∀ x, k x → 0 < x)))
  -- parametric datatypes and a definition over a record
  expectSolved (← `(∃ k : Int → Int → Prop,
    (∀ x (o : Option Int) (p : Int × Int), o = some x → p = (x, x + 1) → 0 ≤ x → k p.1 p.2) ∧
    (∀ a b (v : Vec), k a b → v = ⟨a, true⟩ → twice v < 2 * b)))
  -- Nat fields are nonnegative Ints
  expectSolved (← `(∃ k : Int → Prop,
    (∀ (n : Nat) (p : Nat × Bool), p = (n, true) → k p.1) ∧ (∀ x, k x → 0 ≤ x)))


/-- Like `expectSolved`, after introducing the outer `∀` parameters of the goal. -/
private def expectSolvedIntro (input : TSyntax `term) : TermElabM Unit := do
  let target ← elaborate input
  let goal ← mkFreshExprMVar target
  let (_, inner) ← goal.mvarId!.intros
  inner.withContext do
    let result ← solveGoal inner { backend := .spacer, executable := some "z3", timeoutMs := 20000 }
      (headsOnly := true)
    let goals ← match result with
      | .solved _ => pure #[]
      | .partial report => pure report.certificate.goals
      | .failed failure => throwError "CHC failed at {repr failure.stage}: {failure.message}{indentD input}"
    for g in goals do
      let rest ← Tactic.run g (Tactic.evalTactic (← `(tactic| grind)))
      unless rest.isEmpty do throwError "residual goal not closed{indentD input}"
  let proof ← instantiateMVars goal
  if proof.hasMVar || proof.hasFVar then throwError "open proof"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) target do throwError "proof changed the goal"

-- Outer Int/Prop parameters become leading relation arguments; κs may depend on them.
run_elab do
  unless ← z3Available do return
  expectSolvedIntro (← `(∀ (n : Int) (c : Prop), ∃ k : Int → Prop,
    (∀ x : Int, x = n → k x) ∧ (∀ x, k x → x < n + 1) ∧ (∀ x, k x → False → c)))
  expectSolvedIntro (← `(∀ (b : Bool) (m : Int), ∃ k : Int → Prop,
    (∀ x : Int, (b = true → x = m) → (b = false → x = 0) → k x) ∧
    (∀ x, k x → b = true → x = m)))

-- Function-valued parameters are array arguments; models read them with `select`.
run_elab do
  unless ← z3Available do return
  expectSolvedIntro (← `(∀ (ap : Int → Int → Int) (t : Int), ∃ k : Int → Prop,
    (∀ v, 666 < ap t v → k v) ∧ (∀ v, k v → 0 < ap t v)))
  expectSolvedIntro (← `(∀ (p : Int → Prop) (q : Int → Bool), ∃ k : Int → Prop,
    (∀ x, p x → q x = true → k x) ∧ (∀ x, k x → p x)))

-- Parameters outside the supported sorts are rejected at export.
run_elab do
  let target ← elaborate (← `(∀ s : String, ∃ k : Int → Prop, (∀ x, s = "" → k x) ∧ (∀ x, k x → True)))
  let goal ← mkFreshExprMVar target
  let (_, inner) ← goal.mvarId!.intros
  inner.withContext do
    let result ← solveGoal inner { executable := some "/__flex_no_solver__" }
    let .failed failure := result | throwError "String parameter was accepted"
    unless failure.stage == .exporting do throwError "unexpected stage: {failure.message}"

/-! Model decoding maps encoder symbols back to the Lean datatypes they came from. -/

private def symbolOf (problem : ExportedProblem) (p : String → Bool) : MetaM String := do
  let some s := (problem.symbols.sorts.keys ++ problem.symbols.constructors.keys ++
      problem.symbols.selectors.keys).find? p
    | throwError "symbol not found"
  return s!"|{s}|"

-- Quantifiers over datatype sorts, testers, and selectors (projections and case splits).
run_elab do
  let target ← elaborate (← `(∃ k : Int → Prop,
    (∀ x (o : Option Int) (v : Vec), o = some x → v.len = x → k x) ∧ (∀ x, k x → x = x)))
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let s := problem.symbols
  let option ← symbolOf problem fun k => (s.sorts[k]?.map (·.isAppOf ``Option)).getD false
  let vec ← symbolOf problem fun k => (s.sorts[k]?.map (·.isAppOf ``Vec)).getD false
  let some_ ← symbolOf problem fun k => (s.constructors[k]?.map (·.ctor == ``Option.some)).getD false
  let val ← symbolOf problem fun k => (s.selectors[k]?.map (·.ctor == ``Option.some)).getD false
  let len ← symbolOf problem fun k => (s.selectors[k]?.map fun x => x.ctor == ``Vec.mk && x.field == 0).getD false
  let model := s!"(model (define-fun k_0 ((x!0 Int)) Bool
    (exists ((o {option}) (v {vec}))
      (! (and ((_ is {some_}) o) (= ({val} o) x!0) (= ({len} v) x!0) (= v (|{vec.drop 1 |>.dropEnd 1}| 0 true))) :weight 0))))"
  -- The last conjunct uses a sort as a constructor and must be rejected.
  let rejected ← try discard <| importWitnesses problem (response model); pure false catch _ => pure true
  unless rejected do throwError "a sort symbol was accepted as a constructor"
  let mk ← symbolOf problem fun k => (s.constructors[k]?.map (·.ctor == ``Vec.mk)).getD false
  let model := s!"(model (define-fun k_0 ((x!0 Int)) Bool
    (exists ((o {option}) (v {vec}))
      (! (and ((_ is {some_}) o) (= ({val} o) x!0) (= ({len} v) x!0) (= v ({mk} x!0 true))) :weight 0))))"
  let witnesses ← importWitnesses problem (response model)
  let expected ← elaborate (← `(fun x : Int => ∃ (o : Option Int) (v : Vec),
    (∃ y, o = some y) ∧ (match o with | some y => y | _ => default : Int) = x ∧ v.1 = x ∧
      v = ⟨x, @decide True (Classical.propDecidable True)⟩))
  unless ← isDefEq witnesses[0]!.value expected do
    throwError "unexpected decoding: {witnesses[0]!.value}"

/-! κ arguments of any encodable sort: datatypes and functions (arrays). -/

run_elab do
  unless ← z3Available do return
  -- enum and record arguments
  expectSolved (← `(∃ k : Gib → Int → Prop,
    (∀ x, x = 0 → k .a x) ∧ (∀ x, 0 < x → k .b x) ∧ (∀ g x, k g x → g = .b → 0 < x)))
  expectSolved (← `(∃ k : Vec → Prop,
    (∀ v : Vec, v.len = 0 → v.ok = true → k v) ∧
    (∀ v w : Vec, k v → w = ⟨v.len + 1, v.ok⟩ → k w) ∧ (∀ v, k v → 0 ≤ v.len)))
  -- `Option` and `Nat` arguments
  expectSolved (← `(∃ k : Option Int → Nat → Prop,
    (∀ n : Nat, k none n) ∧ (∀ (x : Int) (n : Nat), 0 < x → k (some x) n) ∧
    (∀ o n, k o n → ∀ x, o = some x → 0 < x)))
  -- a function argument
  expectSolved (← `(∃ k : (Int → Int) → Prop,
    (∀ f : Int → Int, f 0 = 1 → k f) ∧ (∀ f, k f → 0 < f 0)))

private opaque TokenCarrier : (α : Type) × Inhabited α := ⟨Unit, ⟨()⟩⟩
private def Token : Type := TokenCarrier.1
private instance : Inhabited Token := TokenCarrier.2

-- Opaque types are uninterpreted sorts, also as κ arguments.
run_elab do
  unless ← z3Available do return
  expectSolved (← `(∃ k : Int → Token → Prop,
    (∀ t : Token, k 0 t) ∧ (∀ x (t u : Token), k x t → u = t → x < 5 → k (x + 1) u) ∧
    (∀ x t, k x t → 0 ≤ x)))

/-! Bit vectors at literal widths. -/


run_elab do
  unless ← z3Available do return
  -- a bit-vector κ argument
  expectSolved (← `(∃ k : BitVec 32 → Prop,
    (∀ x : BitVec 32, ¬ BitVec.ule x (BitVec.ofInt 32 10) → k x) ∧
    (∀ x, k x → BitVec.ult (BitVec.ofInt 32 10) x)))
  -- `int2bv` through a definition, as in Flux's `alloc_layout_pow2`
  expectSolved (← `(∃ k : Int → Prop,
    (∀ a : Int, (a = 4 ∨ a = 8) → k a) ∧ (∀ a, k a → pow2bv (BitVec.ofInt 64 a))))
  -- Lean's semantics where SMT-LIB differs: `x / 0 = 0`, shifts past the width, `toInt`
  expectSolved (← `(∃ k : BitVec 8 → Prop,
    (∀ x : BitVec 8, k x) ∧
    (∀ x, k x → x / 0 = 0 ∧ x <<< (9 : Nat) = 0 ∧ (BitVec.ofInt 8 (-1)).toInt = -1)))

-- Decoding bit-vector literals and operators.
run_elab do
  let target ← elaborate (← `(∃ k : BitVec 8 → Prop, (∀ x : BitVec 8, k x) ∧ (∀ x, k x → True)))
  let goal ← mkFreshExprMVar target
  let prepared ← prepareGoal goal.mvarId!
  let problem ← exportConstraints prepared.kvars (← prepared.exportGoal.getType)
  let model := "(model (define-fun k_0 ((x!0 (_ BitVec 8))) Bool
    (and (bvule #x0a (bvand x!0 #b11110000)) (= ((_ extract 3 0) x!0) (_ bv5 4))
         (= (bv2nat (bvadd x!0 #x01)) 3) (bvsgt ((_ int2bv 8) 1) #xff))))"
  let witnesses ← importWitnesses problem (response model)
  let expected ← elaborate (← `(fun x : BitVec 8 =>
    BitVec.ule (BitVec.ofNat 8 10) (BitVec.and x (BitVec.ofNat 8 240)) = true ∧
    BitVec.extractLsb' 0 4 x = BitVec.ofNat 4 5 ∧
    ((BitVec.add x (BitVec.ofNat 8 1)).toNat : Int) = 3 ∧
    BitVec.slt (BitVec.ofNat 8 255) (BitVec.ofInt 8 1) = true))
  unless ← isDefEq witnesses[0]!.value expected do
    throwError "unexpected decoding: {witnesses[0]!.value}"

-- Non-linear arithmetic is encoded in Horn clauses (Spacer may still answer `unknown`).
run_elab do
  let goal ← mkFreshExprMVar (← elaborate (← `(∃ k : Int → Int → Prop,
    (∀ x y : Int, x = 3 → y = 4 → k x y) ∧ (∀ x y, k x y → x * y = 12 ∧ (x * y) % y = 0))))
  let prepared ← prepareGoal goal.mvarId!
  let script := (← exportConstraints prepared.kvars (← prepared.exportGoal.getType)).toSMTLib
  unless (script.splitOn "(* ").length > 1 && (script.splitOn "(mod ").length > 1 do
    throwError "non-linear terms were not exported:\n{script}"
