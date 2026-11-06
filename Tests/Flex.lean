import Flex.Tactic.Tactics.Flex

open Lean Meta Elab Tactic

-- State assertions and intentionally rolled-back tactics need not change goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace FlexTests

-- Check the structural rewrite proofs, including quantifiers over empty types.
open Lean Elab Term in
run_elab do
  for (source, expected) in #[
      (← `(∀ p : Prop, True ∧ p), ← `(∀ p : Prop, p)),
      (← `(∀ p : Prop, False ∨ (p ∧ True)), ← `(∀ p : Prop, p)),
      (← `(∀ p : Prop, (True ∨ p) ∧ (p ∨ True)), ← `(True)),
      (← `(∀ p : Prop, (False ∧ p) ∨ (p ∧ False)), ← `(∀ p : Prop, False)),
      (← `(∀ p : Prop, True → (False → p)), ← `(True)),
      (← `(¬(True ∧ False)), ← `(True)),
      (← `(∃ x : Int, False ∨ False), ← `(False)),
      (← `(∀ _ : Empty, True ∧ True), ← `(True)),
      (← `(∀ _ : Empty, False), ← `(∀ _ : Empty, False)),
      (← `(∃ _ : Empty, True), ← `(∃ _ : Empty, True)),
      (← `(∀ h : True, h = h), ← `(∀ h : True, h = h))] do
    let source ← elabTerm source none
    let expected ← elabTerm expected none
    synthesizeSyntheticMVarsNoPostponing
    let source ← instantiateMVars source
    let expected ← instantiateMVars expected
    let (result, proof) ← Flex.Preprocess.simplifyTrueFalse source
    unless ← isDefEq result expected do throwError "unexpected True/False simplification: {result}"
    checkWithKernel proof
    unless ← isDefEq (← inferType proof) (mkApp2 (mkConst ``Iff) source result) do
      throwError "incorrect True/False equivalence"

-- Default preparation does not eliminate equality-bound witnesses.
example : ∀ x : Int, (∃ y : Int, y = x ∧ 0 ≤ y) → 0 ≤ x := by
  flex (backends := []) (config := { zap := false, closeLeaves := false })
  guard_target =~ (∀ x : Int, (∃ y : Int, y = x ∧ 0 ≤ y) → 0 ≤ x)
  grind

-- Enabling cleanup must not invoke it when Zap has no eliminable predicate.
example : ∃ k : Int → Prop, (∀ x, k x → k x) := by
  run_tac do
    let events ← IO.mkRef (#[] : Array Flex.Portfolio.PhaseEvent)
    Flex.Portfolio.flexImpl {
      backends := []
      config := { postprocess := true, closeLeaves := false }
      onPhase := fun e => events.modify (·.push e) }
    if (← events.get).any (·.phase == "postprocess") then
      throwError "postprocessing ran after a no-op Zap"
  exact ⟨fun _ => True, fun _ h => h⟩

/-- info: flex: fix completed the predicate goal -/
#guard_msgs in
example : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex (backends := [fix]) (config := { report := true })

-- Plain `flex` discovers function frames without a candidate-pool override.
example : ∃ k : (Int → Int) → (Int → Int) → Prop,
    (∀ f, k f f) ∧ (∀ f g, k f g → k f g) ∧
      (∀ f g, k f g → ∀ p : (Int → Int) → Prop, p f → p g) := by
  flex

-- An insufficient source pool must roll back before trying ordinary qualifiers.
example : ∃ k : Int → Int → Int → Int → Prop,
    k 0 0 0 0 ∧
      (∀ a b c d, k a b c d → k (a + 1) (b + 1) (c + 1) (d + 1)) ∧
      (∀ a b c d, k a b c d → 0 ≤ a) := by
  flex (backends := [fix]) (config := {scrapeLimits := {maxInstancesPerKappa := 20}})

private partial def countExists : Expr → Nat
  | e@(.app f a) => (if e.isAppOfArity ``Exists 2 then 1 else 0) + countExists f + countExists a
  | .lam _ domain body _ | .forallE _ domain body _ => countExists domain + countExists body
  | .letE _ type value body _ => countExists type + countExists value + countExists body
  | .mdata _ e | .proj _ _ e => countExists e
  | _ => 0

private def expectPredicates (expected : Nat) : TacticM Unit := do
  let target ← instantiateMVars (← getMainTarget)
  unless countExists target == expected do
    throwError "expected {expected} remaining predicates, got {target}"

-- Solving one focused goal must preserve an unrelated sibling.
example (p : Prop) (hp : p) :
    (∃ k : Int → Prop, k 0 ∧ (∀ i, k i → k (i + 1)) ∧
      (∀ i, k i → 0 ≤ i)) ∧ p := by
  constructor
  · flex (backends := [fix])
  · exact hp

-- An unsuccessful closer leaves the original ordinary goal available.
example (p : Prop) (hp : p) : p := by
  flex (backends := []) (closer := fail "no proof")
  guard_target = p
  exact hp

-- A missing backend must retain Zap's exact elimination of `seed`.
set_option flex.spacer.executable "flex-test-no-such-solver" in
example : ∃ loop seed : Int → Prop,
    seed 0 ∧ (∀ i, seed i → loop i) ∧
    (∀ i, loop i → loop (i + 1)) ∧ (∀ i, loop i → 0 ≤ i) := by
  flex (backends := [spacer]) (config := { closeLeaves := false })
  run_tac expectPredicates 1
  refine ⟨fun i : Int => 0 ≤ i, ?_⟩
  grind

-- Unknown synthesis cannot commit an arbitrary predicate assignment.
set_option flex.automation.synthTimeout 0 in
set_option flex.automation.proofHeartbeats 0 in
example : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex (backends := [fix]) (config := { zap := false, closeLeaves := false })
  run_tac expectPredicates 1
  exact ⟨fun i => 0 ≤ i, by grind⟩

-- SMT can establish candidate validity even when head proof search is disabled.
-- The retained VC remains provable by the caller.
set_option flex.automation.proofHeartbeats 0 in
example : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex (backends := [fix]) (config := { closeLeaves := false })
  run_tac expectPredicates 0
  all_goals (and_intros <;> intros <;> omega)

set_option flex.automation.proofHeartbeats 0 in
example : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex (backends := [spacer]) (config := { closeLeaves := false })
  run_tac expectPredicates 0
  all_goals (and_intros <;> intros <;> omega)

-- Later spawn failures must not replace an earlier validated partial result.
set_option flex.automation.proofHeartbeats 0 in
set_option flex.spacer.executable "flex-test-no-such-spacer" in
set_option flex.eldarica.executable "flex-test-no-such-eldarica" in
example : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex (backends := [fix, spacer, eldarica]) (config := { closeLeaves := false })
  run_tac expectPredicates 0
  all_goals (and_intros <;> intros <;> omega)

-- A starved phase keeps the original existential available for a manual witness.
example : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  flex (backends := [fix])
    (config := { heartbeats := 1, zap := false, closeLeaves := false })
  run_tac expectPredicates 1
  guard_target =~ (∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i))
  exact ⟨fun i => 0 ≤ i, by grind⟩

-- A closer override has no fallback and must not discard a validated invariant.
example (p : Prop) (hp : p) : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) ∧ p := by
  flex (backends := [fix]) (closer := fail "manual proof")
  run_tac expectPredicates 0
  guard_target =~ (∀ i : Int, 0 ≤ i → 0 ≤ i) ∧ p
  constructor
  · intro i hi; exact hi
  · exact hp

-- The walker reaches predicate goals below both ∀ and ∧.
example : ∀ start : Int, 0 ≤ start →
    (∃ k : Int → Prop,
      k start ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i)) ∧
    0 ≤ start + 1 := by
  flex (backends := [fix])

-- Refuted invariant choices leave the original unsatisfiable VC untouched.
-- This checks a negative case without admitting a theorem.
open Lean Elab Term in
run_elab do
  let saved ← Term.saveState
  try
    let target ← elabTerm (← `(∃ k : Int → Prop,
      k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → i ≤ 5))) none
    synthesizeSyntheticMVarsNoPostponing
    let target ← instantiateMVars target
    let goal ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
    let remaining ← Tactic.run goal.mvarId! do
      evalTactic (← `(tactic| flex (backends := [fix]) (scrape := no)
        (config := { preprocess := false, zap := false, postprocess := false, closeLeaves := false })))
    unless remaining == [goal.mvarId!] && !(← goal.mvarId!.isAssigned) do
      throwError "a refuted candidate changed the entry goal"
    unless ← isDefEq (← goal.mvarId!.getType) target do
      throwError "a refuted candidate changed the original constraint"
  finally Flex.CHC.restoreTermState saved

end FlexTests

namespace StatefulFoldTests

-- The completion invariant and the unregistered helper equation must be discovered.
def step (s x : Int) := s + 2 * x

def consume (s : Int) : List Int → Int
  | [] => s
  | x :: xs => consume (step s x) xs

example : ∃ k : List Int → Int → List Int → Int → Prop,
    (∀ xs s, k xs s xs s) ∧
    (∀ x xs s original start, k (x :: xs) s original start →
      k xs (step s x) original start) ∧
    (∀ rest s original start, k rest s original start → rest = [] → s = consume start original) := by
  flex

-- Proposition-valued state can be copied and preserved like other data.
example : ∃ k : Prop → Prop → Prop,
    (∀ p, k p p) ∧ (∀ p q, k p q → k p q) ∧ (∀ p q, k p q → p = q) := by
  flex

end StatefulFoldTests

namespace TimeoutTests

-- A cancellable closer simulates expensive proof search without calling a solver.
private def waitForCancellation : TacticM Unit := do
  repeat
    Core.checkInterrupted
    IO.sleep 1

elab "wait_for_flex_timeout" : tactic => waitForCancellation

-- An expired S/E stage leaves its unassigned predicates available to Zap and Fix.
example : ∃ loop seed : Int → Prop,
    seed 0 ∧ (∀ i, seed i → loop i) ∧
    (∀ i, loop i → loop (i + 1)) ∧ (∀ i, loop i → 0 ≤ i) := by
  run_tac do
    let events ← IO.mkRef (#[] : Array Flex.Portfolio.PhaseEvent)
    Flex.Portfolio.flexImpl {
      config := { chcFirst := true, stageTimeout := 1, totalTimeout := 5 }
      backends := [.spacer, .fix]
      onPhase := fun e => do
        events.modify (·.push e)
        if e.phase == "spacer" && e.status == "start" then IO.sleep 1200 }
    let events ← events.get
    unless events.any (fun e => e.phase == "stage/se" && e.status == "timeout") &&
        events.any (fun e => e.phase == "zap" && e.status == "ok") &&
        events.any (fun e => e.phase == "fix" && e.status == "ok") do
      throwError "S/E timeout did not continue through Zap and Fix"

-- An accepted S/E invariant survives a timeout during certification.
set_option flex.automation.proofHeartbeats 0 in
example : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  run_tac do
    let events ← IO.mkRef (#[] : Array Flex.Portfolio.PhaseEvent)
    Flex.Portfolio.flexImpl {
      config := { chcFirst := true, stageTimeout := 1, totalTimeout := 3, closeLeaves := false }
      backends := [.spacer, .fix]
      onPhase := fun e => do
        events.modify (·.push e)
        if e.phase == "spacer/certificate" && e.status == "start" then
          while !(← IO.checkCanceled) do IO.sleep 1 }
    FlexTests.expectPredicates 0
    if (← events.get).any (fun e => e.phase == "zap" || e.phase == "fix") then
      throwError "accepted S/E invariant was resynthesized"
  all_goals (and_intros <;> intros <;> omega)

-- Expiring Fix cannot consume S/E's block or change a caller's sibling goal.
example (p : Prop) (hp : p) :
    (∃ loop seed : Int → Prop,
      seed 0 ∧ (∀ i, seed i → loop i) ∧
      (∀ i, loop i → loop (i + 1)) ∧ (∀ i, loop i → 0 ≤ i)) ∧ p := by
  constructor
  · run_tac do
      let events ← IO.mkRef (#[] : Array Flex.Portfolio.PhaseEvent)
      Flex.Portfolio.flexImpl {
        config := { stageTimeout := 2, totalTimeout := 6 }
        backends := [.fix, .spacer]
        onPhase := fun e => do
          events.modify (·.push e)
          if e.phase == "fix" && e.status == "start" then
            while !(← IO.checkCanceled) do IO.sleep 1 }
      let events ← events.get
      unless events.any (fun e => (e.phase == "stage/zap_fix" || e.phase == "attempt/fix") &&
          e.status == "timeout") &&
          events.any (fun e => e.phase == "attempt/spacer" && e.status == "start" &&
            e.budgetMs.any (· > 0)) &&
          events.any (fun e => e.phase == "spacer" && e.status == "ok") do
        throwError "Fix timeout did not preserve S/E's block"
  · exact hp

-- Spacer's complete attempt must leave time for Eldarica.
example : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) := by
  run_tac do
    let events ← IO.mkRef (#[] : Array Flex.Portfolio.PhaseEvent)
    Flex.Portfolio.flexImpl {
      config := { zap := false, totalTimeout := 6 }
      backends := [.spacer, .eldarica]
      onPhase := fun e => do
        events.modify (·.push e)
        if e.phase == "spacer" && e.status == "start" then
          while !(← IO.checkCanceled) do IO.sleep 1 }
    let events ← events.get
    unless events.any (fun e => e.phase == "attempt/spacer" && e.status == "timeout") &&
        events.any (fun e => e.phase == "attempt/eldarica" && e.status == "start" &&
          e.budgetMs.any (· > 0)) &&
        events.any (fun e => e.phase == "eldarica" && e.status == "ok") do
      throwError "Spacer consumed Eldarica's allocation"

example : True := by
  run_tac do
    let events ← IO.mkRef (#[] : Array Flex.Portfolio.PhaseEvent)
    Flex.Portfolio.flexImpl { backends := [], onPhase := fun e => events.modify (·.push e) }
    let events ← events.get
    unless events.any (·.status == "ok") && events.all (·.status != "interrupted") do
      throwError "successful phases were not reported correctly"

-- A timeout during discharge must preserve Zap's witness and keep caller siblings.
example (p : Prop) (hp : p) : (∃ k : Int → Prop, k 0 ∧ (∀ i, k i → p)) ∧ p := by
  constructor
  · flex (backends := []) (closer := wait_for_flex_timeout)
      (config := { totalTimeout := 1 })
    run_tac do
      unless !(← getMainTarget).isAppOfArity ``Exists 2 do
        throwError "timeout lost Zap's elimination"
    grind
  · exact hp

-- Expiring during PA must not discard an acyclic predicate already eliminated.
example : ∃ loop seed : Int → Prop,
    seed 0 ∧ (∀ i, seed i → loop i) ∧
    (∀ i, loop i → loop (i + 1)) ∧ (∀ i, loop i → 0 ≤ i) := by
  flex (backends := [fix]) (synth := wait_for_flex_timeout)
    (config := { totalTimeout := 1, closeLeaves := false })
  run_tac do
    let target ← getMainTarget
    unless target.isAppOfArity ``Exists 2 do throwError "lost the cyclic predicate"
    withLocalDeclD `k (target.getArg! 0) fun k => do
      if (target.appArg!.beta #[k]).isAppOfArity ``Exists 2 then
        throwError "timeout restored the eliminated acyclic predicate"
  refine ⟨fun i : Int => 0 ≤ i, ?_⟩
  grind

-- The synthesis deadline preserves Zap's progress independently of the pipeline cap.
set_option flex.fixpointTimeout 1 in
example : ∃ loop seed : Int → Prop,
    seed 0 ∧ (∀ i, seed i → loop i) ∧
    (∀ i, loop i → loop (i + 1)) ∧ (∀ i, loop i → 0 ≤ i) := by
  -- The PA deadline applies even without a whole-pipeline deadline.
  flex (backends := [fix]) (synth := wait_for_flex_timeout)
    (config := { totalTimeout := 0, closeLeaves := false })
  run_tac do
    let target ← getMainTarget
    unless target.isAppOfArity ``Exists 2 do throwError "lost the cyclic predicate"
    withLocalDeclD `k (target.getArg! 0) fun k => do
      if (target.appArg!.beta #[k]).isAppOfArity ``Exists 2 then
        throwError "PA timeout lost Zap's checkpoint"
  refine ⟨fun i : Int => 0 ≤ i, ?_⟩
  grind

-- A validated Fix candidate also survives a timeout in the remaining proof.
example (p : Prop) (hp : p) : ∃ k : Int → Prop,
    k 0 ∧ (∀ i, k i → k (i + 1)) ∧ (∀ i, k i → 0 ≤ i) ∧ p := by
  flex (backends := [fix]) (closer := wait_for_flex_timeout)
    (config := { zap := false, totalTimeout := 3 })
  run_tac do
    if (← getMainTarget).isAppOfArity ``Exists 2 then
      throwError "timeout lost the validated Fix invariant"
  all_goals grind

open Lean Elab Term in
run_elab do
  -- A timed-out computation cannot commit assignments, even if it made progress.
  let goal ← mkFreshExprMVar (some (mkConst ``True)) (kind := .syntheticOpaque)
  let remaining ← Tactic.run goal.mvarId! do
    let result ← Flex.Timeout.run (some ((← IO.monoMsNow) + 50)) do
      evalTactic (← `(tactic| trivial))
      waitForCancellation
    unless result.isNone do throwError "deadline was not enforced"
    unless !(← goal.mvarId!.isAssigned) do throwError "timed-out assignment escaped"
  unless remaining == [goal.mvarId!] do throwError "timeout changed the caller's goals"
  -- A caller's interrupt must propagate, rather than looking like a local timeout.
  let token ← IO.CancelToken.new
  let signal ← (do IO.sleep 20; token.set : BaseIO Unit).asTask (prio := .dedicated)
  let action : TermElabM Unit := do
    discard <| Tactic.run goal.mvarId! do
      discard <| Flex.Timeout.run (some ((← IO.monoMsNow) + 1000)) waitForCancellation
  let action := (action.run (← readThe Term.Context) (← getThe Term.State)).run
    (← readThe Meta.Context) (← getThe Meta.State)
  let result ← (action.run' { (← readThe Core.Context) with cancelTk? := some token }
    (← getThe Core.State)).toBaseIO
  unless result matches .error (.internal _ _) do throwError "caller cancellation was swallowed"
  if let .error error := result then
    unless error.isInterrupt do throwError "caller cancellation changed exception kind"
  discard <| IO.wait signal
  -- Native process cancellation must complete before the timeout returns.
  unless System.Platform.isWindows do
    let stopped ← IO.mkRef false
    let start ← IO.monoMsNow
    discard <| Tactic.run goal.mvarId! do
      let result ← Flex.Timeout.run (some (start + 100)) do
        discard <| Flex.CHC.Process.run {
          executable := "/bin/sh", args := #["-c", "exec sleep 10"], timeoutMs := 5000 } ""
        stopped.set true
      unless result.isNone do throwError "native call ignored the deadline"
    unless (← stopped.get) && (← IO.monoMsNow) - start < 2000 do
      throwError "native cancellation did not finish promptly"

end TimeoutTests
