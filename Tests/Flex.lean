import Flex.Tactic.Tactics.Flex

open Lean Meta Elab Tactic

-- State assertions and intentionally rolled-back tactics need not change goals.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace FlexTests

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
