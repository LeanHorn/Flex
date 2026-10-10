import Flex.CHC

/-! Real Spacer-to-Lean witness integration. The test-only tactic supplies all
existential witnesses from the returned model; ordinary Lean tactics then prove
the instantiated constraints. Requires `z3` on PATH and `lake lean` for the
native SMT parser. Production `fix` integration is a separate change. -/
namespace CHCInstantiateDemo

open Lean Meta Elab Tactic Flex.CHC

/-- Stop exactly at witness assignment, leaving invariant correctness to Lean. -/
elab "spacer_witnesses" : tactic => withMainContext do
  let asyncPrefix := (← getEnv).asyncPrefix?
  let checkEnvironment : TacticM Unit := do
    unless (← getEnv).asyncPrefix? == asyncPrefix do
      throwError "CHC operation changed the caller's asynchronous environment"
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro (← getMainGoal)
  let problem ← exportConstraints kvars (← bodyGoal.getType)
  checkEnvironment
  let result ← Spacer.run problem
  let witnesses ← importWitnesses problem result
  checkEnvironment
  unless witnesses.size == kvars.length do
    throwError "Spacer did not provide every existential witness"
  for kvar in kvars do
    if ← kvar.mvarId.isAssignedOrDelayedAssigned then
      throwError "preparing witnesses assigned an existential"
  if ← bodyGoal.isAssignedOrDelayedAssigned then
    throwError "preparing witnesses proved the constraint goal"
  assignWitnesses problem witnesses
  checkEnvironment
  for kvar in kvars do
    unless ← kvar.mvarId.isAssigned do
      throwError "assigning witnesses left an existential unresolved"
  if ← bodyGoal.isAssignedOrDelayedAssigned then
    throwError "assigning witnesses proved the constraint goal"
  let bodyGoal ← bodyGoal.replaceTargetDefEq (← instantiateMVars (← bodyGoal.getType))
  setGoals [bodyGoal]

theorem counter :
    ∃ k : Int → Prop,
      k 0 ∧ (∀ x, k x → k (x + 1)) ∧ (∀ x, k x → 0 ≤ x) := by
  spacer_witnesses
  refine ⟨?_, ?_, ?_⟩
  · omega
  · intro x hx
    omega
  · intro x hx
    omega

-- The Boolean argument matters: the two branches have opposite inequalities.
-- This checks the imported Prop parameter's adaptation back to an actual Bool.
theorem booleanBranches :
    ∃ k : Bool → Int → Prop,
      k true 0 ∧ k false 0 ∧
      (∀ x, k true x → k true (x + 1)) ∧
      (∀ x, k false x → k false (x - 1)) ∧
      (∀ x, k true x → 0 ≤ x) ∧
      (∀ x, k false x → x ≤ 0) := by
  spacer_witnesses
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp_all
  · simp_all
  · intro x hx
    simp_all
    omega
  · intro x hx
    simp_all
    omega
  · intro x hx
    simp_all
    omega
  · intro x hx
    simp_all
    omega

theorem relatedPredicates :
    ∃ entry exit : Int → Prop,
      entry 0 ∧ exit 1 ∧
      (∀ x, entry x → entry (x + 1)) ∧
      (∀ x, exit x → exit (x + 1)) ∧
      (∀ x, entry x → exit (x + 1)) ∧
      (∀ x, exit x → entry x) ∧
      (∀ x, entry x → 0 ≤ x) ∧
      (∀ x, exit x → 1 ≤ x) := by
  spacer_witnesses
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro x hx
    omega
  · intro x hx
    omega
  · intro x hx
    omega
  · intro x hx
    omega
  · intro x hx
    omega
  · intro x hx
    omega

run_elab do
  for name in [``counter, ``booleanBranches, ``relatedPredicates] do
    let axioms ← collectAxioms name
    if axioms.contains ``sorryAx || axioms.contains `autoSMTSorry then
      throwError "incomplete or trusted evidence in Spacer witness proof: {name}"

end CHCInstantiateDemo
