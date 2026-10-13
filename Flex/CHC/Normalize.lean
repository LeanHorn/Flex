import Flex.CHC.Prepare
import Lean.Meta.Tactic.Simp

namespace Flex.CHC

open Lean Meta

private def bounded (count limit : Nat) : MetaM Nat := do
  if count > limit then
    throwError "CHC normalization: expanded constraints exceed the clause limit ({limit})"
  return count

/-- Count branches before duplicating any consequent. Conjunctions multiply
alternatives; disjunctions add them; existential antecedents add only binders. -/
private partial def antecedentBranches (input : Expr) (limit : Nat) : MetaM Nat := do
  let input ← Prepare.expose input
  if let some (left, right) := input.and? then
    bounded ((← antecedentBranches left limit) * (← antecedentBranches right limit)) limit
  else if let some (left, right) := input.or? then
    bounded ((← antecedentBranches left limit) + (← antecedentBranches right limit)) limit
  else if input.isAppOfArity ``Exists 2 then
    let domain := input.getArg! 0
    let predicate := input.getArg! 1
    withLocalDeclD `witness domain fun witness =>
      antecedentBranches (predicate.beta #[witness]) limit
  else
    return 1

/-- Match the body shape consumed by export: leading binders/guards and a tree
of conjunctions. This is a conservative bound when simplification removes work. -/
private partial def expandedClauses (input : Expr) (limit : Nat) : MetaM (Nat × Bool) := do
  let input ← Prepare.expose input
  if input.isConstOf ``True then return (0, false)
  if let some (left, right) := input.and? then
    let (leftCount, leftChanged) ← expandedClauses left limit
    let (rightCount, rightChanged) ← expandedClauses right limit
    return (← bounded (leftCount + rightCount) limit, leftChanged || rightChanged)
  if let .forallE name domain body bi := input then
    withLocalDecl name bi domain fun parameter => do
      let (count, changed) ← expandedClauses (body.instantiate1 parameter) limit
      if (← isProp domain) && !body.hasLooseBVar 0 then
        let domain ← Prepare.expose domain
        let structural := domain.and?.isSome || domain.or?.isSome || domain.isAppOfArity ``Exists 2
        return (← bounded ((← antecedentBranches domain limit) * count) limit,
          changed || structural)
      return (count, changed)
  else
    return (← bounded 1 limit, false)

/-- Normalize Horn antecedents with proof-producing logical equivalences only:
`(∃ x, P x) → Q`, `(P ∨ R) → Q`, and `(P ∧ R) → Q`. This makes the
strongest predicates produced by acyclic elimination usable by CHC export.

The original goal is connected to the returned goal by Lean's simplifier proof.
Existential predicate slots remain unassigned, and even `True` remains an open
goal for the ordinary certificate stage. No user definitions or global simp
lemmas are unfolded. The expansion bound is checked before distributing guards;
any failure restores the caller's meta state. Export and certification must both
consume the returned goal so their clause counts and provenance agree. -/
def normalizeGoal (bodyGoal : MVarId) (maxClauses : Nat := 1024) : MetaM MVarId := do
  let saved ← Meta.saveState
  try
    bodyGoal.withContext do
      if maxClauses == 0 then throwError "CHC normalization: maxClauses must be positive"
      bodyGoal.checkNotAssigned `chc_normalize
      let target ← instantiateMVars (← bodyGoal.getType)
      unless ← isProp target do throwError "CHC normalization: expected a proposition"
      let (_, changed) ← expandedClauses target maxClauses
      unless changed do return bodyGoal
      let mut theorems : SimpTheorems := {}
      for name in [``exists_imp, ``or_imp, ``and_imp] do
        theorems ← theorems.addConst name
      let context ← Simp.mkContext {
        failIfUnchanged := false, iota := false, proj := false, etaStruct := .none
        maxSteps := 100000 } #[theorems]
      let (some normalized, _) ← simpTarget bodyGoal context (mayCloseGoal := false)
        | throwError "CHC normalization unexpectedly closed the body goal"
      -- Keep a postcondition as well as the preflight bound, in case Lean's
      -- simplifier exposes additional beta/let wrappers while rewriting.
      discard <| expandedClauses (← normalized.getType) maxClauses
      return normalized
  catch error =>
    saved.restore
    throw error

end Flex.CHC
