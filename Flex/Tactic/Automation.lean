import Flex.CHC.Certificate
import Flex.Tactic.Oracles
import Flex.PA.Smt

/-! SMT-first synthesis and checked residual automation. -/

open Lean Meta Elab Term Tactic

register_option flex.automation.proofHeartbeats : Nat := {
  defValue := 20000
  descr := "Heartbeats per proof leaf; conjunctions share their combined budget. Zero disables attempts."
}

register_option flex.automation.smtTimeout : Nat := {
  defValue := 30
  descr := "Seconds per reconstructed SMT proof; zero disables SMT proofs."
}

register_option flex.automation.synthTimeout : Nat := {
  defValue := 2
  descr := "Seconds per SMT synthesis batch; zero disables external synthesis."
}

register_option flex.automation.structureSteps : Nat := {
  defValue := 10000
  descr := "Maximum structural steps in residual discharge."
}

namespace Flex.Automation

private def proofLeaves : Expr → Nat
  | .app (.app (.const ``And _) left) right => proofLeaves left + proofLeaves right
  | _ => 1

/-- Each attempt is isolated, including helper declarations and diagnostic messages.
Fresh helper theorems are inlined into evidence in the caller's environment. -/
private def attempt (tactic : TSyntax `tactic) (target : Expr)
    (budgetLeaves : Nat := proofLeaves target)
    : TermElabM (Option Expr) := do
  let mut limit := flex.automation.proofHeartbeats.get (← getOptions) * 1000 * budgetLeaves
  if (← getMaxHeartbeats) != 0 then
    limit := min limit ((← getRemainingHeartbeats) / 2)
  if limit == 0 then return none
  let saved ← Term.saveState
  tryCatchRuntimeEx
    (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := limit }) <|
      Core.withCurrHeartbeats do
        try
          let candidate ← proveLeafWith tactic target
          Core.checkInterrupted
          let candidate ← candidate.mapM instantiateMVars
          let oracleEnvironment ← getEnv
          Flex.CHC.restoreTermState saved
          let some proof := candidate | return none
          let proof ← Meta.unfoldDeclsFrom oracleEnvironment proof
          if proof.hasMVar || proof.hasLevelMVar || proof.hasLooseBVars || proof.hasSorry then
            return none
          -- PA hypotheses may still mention assigned predicate metavariables.
          let closed ← mkLambdaFVars (← getLCtx).getFVars proof (usedOnly := true)
          checkWithKernel (← instantiateMVars closed)
          unless ← isDefEq (← inferType proof) target do return none
          for name in proof.getUsedConstants do
            for axiomName in ← collectAxioms name do
              unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
                return none
          return some proof
        finally Flex.CHC.restoreTermState saved)
    (fun error => do
      Flex.CHC.restoreTermState saved
      if error.isInterrupt then throw error
      Core.checkInterrupted
      return none)

/-- Simplify conjunctions, then try reconstructed SMT and the native portfolio.
Every accepted proof is kernel checked and uses only Lean's standard axioms. -/
def proofOracle : Flex.CHC.ProofOracle := fun target => do
  if target.isAppOfArity ``And 2 then
    if let some proof ← attempt
        (← `(tactic| (try simp_all (config := { maxSteps := 10000 })) <;> grind))
        target (budgetLeaves := 1) then return some proof
  let timeout := flex.automation.smtTimeout.get (← getOptions)
  if timeout != 0 then
    let prepare ← if target.isAppOfArity ``And 2 then
      `(tactic| try simp_all (config := { maxSteps := 10000 })) else `(tactic| skip)
    if let some proof ← attempt
        (← `(tactic| $prepare:tactic <;>
          smt (timeout := some $(quote timeout)) (trust := false) [*] <;>
          first | omega | grind |
            aesop (config := { maxRuleApplications := 200 }) (add unsafe 20% (by omega))))
        target then return some proof
  for tactic in #[← `(tactic| omega), ← `(tactic| grind),
      ← `(tactic| constructor <;> grind)] do
    if let some proof ← attempt tactic target then return some proof
  let needsSearch := fun e : Expr =>
    (e.find? fun e => e.isAppOfArity ``Exists 2 || e.isAppOfArity ``Or 2).isSome
  if needsSearch target || (← getLCtx).any (needsSearch ·.type) then
    if let some proof ← attempt
        (← `(tactic| aesop (config := { maxRuleApplications := 200 })
          (add unsafe 20% (by omega)))) target then return some proof
  attempt (← `(tactic|
    (try simp_all (config := { maxSteps := 10000 })) <;>
      first | omega | grind |
        aesop (config := { maxRuleApplications := 200 }) (add unsafe 20% (by omega)))) target

/-- Batch SMT decisions select candidates; only `proofOracle` builds evidence.
Unsupported or inconclusive SMT queries fall back to bounded native proofs. -/
def synthOracle (checkBudget : TermElabM Unit := pure ()) : PASynthOracle := fun targets => do
  checkBudget
  let timeout := flex.automation.synthTimeout.get (← getOptions)
  let results ← if timeout == 0 then
    pure (targets.map fun _ => PASynthResult.unknown "SMT synthesis disabled")
    else Flex.PA.smtOracle (timeout * 1000) targets
  checkBudget
  unless results.size == targets.size do
    throwError "PA synthesis oracle returned the wrong number of decisions"
  targets.zipWithM (fun target result => do
    checkBudget
    match result with
    | .valid | .invalid => return result
    | .unknown reason =>
      trace[flex.oracle] "SMT synthesis inconclusive: {reason}"
      for tactic in #[← `(tactic| omega), ← `(tactic| grind),
          ← `(tactic| constructor <;> grind)] do
        checkBudget
        let proof ← attempt tactic target
        checkBudget
        if proof.isSome then return .valid
      return result) results

/-- The structural walk used by `solve_fixpoint`, with checked leaf proofs and
finite progress. Definitions are retried only after their target changes; goals
that still mention unresolved predicates are retained for the caller. -/
private def dischargeImpl : TacticM Unit := do
  let mut pending := (← getGoals).map fun goal => (goal, ([] : List Expr))
  let mut remaining := []
  let mut fuel := flex.automation.structureSteps.get (← getOptions)
  while fuel > 0 && !pending.isEmpty do
    fuel := fuel - 1
    let (goal, seen) :: rest := pending | break
    pending := rest
    if ← goal.isAssignedOrDelayedAssigned then continue
    let next ← goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      if target.hasMVar || target.hasLevelMVar then return none
      let exposed ← whnfR target
      if exposed.isForall then
        let (_, next) ← goal.intro1
        return some [(next, seen)]
      if exposed.isAppOfArity ``And 2 then
        let children ← goal.apply (mkConst ``And.intro)
        return some (children.map fun child => (child, seen))
      if exposed.isConstOf ``True then
        goal.assign (mkConst ``True.intro)
        return some []
      if let some proof ← proofOracle target then
        goal.assign proof
        return some []
      if let some unfolded ← unfoldDefinition? target then
        if unfolded != target && !seen.contains unfolded then
          let next ← goal.replaceTargetDefEq unfolded
          return some [(next, target :: seen)]
      return none
    match next with
    | some goals => pending := goals ++ pending
    | none => remaining := goal :: remaining
  setGoals (remaining.reverse ++ pending.map Prod.fst)

/-- Restore the complete entry state if structural traversal itself fails. -/
def discharge : TacticM Unit := do
  let saved ← Tactic.saveState
  tryCatchRuntimeEx dischargeImpl fun error => do
    Flex.CHC.restoreTermState saved.term
    set saved.tactic
    throw error

end Flex.Automation
