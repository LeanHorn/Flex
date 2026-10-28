import Flex.CHC.Certificate
import Flex.Tactic.Oracles
import Flex.PA.Smt

/-! SMT-first synthesis and checked residual automation. -/

open Lean Meta Elab Term Tactic

initialize registerTraceClass `flex.synthesis

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

register_option flex.automation.functionSmt : Bool := {
  defValue := false
  descr := "Try an additional CVC5 synthesis batch for function-valued inputs."
}

register_option flex.automation.structureSteps : Nat := {
  defValue := 10000
  descr := "Maximum structural steps in residual discharge."
}

namespace Flex.Automation

/-- Expose named quantified specifications without unfolding arithmetic relations. -/
private def exposeTarget : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let .const name _ := target.getAppFn | throwError "expected a named specification"
  let .defnInfo _ ← getConstInfo name | throwError "expected a definition"
  let exposed ← withTransparency .default <| whnf target
  unless exposed.isForall do throwError "specification is not quantified"
  if ← isProp exposed.bindingDomain! then throwError "expected a data quantifier"
  replaceMainGoal [← goal.replaceTargetDefEq exposed]

private def generalizeRecordFields : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let hypotheses ← Smt.Preprocess.getPropHyps
  let types ← hypotheses.mapM fun id => id.getType
  let fields ← Flex.PA.recordFields (types.push (← goal.getType))
  unless fields.isEmpty do
    let args := fields.mapIdx fun i field =>
      ({ expr := field, xName? := some (Name.mkSimple s!"field_{i}") } : GeneralizeArg)
    let (_, inputs, goal) ← goal.generalizeHyp args hypotheses
    let mut goal := goal
    for input in inputs do
      goal ← goal.withContext do
        goal.replaceLocalDeclDefEq input (← whnf (← input.getType))
    replaceMainGoal [goal]

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

/-- Run a tactic in isolation and accept only kernel-checked evidence. -/
def proveWith (tactic : TSyntax `tactic) (target : Expr) : TermElabM (Option Expr) :=
  attempt tactic target

private theorem listEqReplicateOfPrefix {α : Type u} (xs : List α) (i : Int) (value : α)
    (bound : xs.length ≤ i)
    (h : ∀ j : Nat, (j : Int) < i → xs[j]? = some value) :
    xs = List.replicate xs.length value := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_replicate]
  split <;> grind

private def listPrefixShape (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isForall && e.bindingDomain!.isConstOf ``Nat &&
    e.bindingBody!.isForall &&
    e.bindingBody!.bindingBody!.isAppOfArity ``Eq 3 &&
    e.bindingBody!.bindingBody!.appArg!.isAppOfArity ``Option.some 2 &&
    (e.bindingBody!.bindingBody!.getArg! 1).isAppOfArity ``GetElem?.getElem? 7

/-- At a completed homogeneous prefix, expose the corresponding constant list. -/
private def completeListPrefixes : TacticM Unit := withMainContext do
  let mut pending := (← getLCtx).getFVars
  let mut fuel := 128
  let mut rewritten := false
  let mut seen : ExprSet := {}
  while !pending.isEmpty && fuel > 0 do
    fuel := fuel - 1
    let proof := pending.back!
    pending := pending.pop
    let type := (← instantiateMVars (← inferType proof)).headBeta
    if type.isAppOfArity ``And 2 then
      pending := pending.push (← mkAppM ``And.left #[proof])
        |>.push (← mkAppM ``And.right #[proof])
    else if listPrefixShape type then
      let data ← withLocalDeclD `j (mkConst ``Nat) fun j => do
        let body := type.bindingBody!.instantiate1 j
        let guard := body.bindingDomain!
        let args := guard.getAppArgs
        let index? := if guard.isAppOfArity ``LT.lt 4 && args[0]!.isConstOf ``Int then
            some (args[2]!, args[3]!)
          else if guard.isAppOfArity ``Int.lt 2 then some (args[0]!, args[1]!) else none
        let some (cast, index) := index? | return none
        unless ← isDefEq cast (mkApp (mkConst ``Int.ofNat) j) do return none
        let equality := body.bindingBody!
        if equality.hasLooseBVar 0 then return none
        let read := equality.getArg! 1
        let xs := read.getArg! 5
        let value := equality.appArg!.appArg!
        if xs.containsFVar j.fvarId! || index.containsFVar j.fvarId! ||
            value.containsFVar j.fvarId! then return none
        unless ← isDefEq (read.getArg! 6) j do return none
        return some (xs, index, value)
      let some (xs, index, value) := data | continue
      if seen.contains xs then continue
      let listType ← whnf (← inferType xs)
      unless listType.isAppOfArity ``List 1 do continue
      let length ← mkAppM ``List.length #[xs]
      let bound ← mkAppM ``LE.le #[mkApp (mkConst ``Int.ofNat) length, index]
      let some boundProof ← proveLeafWith (← `(tactic|
        first | omega | (dsimp (config := { maxSteps := 10000 }) at *; omega))) bound
        | continue
      let equality ← mkAppM ``listEqReplicateOfPrefix #[xs, index, value, boundProof, proof]
      try
        let goal ← getMainGoal
        let result ← goal.rewrite (← goal.getType) equality
        unless result.mvarIds.isEmpty do throwError "prefix rewrite created obligations"
        replaceMainGoal [← goal.replaceTargetEq result.eNew result.eqProof]
        rewritten := true
        seen := seen.insert xs
      catch error =>
        if error.isInterrupt then throw error
  unless rewritten do throwError "no completed list prefix"

private def proveCompletedPrefix (target : Expr) : TermElabM (Option Expr) := do
  let target ← instantiateMVars target
  let mut found := (target.find? listPrefixShape).isSome
  unless found do
    for decl in ← getLCtx do
      if ((← instantiateMVars decl.type).find? listPrefixShape).isSome then
        found := true
        break
  unless found do return none
  let limit := min 5000 (flex.automation.proofHeartbeats.get (← getOptions))
  withOptions (·.set `flex.automation.proofHeartbeats limit) <|
    attempt (← `(tactic| (run_tac completeListPrefixes) <;>
      simp (config := { maxSteps := 10000 }) <;> intros <;> grind)) target
      (budgetLeaves := 1)

/-- Simplify conjunctions, then try reconstructed SMT and the native portfolio.
Every accepted proof is kernel checked and uses only Lean's standard axioms. -/
def proofOracle : Flex.CHC.ProofOracle := fun target => do
  if let some proof ← proveCompletedPrefix target then return some proof
  let quickLimit := min 500 (flex.automation.proofHeartbeats.get (← getOptions))
  if let some proof ← withOptions (·.set `flex.automation.proofHeartbeats quickLimit) <|
      attempt (← `(tactic| (run_tac exposeTarget) <;> intros <;> grind)) target
        (budgetLeaves := 1) then return some proof
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
    if let some proof ← attempt
        (← `(tactic|
          (simp (config := { maxSteps := 10000, failIfUnchanged := false })
            [List.eq_replicate_iff] at *) <;> intros <;>
            (run_tac generalizeRecordFields) <;>
            smt (timeout := some $(quote timeout)) (trust := false) [*])) target then
      return some proof
  for tactic in #[← `(tactic| omega), ← `(tactic| grind),
      ← `(tactic| (run_tac exposeTarget) <;> intros <;> grind),
      ← `(tactic| constructor <;> grind),
      ← `(tactic| (simp (config := { maxSteps := 10000, failIfUnchanged := true })
        [List.eq_replicate_iff] at *) <;> intros <;> grind)] do
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
  let start ← IO.monoMsNow
  let mut results ← if timeout == 0 then
    pure (targets.map fun _ => PASynthResult.unknown "SMT synthesis disabled")
    else Flex.PA.smtOracle (timeout * 1000) targets
  checkBudget
  unless results.size == targets.size do
    throwError "PA synthesis oracle returned the wrong number of decisions"
  trace[flex.synthesis] "scalar SMT: {targets.size} queries, {(← IO.monoMsNow) - start}ms"
  let pending := (Array.range results.size).filter fun i =>
    match results[i]! with | .unknown _ => true | _ => false
  if timeout != 0 && !pending.isEmpty then
    let start ← IO.monoMsNow
    let retry ← Flex.PA.simplifiedSmtOracle (timeout * 1000) (pending.map (targets[·]!))
    checkBudget
    trace[flex.synthesis] "simplified SMT: {pending.size} queries, \
      {(retry.filter (· == .valid)).size} valid, {(← IO.monoMsNow) - start}ms"
    for i in [:pending.size] do
      if let .valid := retry[i]! then results := results.set! pending[i]! .valid
  let pending := (Array.range results.size).filter fun i =>
    match results[i]! with | .unknown _ => true | _ => false
  if flex.automation.functionSmt.get (← getOptions) && timeout != 0 && !pending.isEmpty then
    let start ← IO.monoMsNow
    let retry ← Flex.PA.functionSmtOracle (timeout * 1000) (pending.map (targets[·]!))
    checkBudget
    trace[flex.synthesis] "function SMT: {pending.size} queries, \
      {(retry.filter (· == .valid)).size} valid, {(← IO.monoMsNow) - start}ms"
    for i in [:pending.size] do
      if let .valid := retry[i]! then results := results.set! pending[i]! .valid
  let pending := results.countP fun result => match result with | .unknown _ => true | _ => false
  let start ← IO.monoMsNow
  let answers ← targets.zipWithM (fun target result => do
    checkBudget
    match result with
    | .valid | .invalid => return result
    | .unknown reason =>
      trace[flex.oracle] "SMT synthesis inconclusive: {reason}"
      for tactic in #[← `(tactic| omega), ← `(tactic| grind),
          ← `(tactic| constructor <;> grind),
          ← `(tactic| (simp (config := { maxSteps := 10000, failIfUnchanged := true })
            [List.eq_replicate_iff] at *) <;> intros <;> grind)] do
        checkBudget
        let proof ← attempt tactic target
        checkBudget
        if proof.isSome then return .valid
      return result) results
  trace[flex.synthesis] "native fallback: {pending} queries, {(← IO.monoMsNow) - start}ms"
  return answers

/-- The structural walk used by `solve_fixpoint`, with checked leaf proofs and
finite progress. Definitions are retried only after their target changes; goals
that still mention unresolved predicates are retained for the caller. -/
private def dischargeImpl (oracle : Flex.CHC.ProofOracle) : TacticM Unit := do
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
      if let some proof ← oracle target then
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
def discharge (oracle : Flex.CHC.ProofOracle := proofOracle) : TacticM Unit := do
  let saved ← Tactic.saveState
  tryCatchRuntimeEx (dischargeImpl oracle) fun error => do
    Flex.CHC.restoreTermState saved.term
    set saved.tactic
    throw error

end Flex.Automation

/-- Prove residual VCs with checked SMT and Lean automation, leaving unsolved goals. -/
elab "flex_discharge" : tactic => Flex.Automation.discharge
