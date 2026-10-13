import Flex.VCG.SystemFRK.Bridge.Semantics
import Flex.CHC.Certificate

/-! Certify scalar-to-source implications and simplify residual goals. -/

namespace SystemFRK.Bridge

open Lean Meta Elab Term Tactic

/-- Run the shared oracle with state rollback and transitive admission checking. -/
def checkedProof (oracle : Flex.CHC.ProofOracle) (target : Lean.Expr) :
    TermElabM (Option Lean.Expr) :=
  Flex.CHC.checkOracleProof oracle target

/-- Certify `scalarClause → sourceClause.Valid` with abstract predicates and reflected source syntax. -/
def proveBridge (target : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let tactic ← `(tactic| (
    intro scalarClause
    -- Definedness guards can add scalar witnesses used only in reflexive
    -- equalities. Remove those vacuous scalar binders before instantiation.
    simp (config := { contextual := true })
      [Cstr.Valid, system_frk_bridge, Environment.bind, List.lookup_cons,
        measure_ctor, Signature.findMeasure] at scalarClause ⊢
      <;> grind [MeasureEval.deterministic]))
  checkedProof (proveLeafWith tactic) target

/-- Simplify residual binders, retaining undefined `MeasureEval` obligations.
Failure restores the original goal. -/
def cleanSourceGoal (goal : MVarId) : TermElabM (List MVarId) := do
  let saved ← Term.saveState
  try
    goal.withContext do
      let tactic ← `(tactic| (
        simp (config := { contextual := true })
          [Cstr.Valid, system_frk_bridge, Environment.bind, List.lookup_cons,
            measure_ctor, Signature.findMeasure]
          <;> intros))
      let goals ← Tactic.run goal (evalTactic tactic)
      Core.checkInterrupted
      return goals
  catch error =>
    -- Ordinary `SavedState.restore` intentionally retains diagnostic/info
    -- state. A failed cleanup should leave the caller's state exactly intact.
    set saved.elab
    modifyThe Meta.State fun _ => saved.meta.meta
    modifyThe Core.State fun _ => saved.meta.core.toState
    if error.isInterrupt then throw error
    return [goal]

end SystemFRK.Bridge
