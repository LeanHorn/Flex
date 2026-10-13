import Flex.VCG.LambdaRK.Bridge.Semantics
import Flex.CHC.Certificate

/-!
# Checked reconstruction and residual goals

Lowering proposes a scalar clause. Reconstruction proves its implication to the
original λRK clause with ordinary Lean tactics; unsupported translations never
become assumptions. The CHC certificate API supplies the same evidence checks
for this bridge as for the solver's final invariant certificates.
-/

namespace LambdaRK.Bridge

open Lean Meta Elab Term Tactic

/-- Reusable admission-free oracle invocation with transactional state and
transitive axiom checking. -/
def checkedProof (oracle : Flex.CHC.ProofOracle) (target : Lean.Expr) :
    TermElabM (Option Lean.Expr) :=
  Flex.CHC.checkOracleProof oracle target

/-- Try to certify `scalarClause → sourceClause.Valid`. The signature and source
constraint must be quoted constructor expressions so simplification can inspect
their declarations without unfolding arbitrary user definitions. The relation
predicates themselves remain abstract local variables during this proof. -/
def proveBridge (target : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let tactic ← `(tactic| (
    intro scalarClause
    simp (config := { contextual := true })
      [Cstr.Valid, lambda_rk_bridge, Environment.bind, List.lookup_cons,
        measure_ctor, Signature.findMeasure]
      <;> grind [MeasureEval.deterministic]))
  checkedProof (proveLeafWith tactic) target

/-- Expose the semantic content of an instantiated source clause and introduce
its binders. No solver or proof oracle is run: a remaining measure fact is kept
as a `MeasureEval` obligation, preserving the partial semantics of observations.
If cleanup cannot run, the original goal remains available unchanged. -/
def cleanSourceGoal (goal : MVarId) : TermElabM (List MVarId) := do
  let saved ← Term.saveState
  try
    goal.withContext do
      let tactic ← `(tactic| (
        simp (config := { contextual := true })
          [Cstr.Valid, lambda_rk_bridge, Environment.bind, List.lookup_cons,
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

end LambdaRK.Bridge
