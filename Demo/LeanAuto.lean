import Flex

/-! Integration with the real lean-auto/Z3 backend. Requires `z3` on PATH. -/

namespace LeanAutoDemo

set_option auto.smt.solver.name "z3"
set_option auto.smt.timeout 2

opaque secret : Int := 7
theorem secret_spec : secret = 7 := by native_decide

def needsAuto : Prop := ∃ k : Int → Prop,
  k 7 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → secret ≤ n)

theorem fallback_used : needsAuto := by
  fix (scrape := head) (oracle := flex_auto [*, secret_spec])

open Lean Meta Elab Term in
run_elab do
  -- The default oracle cannot establish the opaque constant's value.
  let goal ← elabTerm (← `(secret = 7)) none
  if (← proveLeaf goal).isSome then throwError "example no longer requires SMT"
  -- Confirm that the proof above actually used the external oracle.
  unless (← collectAxioms ``fallback_used).contains ``autoSMTSorry do
    throwError "expected a real trusted SMT query"
  -- A satisfiable negation must not be accepted as a valid implication.
  let result ← proveLeafWith (← `(tactic| flex_auto)) (mkConst ``False)
  unless result.isNone do throwError "SMT accepted an invalid query"

end LeanAutoDemo
