import Flex
import Flex.Tactic.Oracles.Smt

/-! Trusted candidate checks must not leak into independently reconstructed
certificates. Requires Z3 for `flex_auto`; lean-smt uses its bundled cvc5 FFI. -/
namespace OracleRoutingDemo

set_option auto.smt.timeout 1
set_option auto.smt.solver.name "z3"

def counterVC : Prop := ∃ k : Int → Prop,
  k 0 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → 0 ≤ n)

theorem lean_certificate : counterVC := by
  fix (scrape := head) (synth := flex_auto)

theorem smt_certificate : counterVC := by
  fix (scrape := head) (synth := flex_auto) (proof := flex_smt [*])

-- The proof route must fall back if its preferred tactic leaves an obligation.
theorem incomplete_proof_fallback : counterVC := by
  fix (scrape := head) (proof := skip)

opaque seven : Int := 7
theorem seven_eq : seven = 7 := by native_decide

def needsHint : Prop := ∃ k : Int → Prop,
  k 7 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → seven ≤ n)

-- Both external routes receive a fact unavailable to the default oracle.
theorem external_proof_required : needsHint := by
  fix (scrape := head) (synth := flex_auto [*, seven_eq])
    (proof := flex_smt [*, seven_eq])

open Lean Meta Elab Term in
run_elab do
  for name in [``lean_certificate, ``smt_certificate, ``incomplete_proof_fallback,
      ``external_proof_required] do
    let axioms ← collectAxioms name
    if axioms.contains ``autoSMTSorry || axioms.contains ``sorryAx then
      throwError "trusted synthesis leaked into certificate {name}: {axioms}"
  let opaqueFact ← elabTerm (← `(seven = 7)) none
  if (← proveLeaf opaqueFact).isSome then
    throwError "external proof regression no longer requires its explicit hint"
  -- Exercise the actual reconstruction backend without a Lean fallback.
  let valid ← elabTerm (← `(∀ x y : Int, x ≤ y → x + 1 ≤ y + 1)) none
  unless (← proveLeafWith (← `(tactic| flex_smt [*])) valid).isSome do
    throwError "lean-smt did not reconstruct the arithmetic proof"
  unless (← proveLeafWith (← `(tactic| flex_smt [*])) (mkConst ``False)).isNone do
    throwError "lean-smt accepted an invalid query"

end OracleRoutingDemo
