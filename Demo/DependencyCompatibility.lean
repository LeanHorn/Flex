import Flex
import Flex.Tactic.Oracles.Smt
import Smt2Lean

/-! Check the shared lean-smt/cvc5 dependencies in one environment. The native
parser and expression reconstruction must work alongside Flex's proof oracles.
Run with `lake lean`, which loads cvc5's native plugin. -/

namespace DependencyCompatibility

open Lean Meta Qq

run_elab do
  let env ← getEnv
  let input := "(set-logic LIA)\n\
    (define-fun bump ((x Int)) Int (+ x 1))\n\
    (assert (forall ((n Int)) (> (bump n) n)))\n(check-sat)"
  (Smt2Lean.Backend.parseAndInspectQuery input fun query => do
    let check : MetaM Unit := Smt2Lean.Translate.withAssertions query fun parameters assertions => do
      unless parameters.isEmpty && assertions.size == 1 do
        throwError "unexpected SMT reconstruction shape"
      unless ← isDefEq assertions[0]! q(∀ n : Int, n + 1 > n) do
        throwError "SMT definition did not reconstruct to the expected Lean proposition"
    discard <| check.toIO { fileName := "dependency-compatibility", fileMap := default } { env }
  ).runIO

set_option auto.smt.timeout 1

def counter : Prop := ∃ k : Int → Prop,
  k 0 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → 0 ≤ n)

theorem counter_proof : counter := by
  fix (scrape := head) (synth := flex_auto) (proof := flex_smt [*])

-- Exercise reconstruction directly, so a fallback cannot hide incompatibility.
theorem arithmetic_proof (x y : Int) (h : x ≤ y) : x + 1 ≤ y + 1 := by
  flex_smt [h]

run_elab do
  for name in [``counter_proof, ``arithmetic_proof] do
    let axioms ← collectAxioms name
    if axioms.contains ``sorryAx || axioms.contains ``autoSMTSorry then
      throwError "incomplete or trusted evidence in compatibility proof: {name}"

end DependencyCompatibility
