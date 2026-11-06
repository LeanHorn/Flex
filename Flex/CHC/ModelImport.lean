import Flex.CHC.Witness
import Smt2Lean.Model

/-!
Registers SMTLib-to-Lean's model translator for Spacer/Eldarica witness import.

Kept separate from `Flex.CHC.Witness` because `Smt2Lean.Model` imports Mathlib's reals.
The core tactics (`Flex.Tactic.Tactics.Flex`) do not import it, so the native `flex-lean`
runner links them without compiling Mathlib. `Flex` and `Flex.CHC` import it.
-/

namespace Flex.CHC

initialize
  modelImporter.set <| some fun input environment name => do
    let response ← Smt2Lean.Model.importResponse input environment name
    return { status := response.status, definitions := response.definitions
             diagnostics := response.diagnostics }

end Flex.CHC
