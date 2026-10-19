import Flex.VCG.STLC.Spec.Syntax
import Flex.VCG.STLC.Spec.Logic
import Flex.VCG.STLC.Spec.Semantics
import Flex.VCG.STLC.Spec.Denotation
import Flex.VCG.STLC.Spec.Theorems

/-! # The trusted base

  The mechanization proves "every program the checker accepts is safe". For
  that to mean anything, only the meaning of *safe* has to be right; the checker
  itself is certified by the proofs. The files under `Spec/` are everything that
  meaning depends on, in reading order:

  1. `Spec/Syntax` — expressions and values, opening an expression with a value,
     type erasure; the refinement logic's syntax; types; datatype declarations
     and measure bodies.
  2. `Spec/Semantics` — fuel-indexed big-step evaluation (`Eval`) and `Run`.
     Stuck states must have no rule, and `.timeout` may only come from running
     out of fuel: otherwise "never gets stuck" would be vacuous.
  3. `Spec/Logic` — runtime environments and the interpretation of terms,
     formulas and refinements; the measures' definitions (`DEnv.measEval`).
  4. `Spec/Denotation` — the meaning of types (`TyDenote`).
  5. `Spec/Theorems` — the headline theorems (`type_safety`, `check_safety`,
     `vcgen_safety`, `vcgen_no_stuck`, `vcgen_partial_correct`) and their axiom
     checks.

  Also trusted: Lean's kernel, and — for a particular example — its program and
  specification, including any `Notation` used to write them. A κ in the final
  type is chosen by the solver, so headline specifications should be κ-free.

  **Need only be satisfiable.** The theorems' hypotheses — `Hastype`, `Check`,
  `topVC`, `DEnv.wfB`, `Exp.WFBVars`, `Ty.WFBVars` — are defined in `Checker/`.
  A mistake there can make the checker reject good programs, but not accept bad
  ones; what matters is that the hypotheses can be met, which the end-to-end
  examples (`data_sumList_safe`, `meas_headClient_safe`) show.

  **Untrusted.** `Checker/` (operations, well-formedness, measure facts, typing
  rules, VC generation), `Proofs/`, and `Tactics/` (Flex's tactics build proofs
  the kernel checks).

  Dependencies: `Spec/*` imports only `Spec/*`, except `Spec/Theorems`, which
  imports the proofs it composes. `Notation` sits between `Spec` and `Checker`
  (the typing rules use it); `Checker/*` imports no proofs. -/
