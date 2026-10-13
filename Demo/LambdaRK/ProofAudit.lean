import Flex.VCG.LambdaRK.DraftTheorems
import Demo.LambdaRK.Foundation
import Demo.LambdaRKRecursionChecks
import Flex.VCG.LambdaRK.SyntaxEqualityLemmas

/-!
# Foundation and recursion proof audit

This regression follows each completed PR7/PR8 theorem's transitive dependencies.
It rejects `sorryAx`, native evaluation axioms, and any other axiom beyond Lean's
standard propositional extensionality, choice, and quotient soundness.

Importing `DraftTheorems` deliberately places the unfinished full-language
statements in the same environment. The completed core and recursion results
must remain independent of those later obligations. The actual solver-generated
map proof has its own audit in `SolvedMap`; this file needs no external solver.
-/
namespace LambdaRK.ProofAudit

open Lean Meta Elab

run_elab do
  let completed : List Name := [
    -- Capture avoidance and polymorphic/datatype substitution.
    ``Draft.freshenBinders_freeVars,
    ``Draft.freshenBinders_avoids,
    ``Draft.freshenBinders_denote,
    ``Draft.shiftTypes_scoped,
    ``Draft.substType_scoped,
    ``Draft.instantiateParams_scoped,
    ``Draft.type_environment_congr,
    ``Draft.logical_substitution,
    ``Draft.atom_substitution,
    ``Draft.type_term_substitution,
    ``Draft.type_shift_denote,
    ``Draft.type_substitution,
    ``Draft.instantiateParams_denote,
    -- Formation certificates and runtime-environment transport.
    ``Ty.scopeCheck_eq_true,
    ``Signature.validate_modelReady,
    ``Draft.wfTy_inScope,
    ``Draft.scoped_add,
    ``Draft.assumptionsScoped_add,
    ``Draft.realizes_add,
    ``Draft.scoped_underType,
    ``Draft.assumptionsScoped_underType,
    ``Draft.realizes_underType,
    -- Actual datatype interpretation, including higher-order recursive fields.
    ``Signature.datatypeModel_adequate,
    ``Draft.datatype_model_exists,
    ``FoundationChecks.higherOrderModel,
    -- Core theorem and independently proved structural-recursion cases.
    ``Draft.fundamental_core,
    ``Draft.fundamental_core_closed,
    ``Draft.structural_order_wellFounded,
    ``Apply.recursiveClosure_total,
    ``Context.scoped_recursiveBody,
    ``Context.realizes_recursiveBody,
    ``semTyped_structRec_of_scope,
    ``recursive_call_case,
    ``Draft.semTyped_structRec,
    ``Draft.semTyped_recur,
    ``RecursionChecks.delayed_recursion_evaluates,
    -- Executable comparisons used by the checker match syntactic equality.
    ``LTerm.equal_eq_true,
    ``Ty.equal_eq_true,
    ``instLawfulBEqFormula,
    ``instLawfulBEqAtom
  ]
  for theoremName in completed do
    let axioms ← collectAxioms theoremName
    let unexpected := axioms.filter fun name =>
      name != ``propext && name != ``Classical.choice && name != ``Quot.sound
    unless unexpected.isEmpty do
      throwError "completed LambdaRK theorem contains unapproved axioms: {theoremName}: {unexpected}"
  logInfo m!"LambdaRK proof audit: {completed.length} completed declarations use only standard Lean axioms"

end LambdaRK.ProofAudit
