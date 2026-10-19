import Flex.VCG.STLC.Tactics.MakeHornUnderK
import Flex.VCG.STLC.Checker.VCGen

open STLC

/-! # Shared setup for the examples

  The definitions the verification-condition generator unfolds (as global simp
  lemmas), and `generate`: compute the verification condition of
  `∃ κ, Check …`, then reify the κ's into per-κ unknowns for Flex. -/

attribute [simp] check synth sub EVar.fresh implyBindCstr prim self Refinement.interp Formula.interp TEnv.dom

attribute [simp] Cstr.interp Cstr.triv Refinement.openBVar Formula.openBVar Term.openBVar REnv.update REnv.write

attribute [simp] Term.interp REnv.get Exp.openVar Ty.openVar Exp.fv Refinement.fv Formula.fv Term.fv Ty.fv

attribute [simp] Refinement.openBVar Formula.openBVar Term.openBVar String.length EVar.maxLen

attribute [simp] List.lookup TEnv.tyFv

attribute [simp] DataDecl.ctors Ty.tuple DEnv.ctorRefine DEnv.nFields DEnv.fields? Exp.tupleVarsN
  DEnv.ctorFacts DEnv.ctorMeasures DataDecl.ctorMeasures DEnv.altTy Exp.var? Ty.strengthenUnit
  DEnv.caseFacts Formula.conjAll MBody.toTerm DEnv.measEqs DEnv.measNames

macro "generate" : tactic => `(tactic| (vc_generate ; all_goals vc_reify))
