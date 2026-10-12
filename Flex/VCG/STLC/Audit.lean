import Flex.VCG.STLC.Safety
import Flex.VCG.STLC.Examples

open STLC

/-! # Axiom audit

  Fails the build if any headline result depends on anything beyond Lean's
  three standard axioms — in particular `sorryAx` (a `sorry`, anywhere in the
  dependency cone), compiler-trusting axioms from `native_decide`
  (`Lean.ofReduceBool` / `…._native…`), or user-declared `axiom`s. -/

/-- info: 'vcgen_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vcgen_safety

/-- info: 'vcgen_no_stuck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vcgen_no_stuck

/-- info: 'vcgen_partial_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms vcgen_partial_correct

/-- info: 'type_safety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms type_safety

/-- info: 'hastype_fundamental' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hastype_fundamental

/-- info: 'subtyp_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms subtyp_sound

/-- info: 'topVC_decl_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms topVC_decl_sound

/-- info: 'check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms check_sound

/-- info: 'STLC.Eval.det' depends on axioms: [propext] -/
#guard_msgs in #print axioms Eval.det

/-- info: 'loopMain_vc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopMain_vc

/-- info: 'sum_infer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sum_infer

/-- info: 'poly_id_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms poly_id_client

/-- info: 'poly_choose_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms poly_choose_client

/-- info: 'poly_impredicative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms poly_impredicative

/-- info: 'poly_iter_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms poly_iter_client

/-- info: 'poly_nest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms poly_nest
