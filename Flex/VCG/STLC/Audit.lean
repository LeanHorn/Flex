import Flex.VCG.STLC.Safety
import Flex.VCG.STLC.Examples
import Flex.VCG.STLC.DataExamples
import Flex.VCG.STLC.OrdExamples
import Flex.VCG.STLC.MeasureExamples

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

/-- info: 'data_sumList_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms data_sumList_client

/-- info: 'data_sumList_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms data_sumList_safe

/-- info: 'data_map_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms data_map_client

/-- info: 'data_mkOrd_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms data_mkOrd_bad

/-- info: 'data_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms data_range

/-- info: 'data_filterGe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms data_filterGe

/-- info: 'data_append_client' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms data_append_client

/-- info: 'data_pred_contra_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms data_pred_contra_bad

/-- info: 'ord_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_max

/-- info: 'ord_okList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_okList

/-- info: 'ord_badList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_badList

/-- info: 'ord_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_insert

/-- info: 'ord_insert_mono_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_insert_mono_bad

/-- info: 'ord_isort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_isort

/-- info: 'ord_headsOrdered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_headsOrdered

/-- info: 'ord_sortClient_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ord_sortClient_safe

/-- info: 'meas_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_append

/-- info: 'meas_two_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_two_bad

/-- info: 'meas_infer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_infer

/-- info: 'meas_headClient_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_headClient_safe

/-- info: 'meas_consPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_consPos

/-- info: 'meas_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_node

/-- info: 'meas_sumIList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_sumIList

/-- info: 'meas_mirror' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_mirror

/-- info: 'meas_filterGe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_filterGe

/-- info: 'meas_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_insert

/-- info: 'meas_mirrorHeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_mirrorHeight

/-- info: 'meas_heightLeSize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_heightLeSize

/-- info: 'meas_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_count

/-- info: 'meas_oneTrue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms meas_oneTrue
