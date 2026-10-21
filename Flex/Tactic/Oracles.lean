import Auto.Tactic
import Smt

open Lean Elab Tactic Auto Smt.Tactic

/-- Run lean-auto's SMT backend using its trusted `autoSMTSorry` axiom. -/
macro "flex_auto" hs:hints us:uord* : tactic =>
  `(tactic|
    set_option auto.smt true        in
    set_option auto.smt.trust true  in
      auto $hs:hints $[$us:uord]*)

/-- Run lean-smt with proof reconstruction and a two-second solver timeout. -/
macro "flex_smt" hs:smtHints : tactic =>
  `(tactic| smt (timeout := some 10) $hs:smtHints)
