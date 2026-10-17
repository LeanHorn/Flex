import Smt

open Lean Elab Tactic Smt.Tactic

/-- lean-smt/cvc5 with proof reconstruction and a two-second solver timeout.
    Import this module and use `fix (proof := flex_smt [*])` to prefer it for
    certificate leaves and residual goals. Definition hints are supported,
    e.g. `flex_smt [*, fib]`. For other settings use `smt` directly. -/
macro "flex_smt" hs:smtHints : tactic =>
  `(tactic| smt (timeout := some 2) $hs:smtHints)
