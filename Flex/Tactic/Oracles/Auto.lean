import Auto.Tactic

open Lean Elab Tactic Auto

/-- lean-auto's trusted SMT mode, scoped to this tactic invocation. Solver
    selection and timeout use `auto.smt.solver.name` and `auto.smt.timeout`.
    Accepts auto's hypothesis and definition hints, e.g. `[*] d[fib]`.

    Use `fix (synth := flex_auto)` to prefer it during candidate checking,
    or `fix (oracle := flex_auto)` as a Lean-first fallback for all phases.
    Successful SMT calls use lean-auto's `autoSMTSorry` axiom; a separate proof
    oracle rebuilds the certificate without those synthesis proof terms. -/
macro "flex_auto" hs:hints us:uord* : tactic =>
  `(tactic| set_option auto.smt true in
    set_option auto.smt.trust true in
      auto $hs:hints $[$us:uord]*)
