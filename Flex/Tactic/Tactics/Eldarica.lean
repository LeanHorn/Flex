import Flex.Tactic.Tactics.Spacer

open Lean Elab Tactic

register_option flex.eldarica.executable : String := {
  defValue := "eld"
  descr := "Eldarica executable used by the eldarica tactic."
}

/-- Synthesize with Eldarica, report invariants, and certify heads with grind. -/
elab "eldarica" : tactic => do
  Flex.CHC.solverTactic {
    backend := .eldarica
    executable := some (flex.eldarica.executable.get (← getOptions)) }
