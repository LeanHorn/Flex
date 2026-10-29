import Flex.Tactic.Tactics.Spacer

open Lean Elab Tactic

register_option flex.eldarica.executable : String := {
  defValue := "eld"
  descr := "Eldarica executable used by the eldarica tactic."
}

/-- Synthesize and certify invariants; optional lemmas and equations supply proved facts. -/
syntax "eldarica" (atomic("(" &"lemmas" ":=") "[" ident,* "]" ")")?
  (atomic("(" &"defs" ":=") "[" ident,* "]" ")")? : tactic

elab_rules : tactic
  | `(tactic| eldarica $[(lemmas := [$lemmas:ident,*])]? $[(defs := [$defs:ident,*])]?) => do
    let resolve (names : Array (TSyntax `ident)) : TacticM (Array Name) :=
      names.mapM fun name => do return ← realizeGlobalConstNoOverloadWithInfo name
    let lemmas ← resolve (lemmas.map (·.getElems) |>.getD #[])
    let defs ← resolve (defs.map (·.getElems) |>.getD #[])
    Flex.CHC.solverTactic {
      backend := .eldarica
      executable := some (flex.eldarica.executable.get (← getOptions)) } { lemmas, defs }
