import Flex.Tactic.Tactics.ZapWith

/-! ## `fusion_grind` — RQ3 eval alias

  `zap_with (grind)` with the `[phase]` label `fusion_grind`. The name and the label
  are parsed by `scripts/run_rq3.py`; do not rename either. -/
macro "fusion_grind" : tactic => `(tactic| zap_with (grind) "fusion_grind")

/-- A-test: one acyclic κ, leaf closed by grind. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  fusion_grind
  all_goals first | rfl | grind
