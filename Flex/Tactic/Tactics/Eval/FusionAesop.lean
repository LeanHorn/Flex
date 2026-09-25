import Flex.Tactic.Tactics.ZapWith

/-! ## `fusion_aesop` — RQ3 eval alias

  `zap_with (aesop)` with the `[phase]` label `fusion_aesop`. The name and the label
  are parsed by `scripts/run_rq3.py`; do not rename either. -/
macro "fusion_aesop" : tactic => `(tactic| zap_with (aesop) "fusion_aesop")

/-- A-test: one acyclic κ, leaf closed by aesop. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  fusion_aesop
  all_goals first | rfl | grind
