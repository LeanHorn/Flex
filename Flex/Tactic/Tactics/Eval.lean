import Flex.Tactic.Tactics.ZapWith

-- Keep alias names and timing labels stable for scripts/run_rq3.py.
macro "fusion_grind" : tactic => `(tactic| zap_with (grind) "fusion_grind")

macro "fusion_aesop" : tactic => `(tactic| zap_with (aesop) "fusion_aesop")

/-- A-test: one acyclic κ, leaf closed by grind. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  fusion_grind
  all_goals first | rfl | grind

/-- A-test: one acyclic κ, leaf closed by aesop. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  fusion_aesop
  all_goals first | rfl | grind
