import Flex.Tactic.Tactics.ZapWith

-- RQ3 variants use proof search at predicate heads.
macro "zap_grind" : tactic => `(tactic| zap_with (grind) "zap_grind")

macro "zap_aesop" : tactic => `(tactic| zap_with (aesop) "zap_aesop")

/-- A-test: one acyclic κ, leaf closed by grind. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  zap_grind
  all_goals first | rfl | grind

/-- A-test: one acyclic κ, leaf closed by aesop. -/
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  zap_aesop
  all_goals first | rfl | grind
