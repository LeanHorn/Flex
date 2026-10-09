import Lean
import Aesop

import Flex.Core
import Flex.Fusion
import Flex.Zap
import Flex.PA.Check
import Flex.Tactic.Utils
import Flex.Tactic.Tactics.Fusion

open Lean Meta Elab Tactic

/-! ## `zap_with` — `zap` with a tactic at the κ-head leaves

  Same pipeline as `zap` (`zapImpl`). The only difference is the
  head-acyclic-κ leaf: instead of `nav` building a proof term, the
  σ̂-instantiated clause is handed to `tac`. No fallback: if `tac` fails, the
  whole tactic fails.

  `zap_with (tac) "label"` — the optional string is the `benchPhase` label
  (default `zap_with`). The eval aliases in `Tactics/Eval/` set it. -/

/-- Leaf handler: prove the clause by running `tac` in the ambient context. -/
def searchLeaf (tac : TSyntax `tactic) (label : String) : LeafHandler :=
  fun _ lamBody _ _ _ => do
    match ← proveLeafWith tac lamBody with
    | some pf => return pf
    | none    => throwError "{label}: search tactic failed on κ-head clause:{indentExpr lamBody}"

def searchStrategy (tac : TSyntax `tactic) (label : String) : LeafStrategy :=
  { label, mkHandler := fun _ _ => searchLeaf tac label }

syntax "zap_with" "(" tactic ")" (str)? : tactic

elab_rules : tactic
  | `(tactic| zap_with ($tac) $[$lbl:str]?) =>
      zapImpl (searchStrategy tac ((lbl.map (·.getString)).getD "zap_with"))

-- Tests (same A/B/D constraints as `zap`'s tests in Fusion.lean)
example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  zap_with (grind)
  all_goals first | rfl | grind

example : ∃ κ : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν x)
    ∧ (∀ y : Int, κ y x →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν) := by
  zap_with (aesop)
  all_goals first | rfl | grind

example : ∃ κ1 : Int → Int → Prop, ∃ κ2 : Int → Int → Prop,
    ∀ x : Int, 0 ≤ x →
      (∀ ν : Int, ν = x + 1 → κ1 ν x)
    ∧ (∀ ν : Int, ν = x - 1 → κ2 ν x)
    ∧ (∀ a : Int, κ1 a x → 0 ≤ a)
    ∧ (∀ b : Int, κ2 b x →
        ∀ ν : Int, ν = b + 1 → 0 ≤ ν) := by
  zap_with (grind)
  all_goals first | rfl | grind

example : ∃ κ1 : Int → Prop, ∃ κ2 : Int → Prop,
      (∀ y : Int, κ1 y → κ1 (y + 1))
    ∧ (∀ ν : Int, ν = 0 → κ1 ν)
    ∧ (∀ ν : Int, ν = 0 → κ2 ν)
    ∧ (∀ z : Int, κ2 z → 0 ≤ z) := by
  zap_with (grind)
  exact ⟨fun y => 0 ≤ y, by grind⟩
