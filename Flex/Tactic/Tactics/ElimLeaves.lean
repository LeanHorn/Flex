import Lean

open Lean Elab Tactic Meta in
private partial def elimLeaves : TacticM Unit := do
  let goals ← getGoals
  match goals with
  | [] => return ()
  | g :: restGoals =>
    let ty ← whnfR (← g.getType)
    if ty.isForall then
      -- goal is `p → q` or `∀ x, P x`: introduce
      evalTactic (← `(tactic| intro _))
      elimLeaves
    else if ty.isAppOfArity ``And 2 then
      -- goal is `p ∧ q`: split into two subgoals
      evalTactic (← `(tactic| and_intros))
      elimLeaves
    else
      let leafOk ←
        try evalTactic (← `(tactic| grind)); pure true catch _ =>
        try evalTactic (← `(tactic| rfl));   pure true catch _ => pure false
      if leafOk then
        elimLeaves
      else
        setGoals restGoals
        elimLeaves
        let remaining ← getGoals
        setGoals (g :: remaining)

/--
  Decomposes `p → q` and `p ∧ q`
  recursively via `intro` and `and_intros`, and
  applies `grind` with `rfl` at leaf goals.
-/
elab "elim_leaves" : tactic => elimLeaves
