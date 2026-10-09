import Lean

open Lean List

abbrev Var := Name

/-!
  # Refinement variables KVars

  κ of shape κ(x₁, ..., xₙ)
-/
structure KVar where
  name       : Name       -- κ
  params     : List Name  -- x₁, ..., xₙ (canonical param names)
  paramTypes : List Expr  -- types of each param (e.g. [Int, Int] or [BitVec 32])
  mvarId     : MVarId     -- actual FVarId from peeling ∃
deriving BEq, Hashable, Repr, Inhabited

instance : Hashable KVar where
  hash k := hash k.name

/-!
  # Assignment set of solutions

    `Assignment` models a solution `σ` mapping κ-variables to predicates.
  Each entry is `(κ, (params, body))` where `body` is the predicate
  solution with free variables from `params`.
-/
abbrev Assignment := List (KVar × (List Var × Expr))
