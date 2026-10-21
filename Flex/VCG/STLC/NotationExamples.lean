import Flex.VCG.STLC.Examples
import Flex.VCG.STLC.Notation

/-! # Examples restated using `<| ... |>` notation

  Same programs as `Examples.lean`, but written with the surface syntax from
  `Notation.lean` instead of raw locally-nameless constructor application.
-/

open STLC

/-! ## κ-example with `ty_k`: `let z = 99 in (λx. x : IntK k → IntK k) z ⇐ Pos` -/

example :
    ∃ κ : KEnv,
      topVC κ []
      <| let z = 99 in ((λ x, x) : (Int{v : κ v} -> Int{v : κ v})) z |>
      <ty| Int{ v : 1 ≤ v } |> := by
  simp [topVC]
  intro_kenv
  simp [mkKEnv, liftKPred]
  solve_fixpoint

/-! ## κ-example with `ty_xk`: same shape, output type `IntN 99` -/

example :
    ∃ κ : KEnv,
      topVC κ []
      <| let z = 99 in ((λ x, x) : (x : Int {v : ⊤}) -> Int {v : κ x v}) z |>
      <ty| Int{ v : v = 99 } |> := by
  simp [topVC]
  intro_kenv
  simp [mkKEnv, List.lookup, liftKPred]
  solve_fixpoint

/-! ## Example 3: `let z = 5 in z ⇐ Pos` -/

example (κ : KEnv) : topVC κ [] (<| let z = 5 in z |>) Pos := by
  simp [topVC, check, synth, sub, implyBindCstr, Pos, prim, self,
        Refinement.interp, Formula.interp, Term.interp, REnv.get,
        Exp.openVar]
