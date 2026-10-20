import Flex.VCG.STLC.Examples.Data
import Flex.VCG.STLC.Examples.Ord
import Flex.VCG.STLC.Examples.Measure

open STLC

/-! # Well-formedness tests

  The bound-variable conditions `Ty.WFBVars`, `Exp.WFBVars` and `TEnv.WFBVars`
  are decidable (`Proofs/WFDecide.lean`), and so is `DEnv.wfB`: `decide`
  proves them for well-formed concrete inputs, and refutes them for ill-formed
  ones. -/

namespace STLC.Tests.WellFormed

/-! ## Types -/

example : Ty.WFBVars Pos := by decide
example : Ty.WFBVars sumTy := by decide
example : Ty.WFBVars mapTy := by decide
example : Ty.WFBVars headsTy := by decide

/-- An arrow binder of base sort may be mentioned later… -/
example : Ty.WFBVars <ty| (x : Int) -> (y : Int{ν : x ≤ ν}) -> Int{ν : x ≤ ν ∧ y ≤ ν} |> := by
  decide

/-- …at its own sort only. -/
example : ¬ Ty.WFBVars
    (.arrow (.refine .int (.fmla .tt)) (.refine .bool (.fmla (.eq .bool (.bvar .bool 1) (.bvar .bool 0))))) := by
  decide

/-- ν has the sort of the refined base. -/
example : ¬ Ty.WFBVars (.refine .int (.fmla (.eq .bool (.bvar .bool 0) (.const .bool true)))) := by
  decide

/-- A function-typed binder has no sort, so refinements cannot mention it. -/
example : ¬ Ty.WFBVars
    (.arrow (.arrow TT TT) (.refine .int (.fmla (.eq .int (.bvar .int 0) (.bvar .int 1))))) := by
  decide

/-- A dangling index. -/
example : ¬ Ty.WFBVars (.refine .int (.fmla (.eq .int (.bvar .int 0) (.bvar .int 1)))) := by decide

/-- Quantifiers bind indices of their own. -/
example : Ty.WFBVars <ty| Int{ν : ∃ y : Int, ν ≤ y ∧ y ≤ 0} |> := by decide
/-- Under a quantifier, ν is index `1`, at its own sort. -/
example : ¬ Ty.WFBVars
    (.refine .int (.fmla (.ex .bool (.eq .bool (.bvar .bool 0) (.bvar .bool 1))))) := by decide

/-- A datatype's ν has no sort: it is observed through measures only. -/
example : Ty.WFBVars <ty| list[Int]{ν : len ν = 2} |> := by decide
example : ¬ Ty.WFBVars (.data "list" 1 (fun _ => TT) (.fmla (.eq .int (.bvar .int 0) (.const .int 0)))) := by
  decide

/-- κ-applications are checked too. -/
example : Ty.WFBVars sumTyK := by decide
example : ¬ Ty.WFBVars (.refine .int (.kapp "k" [⟨.bool, .bvar .bool 0⟩])) := by decide

/-! ## Programs (their annotations) -/

example : Exp.WFBVars loopMain := by decide
example : Exp.WFBVars sumClientE := by decide
example : Exp.WFBVars headClientE := by decide
example : Exp.WFBVars sortClientE := by decide
example : Exp.WFBVars nestE := by decide

/-- An ill-formed annotation deep inside a `match` alternative is found. -/
example : ¬ Exp.WFBVars
    <| λ o, match o with
       | None => 0
       | Some x => (x : ⌜Ty.refine .int (.fmla (.eq .bool (.bvar .bool 0) (.const .bool true)))⌝) |> := by
  decide

/-! ## Contexts -/

example : TEnv.WFBVars [("x", Pos), ("f", sumTy)] := by decide
example : ¬ TEnv.WFBVars [("x", Pos), ("y", .refine .int (.fmla (.eq .int (.bvar .int 3) (.bvar .int 0))))] := by
  decide

/-! ## Declarations -/

example : optionEnv.wfB = true := by decide
example : listEnv.wfB = true := by decide
example : lenEnv.wfB = true := by decide

/-- A payload with a free variable. -/
def freeVarDecl : DataDecl where
  params := []
  ctorFields := [("B", [.refine .int (.fmla (.eq .int (.bvar .int 0) (.fvar .int "z")))])]
example : DEnv.wfB [("bad", freeVarDecl)] = false := by decide

/-- A measure reading a field that does not exist. -/
def noFieldDecl : DataDecl where
  params := []
  ctorFields := [("B", [TT])]
  measures := [("m", [.field 1])]
example : DEnv.wfB [("bad", noFieldDecl)] = false := by decide

/-- A measure reading a `Bool` field as an integer. -/
def boolFieldDecl : DataDecl where
  params := []
  ctorFields := [("B", [.refine .bool (.fmla .tt)])]
  measures := [("m", [.field 0])]
example : DEnv.wfB [("bad", boolFieldDecl)] = false := by decide

/-- Two measures with the same name. -/
def dupMeasDecl : DataDecl where
  params := []
  ctorFields := [("B", [TT])]
  measures := [("m", [.const 0]), ("m", [.const 1])]
example : DEnv.wfB [("bad", dupMeasDecl)] = false := by decide

/-- A covariant parameter in a contravariant position. -/
def coDecl : DataDecl where
  params := [.star]
  ctorFields := [("B", [.arrow (.refine (.tbvar 0) (.fmla .tt)) TT])]
  variances := [.co]
example : DEnv.wfB [("bad", coDecl)] = false := by decide
example : DEnv.wfB [("ok", { coDecl with variances := [.contra] })] = true := by decide

/-! ## End to end, with every side condition by `decide` -/

/-- `sum [1, 2]` is safe and returns a natural number (cf. `data_sumList_safe`). -/
example (n : Nat) :
    ∃ o, Run n sumClientE o ∧ ∀ v m, o = .val v m → ∃ i : Int, v = .iconst i ∧ 0 ≤ i := by
  obtain ⟨κ, h⟩ := data_sumList_client
  have hs := check_safety ?_ ?_ ?_ h n <;> try decide
  obtain ⟨o, hrun, hres⟩ := hs
  refine ⟨o, hrun, fun v m ho => ?_⟩
  have := hres v m ho
  simp only [TyDenote, BaseDen] at this
  obtain ⟨⟨i, rfl⟩, hi⟩ := this
  exact ⟨i, rfl, by simpa [Refinement.interp, Formula.interp, Term.interp] using hi⟩

/-- Sorting `[3, 1, 2]` returns `true` if it returns (cf. `ord_sortClient_safe`). -/
example {n m : Nat} {v : Val} (h : Run n sortClientE (.val v m)) : v = .bconst true := by
  have hp := vcgen_partial_correct (κ := fun _ _ => True) ?_ ?_ ?_ (ord_sortClient_vc _) h
    <;> try decide
  obtain ⟨⟨c, rfl⟩, hc⟩ := hp
  simpa [Refinement.interp, Formula.interp, Term.interp, REnv.getBV] using hc

end STLC.Tests.WellFormed
