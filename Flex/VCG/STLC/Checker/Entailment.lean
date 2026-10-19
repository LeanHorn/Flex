import Flex.VCG.STLC.Checker.WellFormed

open STLC


/-! ## Entailment

  Refinements / formulas / models are all parameterized by a κ-assignment
  `κ : KEnv` (the interpretation of uninterpreted predicate symbols). The
  user typically writes `∃ κ : KEnv, Entail κ ...` and lets the solver pick.

  `Entail κ Γ c` (with `c : REnv → Prop`) is the entailment used by
  VCGen-produced `Constraint`s. Refinement subtyping is expressed semantically
  (see `Subtyp.refine` in `Checker/Typing.lean`), so no `Formula`-form entailment is
  needed now that κ lives at the `Refinement` level.
-/

/-- The refined hypothesis a binding of type `t` contributes to a model, if
    any: `x : {ν:b | r}` contributes `r` at sort `b`. Function and polymorphic
    types contribute nothing, and neither do ⋆-kinded type variables (they are
    refined only with `true`, and may hold closures, which have no base sort)
    or unopened (`tbvar`) type variables. -/
def STLC.Ty.hyp? : Ty → Option (Base × Refinement)
  | .refine (.tfvar (_, .star)) _ => none
  -- an unopened type variable never occurs in a well-formed context
  | .refine (.tbvar _) _          => none
  | .refine b r                   => some (b, r)
  | .arrow _ _                    => none
  | .forall _ _                   => none
  | .prod _ _                     => none
  | .data _ _ _ _                 => none

/-- The hypothesis a datatype binding contributes: its refinement, which reads
    the bound value only through measures (no sort, so no `HasBase`). -/
def STLC.Ty.dhyp? : Ty → Option Refinement
  | .data _ _ _ r => some r
  | _             => none

/-- A model for Γ under κ-assignment: every binding with a refined hypothesis
    stores a value of the binding's sort (`HasBase`) satisfying it. The
    `HasBase` conjunct is what lets `Entail.ext` round-trip a refined slot
    through `b.interp`. -/
def ModelsEnv (κ : KEnv) : REnv → TEnv → Prop
  | _, []           => True
  | γ, (x, t) :: Γ  =>
      (match t.hyp? with
       | some (b, r) => REnv.HasBase γ x b ∧ Refinement.interp κ r (γ.push (γ.lookup x))
       | none        =>
         match t.dhyp? with
         | some r => Refinement.interp κ r (γ.push (γ.lookup x))
         | none   => True)
      ∧ ModelsEnv κ γ Γ

/-- `κ; Γ ⊢ c`: `c` (as a Lean predicate over `REnv`) holds in every model of
    Γ under κ. VCGen-produced constraints use this. -/
@[simp]
def Entail (κ : KEnv) (Γ : TEnv) (c : REnv → Prop) : Prop :=
  ∀ γ, ModelsEnv κ γ Γ → c γ
