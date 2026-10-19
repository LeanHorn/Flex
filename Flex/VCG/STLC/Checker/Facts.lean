import Flex.VCG.STLC.Spec.Syntax

open STLC

/-! # Measure facts

  What the typing rules record about measures: at a constructor applied to
  variables (`ctorRefine`), at a match on a variable (`altTy`, on the payload's
  terminal unit), and when a datatype variable is used (`measEqs`). Measure
  bodies are translated into refinement terms (`MBody.toTerm`). -/

namespace STLC

/-- A measure body as a refinement term, given terms for the (`Int` and
    `Bool`) fields and for the fields' measures. -/
def MBody.toTerm (fld : Nat → Term .int) (fldB : Nat → Term .bool) (msr : String → Nat → Term .int) :
    MBody → Term .int
  | .const n  => .const .int n
  | .field i  => fld i
  | .meas m i => msr m i
  | .add a b  => .add (a.toTerm fld fldB msr) (b.toTerm fld fldB msr)
  | .iteLe a b t e =>
      .ite .int (.leqI (a.toTerm fld fldB msr) (b.toTerm fld fldB msr))
        (t.toTerm fld fldB msr) (e.toTerm fld fldB msr)
  | .iteB i t e => .ite .int (fldB i) (t.toTerm fld fldB msr) (e.toTerm fld fldB msr)

/-- Conjoin `r` into the refinement of the terminal unit of a payload type with
    `n` fields. -/
def Ty.strengthenUnit : Nat → Ty → Refinement → Ty
  | 0,     .refine b r', r => .refine b (.conj r' r)
  | n + 1, .prod s t,    r => .prod s (Ty.strengthenUnit n t r)
  | _,     t,            _ => t

/-- The measures of constructor `j`, with their bodies for it. -/
def DataDecl.ctorMeasures (d : DataDecl) (j : Nat) : List (String × MBody) :=
  d.measures.filterMap fun mb => (mb.2[j]?).map fun b => (mb.1, b)

/-- The measures of constructor `j` of `C`, with their bodies for it. -/
def DEnv.ctorMeasures (de : DEnv) (C : String) (j : Nat) : List (String × MBody) :=
  ((de.decl? C).map fun d => d.ctorMeasures j).getD []

/-- A conjunction of formulas. -/
def Formula.conjAll : List Formula → Formula
  | []      => .tt
  | φ :: φs => .and φ (Formula.conjAll φs)

/-- What constructing `C j` from the fields `as` reveals about the result ν
    (`BVar 0`): each measure equals its body for this constructor. -/
def DEnv.ctorFacts (de : DEnv) (C : String) (j : Nat) (as : List EVar) : Refinement :=
  .fmla (Formula.conjAll ((de.ctorMeasures C j).map fun mb =>
    .eq .int (.mbvar mb.1 0)
      (mb.2.toTerm (fun i => if i < as.length then .fvar .int (as.getD i "") else .const .int 0)
        (fun i => if i < as.length then .fvar .bool (as.getD i "") else .const .bool false)
        (fun m' i => if i < as.length then .mfvar m' (as.getD i "") else .const .int 0))))

/-- What matching `x` against `C j` (with `n` fields) reveals: each measure of
    `x` equals its body for this constructor. Read at the payload's terminal
    unit, where field `i` is `BVar (n - i)`. -/
def DEnv.caseFacts (de : DEnv) (C : String) (j n : Nat) (x : EVar) : Refinement :=
  .fmla (Formula.conjAll ((de.ctorMeasures C j).map fun mb =>
    .eq .int (.mfvar mb.1 x)
      (mb.2.toTerm (fun i => .ibvar (n - i)) (fun i => .bbvar (n - i))
        (fun m' i => .mbvar m' (n - i)))))

/-- The names of the measures of `C`. -/
def DEnv.measNames (de : DEnv) (C : String) : List String :=
  ((de.decl? C).map fun d => d.measures.map Prod.fst).getD []

/-- Selfification at a datatype (which has no equality in the logic): every
    measure of ν equals that measure of `x`. -/
def DEnv.measEqs (de : DEnv) (C : String) (x : EVar) : Refinement :=
  .fmla (Formula.conjAll ((de.measNames C).map fun m => .eq .int (.mbvar m 0) (.mfvar m x)))

/-- The scrutinee of a `case`, when it is a variable. -/
def Exp.var? : Exp → Option EVar
  | .fvar x => some x
  | _       => none

/-- The fields of a payload of a constructor with `n` fields, written out as
    variables: `(x₀, (x₁, … (xₙ₋₁, u)))`. -/
def Exp.tupleVarsN : Nat → Exp → Option (List EVar)
  | 0,     _                 => some []
  | n + 1, .pair (.fvar x) e => (Exp.tupleVarsN n e).map (x :: ·)
  | _,     _                 => none

/-- The refinement a constructor application synthesizes: the measure facts,
    when its fields are given as variables. -/
def DEnv.ctorRefine (de : DEnv) (C : String) (j : Nat) (e : Exp) : Refinement :=
  match e.tupleVarsN (de.nFields C j) with
  | some as => de.ctorFacts C j as
  | none    => .fmla .tt

/-- The type an alternative of a match on `C` binds its payload at (`tz`, the
    payload at the scrutinee's type arguments): when the scrutinee is a
    variable `x`, the terminal unit records the measure facts about `x`. -/
def DEnv.altTy (de : DEnv) (C : String) (j : Nat) (x? : Option EVar) (tz : Ty) : Ty :=
  match x? with
  | some x => tz.strengthenUnit (de.nFields C j) (de.caseFacts C j (de.nFields C j) x)
  | none   => tz

end STLC
