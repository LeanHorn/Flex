import Flex.VCG.STLC.Spec.Syntax

open STLC

/-! # The refinement logic's meaning

  Runtime environments (`REnv`: a name map, a de Bruijn stack for ν and
  quantified variables, and a `SortEnv` giving type-variable sorts and measure
  interpretations), and the interpretation of terms, formulas and refinements
  in them. A refinement's κ-applications are read through a `KEnv`. Measures are
  defined here as the structurally recursive functions their bodies describe
  (`DEnv.measEval`). -/

namespace STLC



/-- A sort assignment: the base each type variable stands for (the bound ones
    by de Bruijn index, the free ones by name) — and the interpretation of the
    measures (`meas m v`: the value of measure `m` on `v`). Verification
    conditions hold for *every* assignment, so in them measures are
    uninterpreted; the semantic model fixes them to the measures' definitions. -/
structure SortEnv where
  bv : List BSort := []
  fv : TVar → BSort := fun _ => .int
  meas : String → Val → Int := fun _ _ => 0

/-- The base a sort stands for under `σ`. -/
@[simp, reducible] def Base.resolve (σ : SortEnv) : Base → BSort
  | .int     => .int
  | .bool    => .bool
  | .tbvar j => σ.bv.getD j .int
  | .tfvar a => σ.fv a

/-- The carrier of sort `b` under `σ`. -/
@[simp, reducible] def Base.sem (σ : SortEnv) (b : Base) : Type := (b.resolve σ).ty

/-- A literal, read at its sort. -/
@[simp, reducible] def Base.ofConst (σ : SortEnv) : (b : Base) → b.interp → b.sem σ
  | .int,     n => n
  | .bool,    c => c
  | .tbvar _, e => e.elim
  | .tfvar _, e => e.elim

/-! ## Runtime environment

  `REnv` bundles two things threaded as a single environment `γ`:

  * `map : EVar → Val` — the total name map for *free* variables. The
    base-indexed `get`/`update` are thin views over the lossless Val-level
    `lookup`/`write`: `get` projects the stored `Val` down to `b.interp`
    (defaulting on a tag mismatch, never hit on a well-typed read), and
    `update` injects a `b.interp` value back into a `Val`.
  * `bv : List Val` — the de Bruijn stack for *bound* variables (ν and the
    refinement-formula quantifier binders), innermost = index 0. `Term.interp`
    resolves a `BVar k` through `bv[k]` exactly as it resolves an `fvar`
    through `map`. `push` enters a binder; `getBV` reads one. Outside of
    refinement interpretation `bv` is empty, and `write`/`update` preserve it.

  Because a single `map` cell can no longer be int- and bool-typed at once,
  "read at base `b` then write back" only round-trips when the cell actually
  holds a base-`b` value — captured by `REnv.HasBase`. -/

@[ext]
structure REnv where
  map : EVar → Val
  bv  : List Val := []
  /-- The base each type-variable sort stands for. -/
  sorts : SortEnv := {}

@[simp] def REnv.empty : REnv := { map := fun _ => .iconst 0 }

/-- Reinterpret the type-variable sorts. -/
@[simp, reducible] def REnv.withSorts (γ : REnv) (σ : SortEnv) : REnv := { γ with sorts := σ }

/-- Project a stored `Val` to a value of base `s`. The mismatch cases
    (`0`/`false`) are unreachable for well-typed reads. -/
@[simp, reducible]
def Val.proj : (s : BSort) → Val → s.ty
  | .int,  .iconst n => n
  | .bool, .bconst c => c
  | .int,  _ => 0
  | .bool, _ => false

/-- Inject a value of base `s` into `Val`. -/
@[simp, reducible]
def Val.inj : (s : BSort) → s.ty → Val
  | .int,  n => .iconst n
  | .bool, c => .bconst c

/-- Tag a value with its base, as a κ argument. -/
@[simp, reducible]
def Val.tag : (s : BSort) → s.ty → (Σ b : Base, b.interp)
  | .int,  n => ⟨.int, n⟩
  | .bool, c => ⟨.bool, c⟩

/-- Val-level (lossless) lookup. -/
@[simp, reducible]
def REnv.lookup (γ : REnv) (x : EVar) : Val := γ.map x

/-- Enter a binder: push value `v` as the new innermost de Bruijn slot (index 0),
    shifting the existing stack up one. The name map is untouched. -/
@[simp] def REnv.push (γ : REnv) (v : Val) : REnv := { γ with bv := v :: γ.bv }

/-- Read the `b`-typed value of the de Bruijn `BVar k` from the stack. Out of
    range (never on a well-formed read) defaults per base via `Val.proj`. -/
@[simp, reducible]
def REnv.getBV (b : Base) (γ : REnv) (k : Nat) : b.sem γ.sorts :=
  Val.proj (b.resolve γ.sorts) (γ.bv[k]?.getD (.iconst 0))

/-- Look up the `b`-typed value of variable `x` in `γ` (base-indexed view). -/
@[simp, reducible]
def REnv.get (b : Base) (γ : REnv) (x : EVar) : b.sem γ.sorts :=
  (γ.lookup x).proj (b.resolve γ.sorts)

/-! ## Measure semantics

  A measure is the structurally recursive function its bodies define, on
  runtime values: on `C j w` it is the body for `j`, read on the fields of the
  payload `w`; on anything else it is `0`. -/

/-- The fields of a payload of a constructor with `n` fields. -/
def Val.fieldsN : Nat → Val → List Val
  | n + 1, .pair a r => a :: Val.fieldsN n r
  | _,     _         => []

theorem Val.sizeOf_le_of_mem_fieldsN : ∀ {n : Nat} {w f : Val}, f ∈ w.fieldsN n → sizeOf f ≤ sizeOf w
  | n + 1, .pair a r, f, h => by
    simp only [Val.fieldsN, List.mem_cons] at h
    rcases h with rfl | h
    · simp; omega
    · have := Val.sizeOf_le_of_mem_fieldsN h
      simp; omega
  | 0, _, _, h => by simp [Val.fieldsN] at h
  | _ + 1, .iconst _, _, h | _ + 1, .bconst _, _, h | _ + 1, .clos _, _, h
  | _ + 1, .fclos _, _, h | _ + 1, .ctor _ _ _, _, h => by simp [Val.fieldsN] at h

/-- Evaluate a measure body, given the (integer and boolean) fields and their
    measures. -/
def MBody.eval (fv : Nat → Int) (fb : Nat → Bool) (fm : Nat → String → Int) : MBody → Int
  | .const n  => n
  | .field i  => fv i
  | .meas m i => fm i m
  | .add a b  => a.eval fv fb fm + b.eval fv fb fm
  | .iteLe a b t e => if a.eval fv fb fm ≤ b.eval fv fb fm then t.eval fv fb fm else e.eval fv fb fm
  | .iteB i t e => if fb i then t.eval fv fb fm else e.eval fv fb fm

/-- The value of measure `m` on `v`. -/
def DEnv.measEval (de : DEnv) (m : String) : Val → Int
  | .ctor C j w =>
    match (de.decl? C).bind fun d => d.measBody? m j with
    | some body =>
      body.eval
        (fun i => if h : i < (w.fieldsN (de.nFields C j)).length then
          Val.proj .int (w.fieldsN (de.nFields C j))[i] else 0)
        (fun i => if h : i < (w.fieldsN (de.nFields C j)).length then
          Val.proj .bool (w.fieldsN (de.nFields C j))[i] else false)
        (fun i m' => if h : i < (w.fieldsN (de.nFields C j)).length then
          DEnv.measEval de m' (w.fieldsN (de.nFields C j))[i] else 0)
    | none => 0
  | _ => 0
termination_by v => sizeOf v
decreasing_by
  have := Val.sizeOf_le_of_mem_fieldsN (List.getElem_mem h)
  simp; omega


/-- Interpret a term under the single environment `γ`. `fvar` resolves through
    the name map (`REnv.get`); `bvar` resolves through the de Bruijn stack
    (`REnv.getBV`) — the values of ν and the enclosing quantifier/arrow binders
    live there.. -/
def Term.interp (γ : REnv) : {b : Base} → Term b → b.sem γ.sorts
  | _, .const b c   => Base.ofConst γ.sorts b c
  | _, .bvar b k    => REnv.getBV b γ k
  | _, .fvar b x    => REnv.get b γ x
  | _, .add t₁ t₂   => Term.interp γ t₁ + Term.interp γ t₂
  | _, .mbvar m k   => γ.sorts.meas m (γ.bv[k]?.getD (.iconst 0))
  | _, .mfvar m x   => γ.sorts.meas m (γ.map x)
  | _, .ibvar k     => Val.proj .int (γ.bv[k]?.getD (.iconst 0))
  | _, .bbvar k     => Val.proj .bool (γ.bv[k]?.getD (.iconst 0))
  | _, .not t       => !Term.interp γ t
  | _, .and t₁ t₂   => Term.interp γ t₁ && Term.interp γ t₂
  | _, .leqI t₁ t₂  => decide (Term.interp γ t₁ ≤ Term.interp γ t₂)
  | _, .ite _ c t e => if Term.interp γ c then Term.interp γ t else Term.interp γ e

/-- Interpret a (now κ-free) formula under `γ`. Each quantifier binds `BVar 0`,
    so it `push`es its witness value as the new innermost de Bruijn slot of `γ`
    and recurses. -/
def Formula.interp (γ : REnv) : Formula → Prop
  | .tt           => True
  | .ff           => False
  | .eq _ t₁ t₂   => Term.interp γ t₁ = Term.interp γ t₂
  | .leq b t₁ t₂   => BSort.le (b.resolve γ.sorts) (Term.interp γ t₁) (Term.interp γ t₂)
  | .and φ₁ φ₂    => Formula.interp γ φ₁ ∧ Formula.interp γ φ₂
  | .or φ₁ φ₂     => Formula.interp γ φ₁ ∨ Formula.interp γ φ₂
  | .not φ        => ¬ Formula.interp γ φ
  | .imp φ₁ φ₂    => Formula.interp γ φ₁ → Formula.interp γ φ₂
  | .ex b φ       => ∃ x : b.sem γ.sorts, Formula.interp (γ.push (Val.inj (b.resolve γ.sorts) x)) φ
  | .all b φ      => ∀ x : b.sem γ.sorts, Formula.interp (γ.push (Val.inj (b.resolve γ.sorts) x)) φ

/-- Package a κ-argument: a term of sort `b` is passed as a value of the base
    `b` stands for, tagged with that base. -/
@[simp, reducible] def Base.canonArg (σ : SortEnv) (b : Base) (v : b.sem σ) : (Σ b : Base, b.interp) :=
  Val.tag (b.resolve σ) v

/-- Interpret a refinement under `γ`. This is the *only* interpretation
    that consults the κ-assignment. -/
def Refinement.interp (κ : KEnv) (r : Refinement) (γ : REnv) : Prop :=
  match r with
  | .fmla φ       => Formula.interp γ φ
  | .kapp kn args =>
      κ kn (args.map (fun a => Base.canonArg γ.sorts a.1 (Term.interp γ a.2)))
  | .conj r₁ r₂   => Refinement.interp κ r₁ γ ∧ Refinement.interp κ r₂ γ

/-- The base a `Val` carries (`none` for a closure). Mirrors `Ty.optBase`:
    a value inhabiting a refinement type `{ν:b|…}` has `optBase = some b`. -/
@[simp] def Val.optBase : Val → Option Base
  | .iconst _ => some .int
  | .bconst _ => some .bool
  | .clos _   => none
  | .fclos _  => none
  | .pair _ _ => none
  | .ctor _ _ _ => none



theorem DEnv.measEval_ctor (de : DEnv) (m : String) (C : String) (j : Nat) (w : Val) :
    de.measEval m (.ctor C j w) =
      match (de.decl? C).bind fun d => d.measBody? m j with
      | some body => body.eval
          (fun i => if h : i < (w.fieldsN (de.nFields C j)).length then
            Val.proj .int (w.fieldsN (de.nFields C j))[i] else 0)
          (fun i => if h : i < (w.fieldsN (de.nFields C j)).length then
            Val.proj .bool (w.fieldsN (de.nFields C j))[i] else false)
          (fun i m' => if h : i < (w.fieldsN (de.nFields C j)).length then
            de.measEval m' (w.fieldsN (de.nFields C j))[i] else 0)
      | none => 0 := by
  rw [DEnv.measEval]

end STLC
