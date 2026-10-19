
/-! # Syntax

  What the theorems talk about: the refinement logic (`Term`, `Formula`,
  `Refinement`), types (`Ty`), expressions (`Exp`), runtime values (`Val`), and
  datatype declarations with their measures (`DataDecl`). Everything is locally
  nameless: ν, the `Formula` quantifiers, the `Ty.arrow` binders and the
  expression binders are de Bruijn `BVar`s. Also here: opening an expression
  with a value (used by evaluation) and type erasure (`Run` evaluates the
  erasure). -/

namespace STLC

abbrev EVar := String

inductive Const where
  | int : Int → Const
  deriving Repr, DecidableEq

/-- Kinds of type variables (λ_RF): `B` variables may be refined, compared and
    instantiated only with refined base types; `star` variables are refined
    only with `true` and may be instantiated with any type. -/
inductive Kind where
  | B    : Kind
  | star : Kind
  deriving Repr, DecidableEq

/-- A free type variable: a name together with its kind. Carrying the kind on
    the name makes the kind of any type computable without a kind environment. -/
abbrev TVar := String × Kind

/-- Base sorts of the refinement logic. Type variables are sorts too: a
    locally-nameless bound one (`tbvar k`, the `k`-th enclosing `Ty.forall`)
    or a free one (`tfvar a`). -/
inductive Base where
  | int   : Base
  | bool  : Base
  | tbvar : Nat → Base
  | tfvar : TVar → Base
  deriving Repr, DecidableEq

/-! ## Sorts and their carriers

  `Int` and `Bool` are the base sorts. A `B`-kinded type variable stands for one
  of them, so a type-variable sort is interpreted *by* the base it stands for:
  a sort assignment `σ : SortEnv` (carried by the refinement environment, see
  `REnv.sorts`) resolves every sort to an `Int` or a `Bool` (`Base.resolve`),
  and a term of sort `b` denotes a value of `(b.resolve σ).ty`. So refinements
  (and verification conditions) at a type-variable sort are ordinary `Int` or
  `Bool` statements, once the sort is known. Comparison is polymorphic, like
  equality: `≤` at a sort is `≤` at the base it resolves to (`BSort.le`); on
  `Bool`, `false < true`. -/

/-- The bases a sort can resolve to. -/
inductive BSort where
  | int  : BSort
  | bool : BSort
  deriving Repr, DecidableEq

/-- The carrier of a base. -/
@[simp, reducible] def BSort.ty : BSort → Type
  | .int  => Int
  | .bool => Bool

@[simp, reducible] def BSort.toBase : BSort → Base
  | .int  => .int
  | .bool => .bool

/-- The order at a base; on `Bool` it is implication (`false < true`). -/
@[simp, reducible] def BSort.le : (s : BSort) → s.ty → s.ty → Prop
  | .int,  x, y => x ≤ y
  | .bool, x, y => x = true → y = true

instance (s : BSort) : DecidableRel (BSort.le s) := fun x y => by
  cases s <;> simp only [BSort.le] <;> infer_instance

/-- Literal constants exist at `Int` and `Bool` only (a type-variable sort has
    no literals). -/
@[simp, reducible]
def Base.interp : Base → Type
  | .int     => Int
  | .bool    => Bool
  | .tbvar _ => Empty
  | .tfvar _ => Empty

-- `REnv` (the runtime environment) is a single `EVar → Val` map; it is defined
-- *after* `Val` below, since its operations mention `Val`.

/-! ## Deep-embedded refinement language

  The refinement-side DSL is a first-order language over `REnv` slots plus the
  distinguished value ν. Everything binder-shaped is *locally nameless*: ν, the
  `Formula` quantifiers, and the enclosing `Ty.arrow` binders are all de Bruijn
  `BVar`s sharing one index space (innermost = 0). This keeps the whole
  refinement layer capture-free with no reserved names.
-/

/-- Base-indexed first-order terms over `REnv` slots ∪ {ν} ∪ Ty-bound vars.

    `Term.bvar b k` is a de Bruijn index. Reading outward from an occurrence,
    `k = 0` is the innermost enclosing binder: a `Formula` quantifier if the
    occurrence sits under one, otherwise **ν** of the enclosing refinement;
    further-out `k`s are the enclosing `Ty.arrow` binders. The base `b` must
    match the binder's base; ill-base BVars in well-formed types never appear.

    `Term.fvar b x` refers to an `REnv` slot named `x` (looked up with
    `REnv.get`). ν is *never* an `fvar` — it is always `BVar`-bound. -/
inductive Term : Base → Type where
  | const : (b : Base) → b.interp → Term b
  | bvar  : (b : Base) → Nat → Term b
  | fvar  : (b : Base) → EVar → Term b
  | add   : Term .int  → Term .int  → Term .int
  /-- `m(BVar k)`: measure `m` of the value bound at de Bruijn index `k` (any
      value — typically a datatype value, which has no sort of its own). -/
  | mbvar : String → Nat → Term .int
  /-- `m(x)`: measure `m` of the value of the free variable `x`. -/
  | mfvar : String → EVar → Term .int
  /-- The value bound at de Bruijn index `k`, read as an integer whatever the
      binder's sort (a payload field, in a measure equation). -/
  | ibvar : Nat → Term .int
  /-- The value bound at de Bruijn index `k`, read as a boolean whatever the
      binder's sort (a payload field, in a measure equation). -/
  | bbvar : Nat → Term .bool
  | not   : Term .bool → Term .bool
  | and   : Term .bool → Term .bool → Term .bool
  /-- Integer comparison, as a boolean term (a condition for `ite`). -/
  | leqI  : Term .int → Term .int → Term .bool
  /-- `if c then t else e`, at any sort. -/
  | ite   : (b : Base) → Term .bool → Term b → Term b → Term b

/-- First-order formulas over `Term`s.

    Logical connectives are explicit (no metalevel `Prop` mixing). Quantifiers
    are *locally nameless*: each `exI φ` / `exB φ` binds the de Bruijn `BVar 0`
    inside `φ` (shifting all outer binders up by one). Together with ν (also a
    `BVar`; see `Refinement` below) this means formulas contain no binder names
    at all — substitution and opening are capture-free by construction. -/
inductive Formula where
  | tt   : Formula
  | ff   : Formula
  | eq   : (b: Base) -> Term b  → Term b → Formula
  | leq  : (b : Base) → Term b → Term b → Formula   -- polymorphic comparison
  | and  : Formula → Formula → Formula
  | or   : Formula → Formula → Formula
  | not  : Formula → Formula
  | imp  : Formula → Formula → Formula
  | ex   : Base -> Formula → Formula   -- ∃b. φ
  | all  : Base -> Formula → Formula   -- ∀b. φ

/-- Integer comparison, the common case. -/
@[match_pattern, reducible] def Formula.leqI (t₁ t₂ : Term .int) : Formula := .leq .int t₁ t₂

/-- A refinement, one stratification level *above* `Formula`: either a
    kvar-FREE `Formula` (whose `BVar 0`, i.e. ν, denotes the refined value), or a
    single κ-application `κ(t₁, …, tₙ)`. Keeping κ here rather than inside
    `Formula` makes a refinement *atomic* — a constraint XOR one positive κ
    atom — so κ can never be negated/disjoined/nested. Every VC the generator
    emits then has the shape `(⋀ refinement-hyps) → refinement-head`, i.e. it is
    a Constrained Horn Clause by construction. `Refinement.interp` (in
    `Spec/Logic.lean`) is the only interpretation that needs the κ-assignment.
    (The κ name is an `EVar`; see `KVar` below, defined to be `EVar`.) -/
inductive Refinement where
  | fmla : Formula → Refinement
  | kapp : EVar → List (Σ b : Base, Term b) → Refinement
  /-- Conjunction of refinements: produced by type substitution
      `α{r}[α := b{r'}] = b{r' ∧ r}`. Still Horn — refinements never occur
      under negation, and a conjunctive head splits into one clause per conjunct. -/
  | conj : Refinement → Refinement → Refinement

/-! ## κ-assignments

  A `KVar` is a name for an *uninterpreted* predicate symbol (a "κ" in the
  refinement-types literature). The solver picks `KEnv`-values that satisfy
  the VCs; the user existentially binds over `KEnv` to invoke the solver. -/

abbrev KVar : Type := EVar

/-- κ-assignment: maps each `KVar` to a Lean predicate over its (heterogeneous)
    base-typed argument list. -/
abbrev KEnv : Type := KVar → List (Σ b : Base, b.interp) → Prop

/-! ## Types — locally nameless -/

inductive Ty where
  | refine : (b : Base) → Refinement → Ty -- `{ν: b | r}`
  | arrow  : Ty → Ty → Ty                   -- `x:s -> t`
  | forall : Kind → Ty → Ty                 -- `∀α:k. t`; body has `tbvar 0` = α
  | prod   : Ty → Ty → Ty                   -- dependent pair `Σ x:t₁. t₂`; `t₂` has `BVar 0` = x
  /-- A refined datatype applied to type arguments, `C[τ₀ … τₙ₋₁]{ν | r}`.
      Datatypes have no sort in the refinement logic: `r` (ν = `BVar 0`, a
      datatype value) can only observe ν through measures. The arguments are a
      function out of `Fin n` (not a `List`) so `Ty` stays an ordinary inductive. -/
  | data   : String → (n : Nat) → (Fin n → Ty) → Refinement → Ty

/-! ## Expressions — locally nameless

  Every binding form (`lam`, `letin`) carries no `EVar`. The body is an `Exp`
  with `BVar 0` representing the innermost binder; outer binders use `BVar 1`,
  etc. Free variables remain named via `fvar`.
-/

inductive Exp where
  | bvar   : Nat  → Exp                 -- de Bruijn index for bound vars
  | fvar   : EVar → Exp                 -- named free var
  | iconst : Int  → Exp
  | bconst : Bool → Exp
  | lam    : Exp → Exp                  -- body has BVar 0 = parameter
  | letin  : Exp → Exp → Exp            -- letin e₁ e₂; e₂ has BVar 0 = bound name
  | app    : Exp → Exp → Exp
  | ann    : Exp → Ty  → Exp
  | and    : Exp → Exp → Exp
  | not    : Exp → Exp
  | leq    : Exp → Exp → Exp
  | ite    : Exp → Exp → Exp → Exp
  | add    : Exp → Exp → Exp
  | unreach : Exp                       -- `assert false` / unreachable; not a value, gets stuck
  | fix    : Exp → Exp                  -- recursive function `fix f. λx. body`;
                                        -- body has BVar 1 = f (self), BVar 0 = x (param)
  | tabs   : Kind → Exp → Exp           -- type abstraction `Λα:k. e` (`tbvar 0` = α in types)
  | tapp   : Exp → Ty → Exp             -- type application `e[τ]`
  | pair   : Exp → Exp → Exp            -- pair `(e₁, e₂)`
  | split  : Exp → Exp → Exp            -- `let (x, y) = e₁ in e₂`; e₂ has BVar 1 = x, BVar 0 = y
  /-- Constructor `j` of datatype `C`, at the type arguments `τs`, with a single
      payload (multi-field constructors take a pair). -/
  | ctor   : String → Nat → List Ty → Exp → Exp
  /-- Pattern match: alternative `j` handles constructor `j`; it binds the
      payload as BVar 0. -/
  | case   : Exp → (n : Nat) → (Fin n → Exp) → Exp

/-! ## Runtime values

  Locally nameless closures: `clos body` carries an `Exp` body whose `BVar 0`
  represents the parameter.
-/

inductive Val where
  | iconst : Int  → Val
  | bconst : Bool → Val
  | clos   : Exp  → Val
  | fclos  : Exp  → Val                 -- recursive closure: body of `Exp.fix`
  | pair   : Val → Val → Val
  | ctor   : String → Nat → Val → Val   -- constructor `j` of datatype `C` with its payload

/-- Inject a value into the syntax (used by big-step `lam` and `Exp.openVal`). -/
@[simp] def Val.toExp : Val → Exp
  | .iconst n   => .iconst n
  | .bconst b   => .bconst b
  | .clos body  => .lam body
  | .fclos body => .fix body
  | .pair v₁ v₂ => .pair v₁.toExp v₂.toExp
  | .ctor C j w => .ctor C j [] w.toExp


/-- Locally closed at level `k`: every `bvar j` satisfies `j < k`.
    `ann`'s embedded `Ty` must be `Ty.lc_at k` as well. -/
def Exp.lc_at : Nat → Exp → Prop
  | k, .bvar j        => j < k
  | _, .fvar _        => True
  | _, .iconst _      => True
  | _, .bconst _      => True
  | k, .lam body      => body.lc_at (k+1)
  | k, .letin e₁ e₂   => e₁.lc_at k ∧ e₂.lc_at (k+1)
  | k, .app e₁ e₂     => e₁.lc_at k ∧ e₂.lc_at k
  | k, .ann e _       => e.lc_at k
  | k, .and e₁ e₂     => e₁.lc_at k ∧ e₂.lc_at k
  | k, .not e         => e.lc_at k
  | k, .leq e₁ e₂     => e₁.lc_at k ∧ e₂.lc_at k
  | k, .ite e₀ e₁ e₂  => e₀.lc_at k ∧ e₁.lc_at k ∧ e₂.lc_at k
  | k, .add e₁ e₂     => e₁.lc_at k ∧ e₂.lc_at k
  | _, .unreach       => True
  | k, .fix body      => body.lc_at (k+2)
  | k, .tabs _ e      => e.lc_at k
  | k, .tapp e _      => e.lc_at k
  | k, .pair e₁ e₂    => e₁.lc_at k ∧ e₂.lc_at k
  | k, .split e₁ e₂   => e₁.lc_at k ∧ e₂.lc_at (k+2)
  | k, .ctor _ _ _ e  => e.lc_at k
  | k, .case e _ alts => e.lc_at k ∧ ∀ j, (alts j).lc_at (k+1)

/-- A `Val` is closed when its `toExp` is locally closed (note: the closure
    body is required `lc_at 1` since `BVar 0` is the parameter). -/
def Val.lc (v : Val) : Prop := v.toExp.lc_at 0


/-! ## Substitution on expressions -/

/-- Replace `bvar k` with expression `u` (capture-free if `u` is locally closed). -/
def Exp.openExp (k : Nat) (u : Exp) (e : Exp) : Exp :=
  match e with
  | .bvar j        => if j = k then u else .bvar j
  | .fvar y        => .fvar y
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .lam body      => .lam (Exp.openExp (k+1) u body)
  | .letin e₁ e₂   => .letin (Exp.openExp k u e₁) (Exp.openExp (k+1) u e₂)
  | .app e₁ e₂     => .app (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .ann e t       => .ann (Exp.openExp k u e) t
  | .and e₁ e₂     => .and (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .not e         => .not (Exp.openExp k u e)
  | .leq e₁ e₂     => .leq (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .ite e₀ e₁ e₂  => .ite (Exp.openExp k u e₀) (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .add e₁ e₂     => .add (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .unreach       => .unreach
  | .fix body      => .fix (Exp.openExp (k+2) u body)
  | .tabs κ e      => .tabs κ (Exp.openExp k u e)
  | .tapp e t      => .tapp (Exp.openExp k u e) t
  | .pair e₁ e₂    => .pair (Exp.openExp k u e₁) (Exp.openExp k u e₂)
  | .split e₁ e₂   => .split (Exp.openExp k u e₁) (Exp.openExp (k+2) u e₂)
  | .ctor C j τs e => .ctor C j τs (Exp.openExp k u e)
  | .case e n alts => .case (Exp.openExp k u e) n (fun j => Exp.openExp (k+1) u (alts j))

/-- Open `bvar k` with a value (via `Val.toExp`). Handy for big-step. -/
def Exp.openVal (k : Nat) (v : Val) : Exp → Exp := Exp.openExp k v.toExp

/-! ## Free variables, local closure and type-freeness of values -/

def Exp.fv : Exp → List EVar
  | .bvar _        => []
  | .fvar x        => [x]
  | .iconst _      => []
  | .bconst _      => []
  | .lam body      => Exp.fv body
  | .letin e₁ e₂   => Exp.fv e₁ ++ Exp.fv e₂
  | .app e₁ e₂     => Exp.fv e₁ ++ Exp.fv e₂
  | .ann e _       => Exp.fv e
  | .and e₁ e₂     => Exp.fv e₁ ++ Exp.fv e₂
  | .not e         => Exp.fv e
  | .leq e₁ e₂     => Exp.fv e₁ ++ Exp.fv e₂
  | .ite e₀ e₁ e₂  => Exp.fv e₀ ++ Exp.fv e₁ ++ Exp.fv e₂
  | .add e₁ e₂     => Exp.fv e₁ ++ Exp.fv e₂
  | .unreach       => []
  | .fix body      => Exp.fv body
  | .tabs _ e      => Exp.fv e
  | .tapp e _      => Exp.fv e
  | .pair e₁ e₂    => Exp.fv e₁ ++ Exp.fv e₂
  | .split e₁ e₂   => Exp.fv e₁ ++ Exp.fv e₂
  | .ctor _ _ _ e  => Exp.fv e
  | .case e n alts => Exp.fv e ++ (List.finRange n).flatMap fun j => Exp.fv (alts j)

def Val.fv (v : Val) : List EVar := v.toExp.fv

/-- A value is *closed* when it has no free names. For `iconst`/`bconst` this
    is automatic; for `clos body` it says the body's free names are all bound
    by the parameter. Separate from `Val.lc` (which constrains de Bruijn
    indices, not free names). -/
@[simp]
def Val.closed (v : Val) : Prop := Val.fv v = []

/-- An expression with no type information anywhere. -/
def Exp.TypeFree : Exp → Prop
  | .bvar _ | .fvar _ | .iconst _ | .bconst _ | .unreach => True
  | .lam b | .not b | .fix b => b.TypeFree
  | .letin e₁ e₂ | .app e₁ e₂ | .and e₁ e₂ | .leq e₁ e₂ | .add e₁ e₂
  | .pair e₁ e₂ | .split e₁ e₂ => e₁.TypeFree ∧ e₂.TypeFree
  | .ite e₀ e₁ e₂ => e₀.TypeFree ∧ e₁.TypeFree ∧ e₂.TypeFree
  | .ctor _ _ τs e => τs = [] ∧ e.TypeFree
  | .case e _ alts => e.TypeFree ∧ ∀ j, (alts j).TypeFree
  | .ann _ _ | .tabs _ _ | .tapp _ _ => False

/-- A value is erased when its syntax carries no types. -/
def Val.Erased (v : Val) : Prop := v.toExp.TypeFree

/-- `Ty.data` from a list of type arguments. -/
@[simp, reducible] def Ty.dataL (C : String) (τs : List Ty) (r : Refinement := .fmla .tt) : Ty :=
  .data C τs.length (fun i => τs[i]) r

/-! ## Datatype declarations

  A program is a list of datatype declarations (`DEnv`) followed by an
  expression. A declaration lists the kinds of its type parameters, its
  constructors — each with a telescope of field types — and its measures. In a
  field type, `tbvar i` is parameter `i`, and `BVar` levels refer to earlier
  fields; field types have no free term or type variables.

  At runtime a constructor carries a single payload: its fields in nested pairs
  ending in a unit, `(f₀, (f₁, … (fₙ₋₁, ())))`. Its type is the telescope
  `Σ f₀:t₀. … Σ fₙ₋₁:tₙ₋₁. Int`; pattern matching records the measure equations
  on the terminal unit, which is under all the fields. -/

/-- The payload type of a constructor with fields `ts`. -/
def Ty.tuple : List Ty → Ty
  | []      => .refine .int (.fmla .tt)
  | t :: ts => .prod t (Ty.tuple ts)

/-- A measure's body for one constructor, over that constructor's fields:
    an integer built from literals, `Int` fields, measures of fields, `+`, and
    conditionals — on a comparison, or on a `Bool` field (`and`/`or`/`not` of
    fields by nesting). -/
inductive MBody where
  | const : Int → MBody
  | field : Nat → MBody               -- the (`Int`) field `i`
  | meas  : String → Nat → MBody      -- measure `m` of field `i`
  | add   : MBody → MBody → MBody
  | iteLe : MBody → MBody → MBody → MBody → MBody   -- `if a ≤ b then t else e`
  | iteB  : Nat → MBody → MBody → MBody              -- `if (Bool field i) then t else e`
  deriving Repr

/-- `max a b`, as a conditional. -/
@[reducible] def MBody.max (a b : MBody) : MBody := .iteLe a b b a

/-- The variance of a datatype parameter: how subtyping on the datatype
    follows subtyping on the argument. -/
inductive Variance where
  | co     : Variance
  | contra : Variance
  | inv    : Variance
  deriving Repr, DecidableEq

structure DataDecl where
  params : List Kind
  /-- The constructors, each with its field types. -/
  ctorFields : List (String × List Ty)
  /-- Declared variances of the parameters (checked against the payloads);
      a parameter without one is invariant. -/
  variances : List Variance := []
  /-- The measures, each with one body per constructor (in order). -/
  measures : List (String × List MBody) := []

/-- The constructors with their payload types. -/
def DataDecl.ctors (d : DataDecl) : List (String × Ty) :=
  d.ctorFields.map fun c => (c.1, Ty.tuple c.2)

/-- The body of measure `m` for constructor `j`. -/
def DataDecl.measBody? (d : DataDecl) (m : String) (j : Nat) : Option MBody :=
  (d.measures.lookup m).bind fun bs => bs[j]?

abbrev DEnv := List (String × DataDecl)

/-- The declaration of datatype `C`. -/
def DEnv.decl? (de : DEnv) (C : String) : Option DataDecl := de.lookup C

/-- The payload type of constructor `j` of `C`. -/
def DEnv.payload? (de : DEnv) (C : String) (j : Nat) : Option Ty :=
  (de.decl? C).bind fun d => (d.ctors[j]?).map Prod.snd

/-- The field types of constructor `j` of `C`. -/
def DEnv.fields? (de : DEnv) (C : String) (j : Nat) : Option (List Ty) :=
  (de.decl? C).bind fun d => (d.ctorFields[j]?).map Prod.snd

/-- The number of fields of constructor `j` of `C`. -/
def DEnv.nFields (de : DEnv) (C : String) (j : Nat) : Nat := ((de.fields? C j).map List.length).getD 0

/-! ### Type erasure

  Types never influence evaluation, so programs are run after erasing them
  (`Run`, `Spec/Semantics.lean`). Erasure is what makes opening a type binder
  (`Exp.openTv`) invisible at runtime. -/

/-- Erase all type information: annotations, type abstractions and type
    applications. -/
def Exp.erase : Exp → Exp
  | .bvar j        => .bvar j
  | .fvar y        => .fvar y
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .lam body      => .lam body.erase
  | .letin e₁ e₂   => .letin e₁.erase e₂.erase
  | .app e₁ e₂     => .app e₁.erase e₂.erase
  | .ann e _       => e.erase
  | .and e₁ e₂     => .and e₁.erase e₂.erase
  | .not e         => .not e.erase
  | .leq e₁ e₂     => .leq e₁.erase e₂.erase
  | .ite e₀ e₁ e₂  => .ite e₀.erase e₁.erase e₂.erase
  | .add e₁ e₂     => .add e₁.erase e₂.erase
  | .unreach       => .unreach
  | .fix body      => .fix body.erase
  | .tabs _ e      => e.erase
  | .tapp e _      => e.erase
  | .pair e₁ e₂    => .pair e₁.erase e₂.erase
  | .split e₁ e₂   => .split e₁.erase e₂.erase
  | .ctor C j _ e  => .ctor C j [] e.erase
  | .case e n alts => .case e.erase n (fun j => (alts j).erase)

/-- Structural skeleton of `Ty`: counts arrow nesting, ignoring refinement
    bodies. Preserved by `openVar` / `openVarAt`. Used as a termination
    measure for the algorithmic subtyping function in `Checker/VCGen.lean`. -/
@[simp]
def Ty.skel : Ty → Nat
  | .refine _ _ => 0
  | .arrow s t  => 1 + s.skel + t.skel
  | .forall _ t => 1 + t.skel
  | .prod s t   => 1 + s.skel + t.skel
  | .data _ _ args _ => 1 + (List.ofFn fun i => (args i).skel).sum

/-- Every element of a list of naturals is at most its sum. -/
theorem List.le_sum_of_mem_nat : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp only [List.sum_cons]; omega
  | y :: _, _, .tail _ h => by
      have := List.le_sum_of_mem_nat h
      simp only [List.sum_cons]; omega

theorem Ty.skel_data_lt (C : String) (n : Nat) (args : Fin n → Ty) (r : Refinement) (i : Fin n) :
    (args i).skel < (Ty.data C n args r).skel := by
  have := List.le_sum_of_mem_nat (List.mem_ofFn.mpr ⟨i, rfl⟩ :
    (args i).skel ∈ List.ofFn fun i => (args i).skel)
  simp only [Ty.skel]; omega


end STLC
