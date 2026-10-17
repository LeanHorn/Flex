namespace STLC

/-! # STLC Syntax (locally nameless + deeply embedded refinements)

  Layout:

  1. **Variables, bases, runtime envs** — `EVar`, `Base`, `REnv`.
  2. **Deep-embedded refinement language** — `Term`, `Formula`, `Refinement`.
     Fully LN: ν, the `Formula` quantifiers, and the `Ty.arrow` binders are all
     de Bruijn `BVar`s.
  3. **Types (LN)** — `Ty`. `arrow s t` carries no binder name; `t` is a body
     with `BVar 0` standing for the function argument.
  4. **Expressions (LN)** — `Exp`. Binding forms (`lam`, `letin`) carry no
     binder name; the body has `BVar 0` for the innermost binder.

  All substitution / opening / closing / freshness machinery lives in
  `Substitution.lean`. This file declares data only.
-/

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
  | not   : Term .bool → Term .bool
  | and   : Term .bool → Term .bool → Term .bool
-- NOTE: no cross-base constructors (e.g. `leq : Term .int → Term .int → Term .bool`).
-- Keeping each `Term` homogeneous in its base means an `REnv` update at one base
-- can never affect a term of another base. Cross-base relations go in
-- `Formula` (e.g. `Formula.leq`).

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
    `Substitution.lean`) is the only interpretation that needs the κ-assignment.
    (The κ name is an `EVar`; see `KVar` below, defined to be `EVar`.) -/
inductive Refinement where
  | fmla : Formula → Refinement
  | kapp : EVar → List (Σ b : Base, Term b) → Refinement
  /-- Conjunction of refinements: produced by type substitution
      `α{r}[α := b{r'}] = b{r' ∧ r}`. Still Horn — refinements never occur
      under negation, and a conjunctive head splits into one clause per conjunct. -/
  | conj : Refinement → Refinement → Refinement

/-! ## Syntactic constraints (CHC tree)

  A verification condition, produced by VC generation (`VCGen.lean`), as a
  Constrained Horn Clause tree. -/
inductive Cstr where
  | head : Refinement → Cstr             -- goal refinement `r`
  | imp  : Refinement → Cstr → Cstr      -- hypothesis `r ⇒ c`
  | all  : EVar → Base → Cstr → Cstr     -- `∀ x:b. c`
  | conj : Cstr → Cstr → Cstr            -- `c₁ ∧ c₂`

/-- The trivially-true constraint (used for synthesis leaves). -/
@[simp] def Cstr.triv : Cstr := .head (.fmla .tt)
@[simp] def Cstr.ff : Cstr := .head (.fmla .ff)

/-! ## κ-assignments

  A `KVar` is a name for an *uninterpreted* predicate symbol (a "κ" in the
  refinement-types literature). The solver picks `KEnv`-values that satisfy
  the VCs; the user existentially binds over `KEnv` to invoke the solver. -/

abbrev KVar : Type := EVar

/-- κ-assignment: maps each `KVar` to a Lean predicate over its (heterogeneous)
    base-typed argument list. -/
abbrev KEnv : Type := KVar → List (Σ b : Base, b.interp) → Prop

/-! ## KEnv construction helpers

  `KPred n` is the type of n-ary curried Int predicates.
  `liftKPred n` lifts a `KPred n` into the heterogeneous-list form expected
  by `KEnv`: it peels Int values off the front of the arg list one at a time.
  `mkKEnv` builds a `KEnv` from a finite name→predicate list, defaulting to
  `True` for unmentioned keys. `exists_kenv_curried` is the sufficiency lemma
  used by `intro_kenv` to replace `∃ κ : KEnv, P κ` with individual curried
  existentials. -/

/-- `KPred n` = `Int → Int → … → Int → Prop` (n arguments, curried). -/
@[reducible]
def KPred : Nat → Type
  | 0     => Prop
  | n + 1 => Int → KPred n

/-- Lift a curried `KPred n` to operate on a heterogeneous arg list.
    Returns `True` on arity or type mismatch. -/
def liftKPred : (n : Nat) → KPred n → List (Σ b : Base, b.interp) → Prop
  | 0,     p, []                    => p
  | 0,     _, _                     => True
  | _ + 1, _, []                    => True
  | n + 1, f, (⟨.int,  v⟩ :: rest) => liftKPred n (f v) rest
  | _ + 1, _, _                     => True

@[simp] theorem liftKPred_zero (p : Prop) :
    liftKPred 0 p [] = p := rfl

@[simp] theorem liftKPred_succ_int (n : Nat) (f : Int → KPred n) (v : Int)
    (rest : List (Σ b : Base, b.interp)) :
    liftKPred (n + 1) f (⟨.int, v⟩ :: rest) = liftKPred n (f v) rest := rfl


def mkKEnv (ks : List (KVar × (List (Σ b : Base, b.interp) → Prop))) : KEnv :=
  fun name => (ks.lookup name).getD (fun _ => True)

theorem exists_kenv_curried {P : KEnv → Prop}
    (ks : List (KVar × (List (Σ b : Base, b.interp) → Prop)))
    (h : P (mkKEnv ks)) : ∃ κ : KEnv, P κ :=
  ⟨mkKEnv ks, h⟩

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

/-- Typing context: a list of free-name × type pairs. Names are unique by convention. -/
@[simp]
abbrev TEnv := List (EVar × Ty)

/-- Get all free names declared in a typing context. -/
def TEnv.dom : TEnv → List EVar
  | []          => []
  | (x, _) :: Γ => x :: TEnv.dom Γ


/-! ## Runtime values

  Locally nameless closures: `clos body` carries an `Exp` body whose `BVar 0`
  represents the parameter. Operations on `Val` (`fv`, `lc`, etc.) live in
  `Substitution.lean` alongside the corresponding `Exp` operations.
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

/-- The base a `Val` carries (`none` for a closure). Mirrors `Ty.optBase`:
    a value inhabiting a refinement type `{ν:b|…}` has `optBase = some b`. -/
@[simp] def Val.optBase : Val → Option Base
  | .iconst _ => some .int
  | .bconst _ => some .bool
  | .clos _   => none
  | .fclos _  => none
  | .pair _ _ => none
  | .ctor _ _ _ => none

/-- The runtime comparison: defined on two base values of the same sort (it
    reads only their runtime tags, so it needs no type information), stuck on
    anything else. -/
def Val.leb? : Val → Val → Option Bool
  | .iconst a, .iconst b => some (decide (a ≤ b))
  | .bconst a, .bconst b => some (decide (a ≤ b))
  | _, _ => none

/-- Val-level (lossless) lookup. -/
@[simp, reducible]
def REnv.lookup (γ : REnv) (x : EVar) : Val := γ.map x

/-- Val-level (lossless) update of the name map: `write γ x (lookup γ x) = γ`
    unconditionally. Preserves the de Bruijn stack `bv`. -/
@[simp, reducible]
def REnv.write (γ : REnv) (x : EVar) (v : Val) : REnv :=
  { γ with map := fun y => if x == y then v else γ.map y }

/-- Enter a binder: push value `v` as the new innermost de Bruijn slot (index 0),
    shifting the existing stack up one. The name map is untouched. -/
@[simp] def REnv.push (γ : REnv) (v : Val) : REnv := { γ with bv := v :: γ.bv }

/-- Insert value `v` at de Bruijn index `k` (shifting indices `≥ k` up one).
    `insertBV 0 = push`. Used to bridge `push`-style `TyDenote` with `openVar`:
    putting a value into the stack at level `k` mirrors opening `BVar k` to a
    fresh name bound to that value. -/
def REnv.insertBV (k : Nat) (v : Val) (γ : REnv) : REnv := { γ with bv := γ.bv.insertIdx k v }

@[simp] theorem REnv.insertBV_zero (v : Val) (γ : REnv) : γ.insertBV 0 v = γ.push v := rfl

@[simp] theorem REnv.insertBV_map (k : Nat) (v : Val) (γ : REnv) :
    (γ.insertBV k v).map = γ.map := rfl

@[simp] theorem REnv.insertBV_bv (k : Nat) (v : Val) (γ : REnv) :
    (γ.insertBV k v).bv = γ.bv.insertIdx k v := rfl

@[simp] theorem REnv.insertBV_sorts (k : Nat) (v : Val) (γ : REnv) :
    (γ.insertBV k v).sorts = γ.sorts := rfl

/-- Pushing then inserting deeper = inserting then pushing: `push` is `insertBV 0`,
    and inserting at `k+1` after a `push` is the same as inserting at `k` first. -/
theorem REnv.push_insertBV_comm (γ : REnv) (w v : Val) (k : Nat) :
    (γ.insertBV k v).push w = (γ.push w).insertBV (k+1) v := rfl

/-- Read the `b`-typed value of the de Bruijn `BVar k` from the stack. Out of
    range (never on a well-formed read) defaults per base via `Val.proj`. -/
@[simp, reducible]
def REnv.getBV (b : Base) (γ : REnv) (k : Nat) : b.sem γ.sorts :=
  Val.proj (b.resolve γ.sorts) (γ.bv[k]?.getD (.iconst 0))

/-- Look up the `b`-typed value of variable `x` in `γ` (base-indexed view). -/
@[simp, reducible]
def REnv.get (b : Base) (γ : REnv) (x : EVar) : b.sem γ.sorts :=
  (γ.lookup x).proj (b.resolve γ.sorts)

/-- Update the `b`-typed slot for `x` in `γ` to `v` (base-indexed view). -/
@[simp, reducible]
def REnv.update (b : Base) (γ : REnv) (x : EVar) (v : b.sem γ.sorts) : REnv :=
  γ.write x (Val.inj (b.resolve γ.sorts) v)

/-- Derived accessors mirroring the old two-field layout. -/
@[simp, reducible] def REnv.bools (γ : REnv) (x : EVar) : Bool := REnv.get .bool γ x

/-- `v` is a value of base `s`. -/
@[simp] def Val.HasSort : BSort → Val → Prop
  | .int,  v => ∃ n, v = .iconst n
  | .bool, v => ∃ c, v = .bconst c

/-- The cell for `x` stores a value of the base sort `b` stands for. Holds for
    every slot bound at sort `b` in a well-typed model; needed to know
    `update b _ x (get b _ x)` round-trips. -/
@[simp] def REnv.HasBase (γ : REnv) (x : EVar) (b : Base) : Prop :=
  Val.HasSort (b.resolve γ.sorts) (γ.map x)


/-! ## 5b. Val operations (depend on Exp.* declared above) -/

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

/-- Structural skeleton of `Ty`: counts arrow nesting, ignoring refinement
    bodies. Preserved by `openVar` / `openVarAt`. Used as a termination
    measure for the algorithmic subtyping function in `VCGen.lean`. -/
@[simp]
def Ty.skel : Ty → Nat
  | .refine _ _ => 0
  | .arrow s t  => 1 + s.skel + t.skel
  | .forall _ t => 1 + t.skel
  | .prod s t   => 1 + s.skel + t.skel
  | .data _ _ args _ => 1 + (List.ofFn fun i => (args i).skel).sum

/-- `Ty.data` from a list of type arguments. -/
@[simp, reducible] def Ty.dataL (C : String) (τs : List Ty) (r : Refinement := .fmla .tt) : Ty :=
  .data C τs.length (fun i => τs[i]) r

/-! ## Datatype declarations

  A program is a list of datatype declarations (`DEnv`) followed by an
  expression. A declaration lists the kinds of its type parameters, its
  constructors — each with a telescope of field types — and its measures. In a
  field type, `tbvar i` is parameter `i`, and `BVar` levels refer to earlier
  fields; field types have no free term or type variables.

  At runtime a constructor carries a single payload: a unit for no fields, the
  field itself for one, and nested pairs `(f₀, (f₁, … fₙ₋₁))` for more. Its type
  is the telescope `Σ f₀:t₀. … tₙ₋₁`; the last field's type — under all the
  others — is where pattern matching records the measure equations. -/

/-- The payload type of a constructor with fields `ts`. -/
def Ty.tuple : List Ty → Ty
  | []      => .refine .int (.fmla .tt)
  | [t]     => t
  | t :: ts => .prod t (Ty.tuple ts)

/-- A measure's body for one constructor, over that constructor's fields:
    an integer built from literals, `Int` fields, and measures of fields. -/
inductive MBody where
  | const : Int → MBody
  | field : Nat → MBody               -- the (`Int`) field `i`
  | meas  : String → Nat → MBody      -- measure `m` of field `i`
  | add   : MBody → MBody → MBody
  deriving Repr

/-- A measure body as a refinement term, given terms for the fields and for
    the fields' measures. -/
def MBody.toTerm (fld : Nat → Term .int) (msr : String → Nat → Term .int) : MBody → Term .int
  | .const n  => .const .int n
  | .field i  => fld i
  | .meas m i => msr m i
  | .add a b  => .add (a.toTerm fld msr) (b.toTerm fld msr)

/-- Every field a body reads is one of the `n` fields. -/
def MBody.idxOK (n : Nat) : MBody → Bool
  | .const _  => true
  | .field i  => decide (i < n)
  | .meas _ i => decide (i < n)
  | .add a b  => a.idxOK n && b.idxOK n

/-- Conjoin `r` into the refinement of the last component of a payload type
    with `n + 1` components (types without a refinement are left alone). -/
def Ty.strengthenLast : Nat → Ty → Refinement → Ty
  | 0,     .refine b r',     r => .refine b (.conj r' r)
  | 0,     .data C k a r',   r => .data C k a (.conj r' r)
  | n + 1, .prod s t,        r => .prod s (Ty.strengthenLast n t r)
  | _,     t,                _ => t

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

/-- The measures of constructor `j`, with their bodies for it. -/
def DataDecl.ctorMeasures (d : DataDecl) (j : Nat) : List (String × MBody) :=
  d.measures.filterMap fun mb => (mb.2[j]?).map fun b => (mb.1, b)

/-- The body of measure `m` for constructor `j`. -/
def DataDecl.measBody? (d : DataDecl) (m : String) (j : Nat) : Option MBody :=
  (d.measures.lookup m).bind fun bs => bs[j]?

abbrev DEnv := List (String × DataDecl)

/-- The declaration of datatype `C`. -/
def DEnv.decl? (de : DEnv) (C : String) : Option DataDecl := de.lookup C

/-- The declared variance of parameter `i` of `C` (invariant by default). -/
def DEnv.var (de : DEnv) (C : String) (i : Nat) : Variance :=
  ((de.decl? C).bind fun d => d.variances[i]?).getD .inv

/-- The payload type of constructor `j` of `C`. -/
def DEnv.payload? (de : DEnv) (C : String) (j : Nat) : Option Ty :=
  (de.decl? C).bind fun d => (d.ctors[j]?).map Prod.snd

/-- The field types of constructor `j` of `C`. -/
def DEnv.fields? (de : DEnv) (C : String) (j : Nat) : Option (List Ty) :=
  (de.decl? C).bind fun d => (d.ctorFields[j]?).map Prod.snd

/-- The measures of constructor `j` of `C`, with their bodies for it. -/
def DEnv.ctorMeasures (de : DEnv) (C : String) (j : Nat) : List (String × MBody) :=
  ((de.decl? C).map fun d => d.ctorMeasures j).getD []

/-- A conjunction of formulas. -/
def Formula.conjAll : List Formula → Formula
  | []      => .tt
  | φ :: φs => .and φ (Formula.conjAll φs)

/-- The number of fields of constructor `j` of `C`. -/
def DEnv.nFields (de : DEnv) (C : String) (j : Nat) : Nat := ((de.fields? C j).map List.length).getD 0

/-- What constructing `C j` from the fields `as` reveals about the result ν
    (`BVar 0`): each measure equals its body for this constructor. -/
def DEnv.ctorFacts (de : DEnv) (C : String) (j : Nat) (as : List EVar) : Refinement :=
  .fmla (Formula.conjAll ((de.ctorMeasures C j).map fun mb =>
    .eq .int (.mbvar mb.1 0)
      (mb.2.toTerm (fun i => if i < as.length then .fvar .int (as.getD i "") else .const .int 0)
        (fun m' i => if i < as.length then .mfvar m' (as.getD i "") else .const .int 0))))

/-- What matching `x` against `C j` (with `n` fields) reveals, read at the
    payload's last field — where field `i` is `BVar (n - 1 - i)` — : each
    measure of `x` equals its body for this constructor. -/
def DEnv.caseFacts (de : DEnv) (C : String) (j n : Nat) (x : EVar) : Refinement :=
  .fmla (Formula.conjAll ((de.ctorMeasures C j).map fun mb =>
    .eq .int (.mfvar mb.1 x)
      (mb.2.toTerm (fun i => .ibvar (n - 1 - i)) (fun m' i => .mbvar m' (n - 1 - i)))))

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
    variables: `x` for one field, `(x₀, (x₁, … xₙ₋₁))` for more (none for none). -/
def Exp.tupleVarsN : Nat → Exp → Option (List EVar)
  | 0,     _                 => some []
  | 1,     .fvar x           => some [x]
  | n + 2, .pair (.fvar x) e => (Exp.tupleVarsN (n + 1) e).map (x :: ·)
  | _,     _                 => none

/-- The refinement a constructor application synthesizes: the measure facts,
    when its fields are given as variables. -/
def DEnv.ctorRefine (de : DEnv) (C : String) (j : Nat) (e : Exp) : Refinement :=
  match e.tupleVarsN (de.nFields C j) with
  | some as => de.ctorFacts C j as
  | none    => .fmla .tt

/-- The type an alternative of a match on `C` binds its payload at (`tz`, the
    payload at the scrutinee's type arguments): when the scrutinee is a
    variable `x`, the last field records the measure facts about `x`. -/
def DEnv.altTy (de : DEnv) (C : String) (j : Nat) (x? : Option EVar) (tz : Ty) : Ty :=
  match x? with
  | some x => tz.strengthenLast (de.nFields C j - 1) (de.caseFacts C j (de.nFields C j) x)
  | none   => tz

/-! ## Measure semantics

  A measure is the structurally recursive function its bodies define, on
  runtime values: on `C j w` it is the body for `j`, read on the fields of the
  payload `w`; on anything else it is `0`. -/

/-- The fields of a payload of a constructor with `n` fields. -/
def Val.fieldsN : Nat → Val → List Val
  | 0,     _          => []
  | 1,     w          => [w]
  | n + 2, .pair a r  => a :: Val.fieldsN (n + 1) r
  | _ + 2, _          => []

theorem Val.sizeOf_le_of_mem_fieldsN : ∀ {n : Nat} {w f : Val}, f ∈ w.fieldsN n → sizeOf f ≤ sizeOf w
  | 0, _, _, h => by simp [Val.fieldsN] at h
  | 1, w, f, h => by simp only [Val.fieldsN, List.mem_singleton] at h; subst h; exact Nat.le_refl _
  | n + 2, .pair a r, f, h => by
    simp only [Val.fieldsN, List.mem_cons] at h
    rcases h with rfl | h
    · simp; omega
    · have := Val.sizeOf_le_of_mem_fieldsN h
      simp; omega
  | _ + 2, .iconst _, _, h | _ + 2, .bconst _, _, h | _ + 2, .clos _, _, h
  | _ + 2, .fclos _, _, h | _ + 2, .ctor _ _ _, _, h => by simp [Val.fieldsN] at h

/-- Evaluate a measure body, given the (integer) fields and their measures. -/
def MBody.eval (fv : Nat → Int) (fm : Nat → String → Int) : MBody → Int
  | .const n  => n
  | .field i  => fv i
  | .meas m i => fm i m
  | .add a b  => a.eval fv fm + b.eval fv fm

/-- The value of measure `m` on `v`. -/
def DEnv.measEval (de : DEnv) (m : String) : Val → Int
  | .ctor C j w =>
    match (de.decl? C).bind fun d => d.measBody? m j with
    | some body =>
      body.eval
        (fun i => if h : i < (w.fieldsN (de.nFields C j)).length then
          Val.proj .int (w.fieldsN (de.nFields C j))[i] else 0)
        (fun i m' => if h : i < (w.fieldsN (de.nFields C j)).length then
          DEnv.measEval de m' (w.fieldsN (de.nFields C j))[i] else 0)
    | none => 0
  | _ => 0
termination_by v => sizeOf v
decreasing_by
  have := Val.sizeOf_le_of_mem_fieldsN (List.getElem_mem h)
  simp; omega

theorem DEnv.measEval_ctor (de : DEnv) (m : String) (C : String) (j : Nat) (w : Val) :
    de.measEval m (.ctor C j w) =
      match (de.decl? C).bind fun d => d.measBody? m j with
      | some body => body.eval
          (fun i => if h : i < (w.fieldsN (de.nFields C j)).length then
            Val.proj .int (w.fieldsN (de.nFields C j))[i] else 0)
          (fun i m' => if h : i < (w.fieldsN (de.nFields C j)).length then
            de.measEval m' (w.fieldsN (de.nFields C j))[i] else 0)
      | none => 0 := by
  rw [DEnv.measEval]

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
