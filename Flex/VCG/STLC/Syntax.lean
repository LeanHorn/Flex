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

/-- The refinement-logic domain of a type-variable sort. Only `B`-kinded type
    variables are ever compared in refinements, and they only ever hold ints or
    bools, so this code type (with closures collapsed to `other`) is faithful.
    It is defined here, before `Val`, to break the `Val → Exp → Ty → Term`
    definitional cycle. -/
inductive BVal where
  | int   : Int → BVal
  | bool  : Bool → BVal
  | other : BVal
  deriving Repr, DecidableEq

@[simp, reducible]
def Base.interp : Base → Type
  | .int     => Int
  | .bool    => Bool
  | .tbvar _ => BVal
  | .tfvar _ => BVal

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
  | not   : Term .bool → Term .bool
  | and   : Term .bool → Term .bool → Term .bool
-- NOTE: no cross-base constructors (e.g. `leq : Term .int → Term .int → Term .bool`).
-- Keeping each `Term` homogeneous in its base means an `REnv` update at one base
-- can never affect a term of another base. Cross-base relations go in
-- `Formula` (e.g. `Formula.leqI`).

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
  | leqI : Term .int  → Term .int  → Formula
  | and  : Formula → Formula → Formula
  | or   : Formula → Formula → Formula
  | not  : Formula → Formula
  | imp  : Formula → Formula → Formula
  | ex   : Base -> Formula → Formula   -- ∃b. φ
  | all  : Base -> Formula → Formula   -- ∀b. φ

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
  /-- A datatype applied to type arguments, `C[τ₀ … τₙ₋₁]`. Datatypes carry no
      refinement and have no sort in the refinement logic. The arguments are a
      function out of `Fin n` (not a `List`) so `Ty` stays an ordinary inductive. -/
  | data   : String → (n : Nat) → (Fin n → Ty) → Ty

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

@[simp] def REnv.empty : REnv := ⟨fun _ => .iconst 0, []⟩

/-- Code a runtime value into the type-variable sort's domain. -/
@[simp, reducible]
def Val.toBVal : Val → BVal
  | .iconst n => .int n
  | .bconst c => .bool c
  | _         => .other

/-- Decode a type-variable-sort value. `other` decodes to a (dummy) closure,
    so that `toBVal (toVal c) = c` for every code `c`. -/
@[simp, reducible]
def BVal.toVal : BVal → Val
  | .int n  => .iconst n
  | .bool c => .bconst c
  | .other  => .clos .unreach

/-- Project a stored `Val` to a base-typed value. The mismatch cases
    (`0`/`false`) are unreachable for well-typed reads. -/
@[simp, reducible]
def Val.proj : (b : Base) → Val → b.interp
  | .int,  .iconst n => n
  | .bool, .bconst c => c
  | .int,  _ => 0
  | .bool, _ => false
  | .tbvar _, v => Val.toBVal v
  | .tfvar _, v => Val.toBVal v

/-- Inject a base-typed value into `Val`. -/
@[simp, reducible]
def Val.inj : (b : Base) → b.interp → Val
  | .int,  n => .iconst n
  | .bool, c => .bconst c
  | .tbvar _, v => BVal.toVal v
  | .tfvar _, v => BVal.toVal v

/-- The base a `Val` carries (`none` for a closure). Mirrors `Ty.optBase`:
    a value inhabiting a refinement type `{ν:b|…}` has `optBase = some b`. -/
@[simp] def Val.optBase : Val → Option Base
  | .iconst _ => some .int
  | .bconst _ => some .bool
  | .clos _   => none
  | .fclos _  => none
  | .pair _ _ => none
  | .ctor _ _ _ => none

/-- Val-level (lossless) lookup. -/
@[simp, reducible]
def REnv.lookup (γ : REnv) (x : EVar) : Val := γ.map x

/-- Val-level (lossless) update of the name map: `write γ x (lookup γ x) = γ`
    unconditionally. Preserves the de Bruijn stack `bv`. -/
@[simp, reducible]
def REnv.write (γ : REnv) (x : EVar) (v : Val) : REnv :=
  ⟨fun y => if x == y then v else γ.map y, γ.bv⟩

/-- Enter a binder: push value `v` as the new innermost de Bruijn slot (index 0),
    shifting the existing stack up one. The name map is untouched. -/
@[simp] def REnv.push (γ : REnv) (v : Val) : REnv := ⟨γ.map, v :: γ.bv⟩

/-- Insert value `v` at de Bruijn index `k` (shifting indices `≥ k` up one).
    `insertBV 0 = push`. Used to bridge `push`-style `TyDenote` with `openVar`:
    putting a value into the stack at level `k` mirrors opening `BVar k` to a
    fresh name bound to that value. -/
def REnv.insertBV (k : Nat) (v : Val) (γ : REnv) : REnv := ⟨γ.map, γ.bv.insertIdx k v⟩

@[simp] theorem REnv.insertBV_zero (v : Val) (γ : REnv) : γ.insertBV 0 v = γ.push v := rfl

@[simp] theorem REnv.insertBV_map (k : Nat) (v : Val) (γ : REnv) :
    (γ.insertBV k v).map = γ.map := rfl

@[simp] theorem REnv.insertBV_bv (k : Nat) (v : Val) (γ : REnv) :
    (γ.insertBV k v).bv = γ.bv.insertIdx k v := rfl

/-- Pushing then inserting deeper = inserting then pushing: `push` is `insertBV 0`,
    and inserting at `k+1` after a `push` is the same as inserting at `k` first. -/
theorem REnv.push_insertBV_comm (γ : REnv) (w v : Val) (k : Nat) :
    (γ.insertBV k v).push w = (γ.push w).insertBV (k+1) v := rfl

/-- Read the `b`-typed value of the de Bruijn `BVar k` from the stack. Out of
    range (never on a well-formed read) defaults per base via `Val.proj`. -/
@[simp, reducible]
def REnv.getBV (b : Base) (γ : REnv) (k : Nat) : b.interp :=
  Val.proj b (γ.bv[k]?.getD (.iconst 0))

/-- Look up the `b`-typed value of variable `x` in `γ` (base-indexed view). -/
@[simp, reducible]
def REnv.get (b : Base) (γ : REnv) (x : EVar) : b.interp :=
  (γ.lookup x).proj b

/-- Update the `b`-typed slot for `x` in `γ` to `v` (base-indexed view). -/
@[simp, reducible]
def REnv.update (b : Base) (γ : REnv) (x : EVar) (v : b.interp) : REnv :=
  γ.write x (Val.inj b v)

/-- Derived accessors mirroring the old two-field layout. -/
@[simp, reducible] def REnv.bools (γ : REnv) (x : EVar) : Bool := REnv.get .bool γ x

/-- The cell for `x` stores a value of base `b`. Holds for every slot bound at
    base `b` in a well-typed model; needed to know `update b _ x (get b _ x)`
    round-trips. -/
def REnv.HasBase (γ : REnv) (x : EVar) : Base → Prop
  | .int  => ∃ n, γ.map x = .iconst n
  | .bool => ∃ c, γ.map x = .bconst c
  | .tbvar _ => (∃ n, γ.map x = .iconst n) ∨ (∃ c, γ.map x = .bconst c)
  | .tfvar _ => (∃ n, γ.map x = .iconst n) ∨ (∃ c, γ.map x = .bconst c)


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
  | .data _ _ args => 1 + (List.ofFn fun i => (args i).skel).sum

/-- `Ty.data` from a list of type arguments. -/
@[simp, reducible] def Ty.dataL (C : String) (τs : List Ty) : Ty := .data C τs.length (fun i => τs[i])

/-! ## Datatype declarations

  A program is a list of datatype declarations (`DEnv`) followed by an
  expression. A declaration lists the kinds of its type parameters and its
  constructors, each with a single payload type. In a payload type, `tbvar i`
  is parameter `i`; a payload has no free term or type variables. -/

/-- The variance of a datatype parameter: how subtyping on the datatype
    follows subtyping on the argument. -/
inductive Variance where
  | co     : Variance
  | contra : Variance
  | inv    : Variance
  deriving Repr, DecidableEq

structure DataDecl where
  params : List Kind
  ctors  : List (String × Ty)
  /-- Declared variances of the parameters (checked against the payloads);
      a parameter without one is invariant. -/
  variances : List Variance := []

abbrev DEnv := List (String × DataDecl)

/-- The declaration of datatype `C`. -/
def DEnv.decl? (de : DEnv) (C : String) : Option DataDecl := de.lookup C

/-- The declared variance of parameter `i` of `C` (invariant by default). -/
def DEnv.var (de : DEnv) (C : String) (i : Nat) : Variance :=
  ((de.decl? C).bind fun d => d.variances[i]?).getD .inv

/-- The payload type of constructor `j` of `C`. -/
def DEnv.payload? (de : DEnv) (C : String) (j : Nat) : Option Ty :=
  (de.decl? C).bind fun d => (d.ctors[j]?).map Prod.snd

/-- Every element of a list of naturals is at most its sum. -/
theorem List.le_sum_of_mem_nat : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | _ :: _, _, .head _ => by simp only [List.sum_cons]; omega
  | y :: _, _, .tail _ h => by
      have := List.le_sum_of_mem_nat h
      simp only [List.sum_cons]; omega

theorem Ty.skel_data_lt (C : String) (n : Nat) (args : Fin n → Ty) (i : Fin n) :
    (args i).skel < (Ty.data C n args).skel := by
  have := List.le_sum_of_mem_nat (List.mem_ofFn.mpr ⟨i, rfl⟩ :
    (args i).skel ∈ List.ofFn fun i => (args i).skel)
  simp only [Ty.skel]; omega

end STLC
