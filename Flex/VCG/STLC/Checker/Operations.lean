import Flex.VCG.STLC.Spec.Logic
import Flex.VCG.STLC.Checker.Facts

open STLC

/-! # Syntactic operations used by the checker

  Free variables, opening and closing of term and type binders, sort
  substitution and type instantiation, freshness, the typing context `TEnv`,
  and the closing substitution `Exp.substEnv` used by the proofs. -/

namespace STLC



/-- Typing context: a list of free-name × type pairs. Names are unique by convention. -/
@[simp]
abbrev TEnv := List (EVar × Ty)

/-- Get all free names declared in a typing context. -/
def TEnv.dom : TEnv → List EVar
  | []          => []
  | (x, _) :: Γ => x :: TEnv.dom Γ


/-- Val-level (lossless) update of the name map: `write γ x (lookup γ x) = γ`
    unconditionally. Preserves the de Bruijn stack `bv`. -/
@[simp, reducible]
def REnv.write (γ : REnv) (x : EVar) (v : Val) : REnv :=
  { γ with map := fun y => if x == y then v else γ.map y }

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


/-- The declared variance of parameter `i` of `C` (invariant by default). -/
def DEnv.var (de : DEnv) (C : String) (i : Nat) : Variance :=
  ((de.decl? C).bind fun d => d.variances[i]?).getD .inv

/-! ## 1. Term operations -/

/-- Free variables of a term (includes `nuName` if present). -/
def Term.fv : {b : Base} → Term b → List EVar
  | _, .const _ _   => []
  | _, .bvar _ _    => []
  | _, .fvar _ x    => [x]
  | _, .add t₁ t₂   => Term.fv t₁ ++ Term.fv t₂
  | _, .mbvar _ _   => []
  | _, .mfvar _ x   => [x]
  | _, .ibvar _     => []
  | _, .bbvar _     => []
  | _, .not t       => Term.fv t
  | _, .and t₁ t₂   => Term.fv t₁ ++ Term.fv t₂
  | _, .leqI t₁ t₂  => Term.fv t₁ ++ Term.fv t₂
  | _, .ite _ c t e => Term.fv c ++ Term.fv t ++ Term.fv e

/-- Open the `BVar` at level `k` with a free var `x`, and
    *shift every deeper de Bruijn index down by one* (proper LN binder
    instantiation). -/
def Term.openBVar (k : Nat) (x : EVar) : {b : Base} → Term b → Term b
  | _, .const b c    => .const b c
  | _, .bvar b j     =>
      if j = k then .fvar b x else if k < j then .bvar b (j - 1) else .bvar b j
  | _, .fvar b y     => .fvar b y
  | _, .add t₁ t₂    => .add (Term.openBVar k x t₁) (Term.openBVar k x t₂)
  | _, .mbvar m j    =>
      if j = k then .mfvar m x else if k < j then .mbvar m (j - 1) else .mbvar m j
  | _, .mfvar m y    => .mfvar m y
  | _, .ibvar j      =>
      if j = k then .fvar .int x else if k < j then .ibvar (j - 1) else .ibvar j
  | _, .bbvar j      =>
      if j = k then .fvar .bool x else if k < j then .bbvar (j - 1) else .bbvar j
  | _, .not t        => .not (Term.openBVar k x t)
  | _, .and t₁ t₂    => .and (Term.openBVar k x t₁) (Term.openBVar k x t₂)
  | _, .leqI t₁ t₂   => .leqI (Term.openBVar k x t₁) (Term.openBVar k x t₂)
  | _, .ite b c t e  => .ite b (Term.openBVar k x c) (Term.openBVar k x t) (Term.openBVar k x e)

/-! ## 2. Formula operations -/

/-- Free variables of a formula. The quantifiers are locally nameless, so they
    bind no name and just pass their body's fv through. -/
def Formula.fv : Formula → List EVar
  | .tt           => []
  | .ff           => []
  | .eq _ t₁ t₂   => t₁.fv ++ t₂.fv
  | .leq _ t₁ t₂   => t₁.fv ++ t₂.fv
  | .and φ₁ φ₂    => Formula.fv φ₁ ++ Formula.fv φ₂
  | .or φ₁ φ₂     => Formula.fv φ₁ ++ Formula.fv φ₂
  | .not φ        => Formula.fv φ
  | .imp φ₁ φ₂    => Formula.fv φ₁ ++ Formula.fv φ₂
  | .ex _  φ      => Formula.fv φ
  | .all _ φ      => Formula.fv φ

/-- Open the `BVar` at level `k` with a free var `x` throughout `φ`, shifting
    deeper indices down (base-agnostic, see `Term.openBVar`). Crossing a
    quantifier binds a fresh innermost `BVar`, so the level bumps. -/
def Formula.openBVar (k : Nat) (x : EVar) : Formula → Formula
  | .tt           => .tt
  | .ff           => .ff
  | .eq b t₁ t₂   => .eq b (t₁.openBVar k x) (t₂.openBVar k x)
  | .leq b t₁ t₂   => .leq b (t₁.openBVar k x) (t₂.openBVar k x)
  | .and φ₁ φ₂    => .and (φ₁.openBVar k x) (φ₂.openBVar k x)
  | .or φ₁ φ₂     => .or (φ₁.openBVar k x) (φ₂.openBVar k x)
  | .not φ        => .not (φ.openBVar k x)
  | .imp φ₁ φ₂    => .imp (φ₁.openBVar k x) (φ₂.openBVar k x)
  | .ex b φ       => .ex b (φ.openBVar (k+1) x)
  | .all b φ      => .all b (φ.openBVar (k+1) x)

/-! ## 3. Refinement operations -/

/-- Free variables of a refinement. ν is a `BVar` (level 0), never an `fvar`,
    so the formula's fv already excludes it — no filtering needed. -/
def Refinement.fv (r : Refinement) : List EVar :=
  match r with
  | .fmla φ      => φ.fv
  | .kapp _ args => args.flatMap (fun a => Term.fv a.2)
  | .conj r₁ r₂  => Refinement.fv r₁ ++ Refinement.fv r₂

/-- Open the `BVar` at level `k` (base-agnostic, shifting; see `Term.openBVar`).
    ν-instantiation is the `k = 0` case: `r.openBVar 0 x` replaces ν (`bvar _ 0`)
    with the free name `x` and shifts deeper indices down. -/
def Refinement.openBVar (k : Nat) (x : EVar)
    (r : Refinement) : Refinement :=
  match r with
  | .fmla φ       => .fmla (φ.openBVar k x)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, Term.openBVar k x a.2⟩))
  | .conj r₁ r₂   => .conj (r₁.openBVar k x) (r₂.openBVar k x)

/-- Refinement type for an integer constant: `{ν : Int | ν = n}` (ν = `BVar 0`). -/
@[simp] def prim (n : Int) : Ty :=
  .refine .int (.fmla (.eq .int (.bvar .int 0) (.const .int n)))

/-- Refinement type for a boolean constant: `{ν : Bool | ν = b}` (ν = `BVar 0`). -/
@[simp] def primBool (b : Bool) : Ty :=
  .refine .bool (.fmla (.eq .bool (.bvar .bool 0) (.const .bool b)))

/-- `self x t` is the *singleton* refinement `{ν | ν = x}` against the stored
    value of `x` (selfification), with ν = `BVar 0`. The variable's own
    refinement is recovered from the typing context, so it is not re-conjoined
    here — keeping the synthesized type kvar-free. For function types, returns
    `t` unchanged. -/
@[simp] def self (de : DEnv) : EVar → Ty → Ty
  -- ⋆-kinded type variables are never compared (λ_RF's `self(_, _, ⋆)`)
  | _, .refine (.tfvar (a, .star)) r => .refine (.tfvar (a, .star)) r
  | x, .refine b _     => .refine b (.fmla (.eq b (.bvar b 0) (.fvar b x)))
  | _, .arrow t1 t2    => .arrow t1 t2
  | _, .forall k t     => .forall k t
  | _, .prod s t       => .prod s t
  -- a datatype value has no equality: it has the same measures as `x`
  | x, .data C n args _ => .data C n args (de.measEqs C x)

/-! ## 4. Ty operations (locally nameless)

  `Ty.openVar k x t` opens the `BVar` at level `k` to `fvar x` throughout
  refinements in `t`. Crossing a `Ty.arrow` binder bumps the level: `arrow`'s
  domain stays at the parent level, its codomain is at `k+1`.
-/

def Ty.fv : Ty → List EVar
  | .refine _ r => r.fv
  | .arrow s t  => Ty.fv s ++ Ty.fv t
  | .forall _ t => Ty.fv t
  | .prod s t   => Ty.fv s ++ Ty.fv t
  | .data _ n args r => ((List.finRange n).flatMap fun i => Ty.fv (args i)) ++ r.fv

/-- Open a `Ty`'s outermost binder at level `k` with free name `x`. Opens the
    refinement `BVar` at level `k+1` — the `+1` because ν occupies formula-level
    0, so arrow binders live one level out. One base-agnostic, shifting
    `openBVar` handles both bases at once. -/
def Ty.openVar (k : Nat) (x : EVar) : Ty → Ty
  | .refine b r => .refine b (r.openBVar (k+1) x)
  | .arrow s t  => .arrow (s.openVar k x) (t.openVar (k+1) x)
  | .forall κ t => .forall κ (t.openVar k x)
  | .prod s t   => .prod (s.openVar k x) (t.openVar (k+1) x)
  | .data C n args r => .data C n (fun i => (args i).openVar k x) (r.openBVar (k+1) x)

@[simp]
theorem Ty.skel_openVar (k : Nat) (x : EVar) (t : Ty) :
    (t.openVar k x).skel = t.skel := by
  induction t generalizing k with
  | refine _ _ => rfl
  | arrow s t ihs iht => simp [Ty.openVar, Ty.skel, ihs, iht]
  | «forall» _ t ih => simp [Ty.openVar, Ty.skel, ih]
  | prod s t ihs iht => simp [Ty.openVar, Ty.skel, ihs, iht]
  | data C n args r ih => simp [Ty.openVar, Ty.skel, ih]

/-! ### Well-formedness: BVar base consistency (WFBVarCtx)

  In coq-SystemRF, `WFtype` ensures that bound variables in predicate formulas
  match the base of the enclosing binder's domain type. In our system, this is
  `Ty.WFBVarCtx ctx t`: for each level `k`, all `BVar b k` in `t`'s refinement
  formulas have `ctx[k]? = some (some b)` (the k-th outer arrow binder's domain
  base). It drives `Ty.WFBVarCtx_openVar_last` (WFBVars is preserved by opening),
  which `subtyp_sound` threads through its arrow rule. -/

/-- `Term.hasBVar b k t`: t contains at least one `Term.bvar b k`. -/
def Term.hasBVar (b : Base) (k : Nat) : {b' : Base} → Term b' → Prop
  | _, .const _ _  => False
  | _, .bvar b' j  => b = b' ∧ k = j
  | _, .fvar _ _   => False
  | _, .add t₁ t₂  => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂
  | _, .mbvar _ _  => False
  | _, .mfvar _ _  => False
  | _, .ibvar _    => False
  | _, .bbvar _    => False
  | _, .not t      => Term.hasBVar b k t
  | _, .and t₁ t₂  => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂
  | _, .leqI t₁ t₂ => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂
  | _, .ite _ c t e => Term.hasBVar b k c ∨ Term.hasBVar b k t ∨ Term.hasBVar b k e

/-- `Formula.hasBVar b k φ`: φ contains at least one `Term.bvar b k`. -/
def Formula.hasBVar (b : Base) (k : Nat) : Formula → Prop
  | .tt | .ff => False
  | .eq _ t₁ t₂ | .leq _ t₁ t₂ =>
      Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂
  | .and φ₁ φ₂ | .or φ₁ φ₂ | .imp φ₁ φ₂ =>
      Formula.hasBVar b k φ₁ ∨ Formula.hasBVar b k φ₂
  | .not φ => Formula.hasBVar b k φ
  | .ex _ φ | .all _ φ =>
      -- each quantifier binds the innermost BVar, so outer levels shift up
      Formula.hasBVar b (k+1) φ

/-- `Refinement.hasBVar b k r`: r mentions `Term.bvar b k` — in its formula, or
    in the arguments of a κ-application. -/
def Refinement.hasBVar (b : Base) (k : Nat) (r : Refinement) : Prop :=
  match r with
  | .fmla φ      => Formula.hasBVar b k φ
  | .kapp _ args => ∃ a ∈ args, Term.hasBVar b k a.2
  | .conj r₁ r₂  => Refinement.hasBVar b k r₁ ∨ Refinement.hasBVar b k r₂

/-- `Term.hasMBVar k t`: t contains a measure application `m(BVar k)` (which
    reads the de Bruijn slot `k` whatever value it holds). -/
def Term.hasMBVar (k : Nat) : {b' : Base} → Term b' → Prop
  | _, .const _ _  => False
  | _, .bvar _ _   => False
  | _, .fvar _ _   => False
  | _, .add t₁ t₂  => Term.hasMBVar k t₁ ∨ Term.hasMBVar k t₂
  | _, .mbvar _ j  => k = j
  | _, .mfvar _ _  => False
  | _, .ibvar j    => k = j
  | _, .bbvar j    => k = j
  | _, .not t      => Term.hasMBVar k t
  | _, .and t₁ t₂  => Term.hasMBVar k t₁ ∨ Term.hasMBVar k t₂
  | _, .leqI t₁ t₂ => Term.hasMBVar k t₁ ∨ Term.hasMBVar k t₂
  | _, .ite _ c t e => Term.hasMBVar k c ∨ Term.hasMBVar k t ∨ Term.hasMBVar k e

def Formula.hasMBVar (k : Nat) : Formula → Prop
  | .tt | .ff => False
  | .eq _ t₁ t₂ | .leq _ t₁ t₂ => Term.hasMBVar k t₁ ∨ Term.hasMBVar k t₂
  | .and φ₁ φ₂ | .or φ₁ φ₂ | .imp φ₁ φ₂ => Formula.hasMBVar k φ₁ ∨ Formula.hasMBVar k φ₂
  | .not φ => Formula.hasMBVar k φ
  | .ex _ φ | .all _ φ => Formula.hasMBVar (k+1) φ

def Refinement.hasMBVar (k : Nat) (r : Refinement) : Prop :=
  match r with
  | .fmla φ      => Formula.hasMBVar k φ
  | .kapp _ args => ∃ a ∈ args, Term.hasMBVar k a.2
  | .conj r₁ r₂  => Refinement.hasMBVar k r₁ ∨ Refinement.hasMBVar k r₂

/-- Extract the base of a refinement type; None for arrow types. -/
def Ty.optBase : Ty → Option Base
  | .refine b _ => some b
  | .arrow _ _  => none
  | .forall _ _ => none
  | .prod _ _   => none
  | .data _ _ _ _ => none

/-- Shift the type-variable de Bruijn indices of a sort up by one (entering a
    `Ty.forall`). -/
def Base.shiftT : Base → Base
  | .tbvar j => .tbvar (j+1)
  | b        => b

/-! ## 4b. Type variables: sort substitution, opening, instantiation

  Type variables are sorts of the refinement logic, so substituting for a type
  variable has to *retype* the deep-embedded refinements: a `Term (tbvar k)`
  becomes a `Term b'`. A sort substitution `σ` acts on the type-variable sorts
  only and fixes `int`/`bool` *definitionally*, which is what lets
  `Term.substB` be defined by plain structural recursion. -/

/-- A sort substitution: acts on the type-variable sorts only. -/
structure BSubst where
  bv : Nat → Base
  fv : TVar → Base

def Base.substB (σ : BSubst) : Base → Base
  | .int     => .int
  | .bool    => .bool
  | .tbvar k => σ.bv k
  | .tfvar a => σ.fv a

/-- Literals only exist at `Int`/`Bool`, which sort substitutions fix. -/
@[reducible] def Base.constSubst (σ : BSubst) : (b : Base) → b.interp → (b.substB σ).interp
  | .int,     n => n
  | .bool,    c => c
  | .tbvar _, e => e.elim
  | .tfvar _, e => e.elim

/-- Retype a term along a sort substitution. -/
def Term.substB (σ : BSubst) : {b : Base} → Term b → Term (b.substB σ)
  | _, .const b c => .const _ (Base.constSubst σ b c)
  | _, .bvar _ k  => .bvar _ k
  | _, .fvar _ x  => .fvar _ x
  | _, .add t₁ t₂ => .add (Term.substB σ t₁) (Term.substB σ t₂)
  | _, .mbvar m k => .mbvar m k
  | _, .mfvar m x => .mfvar m x
  | _, .ibvar k   => .ibvar k
  | _, .bbvar k   => .bbvar k
  | _, .not t     => .not (Term.substB σ t)
  | _, .and t₁ t₂ => .and (Term.substB σ t₁) (Term.substB σ t₂)
  | _, .leqI t₁ t₂ => .leqI (Term.substB σ t₁) (Term.substB σ t₂)
  | _, .ite _ c t e => .ite _ (Term.substB σ c) (Term.substB σ t) (Term.substB σ e)

def Formula.substB (σ : BSubst) : Formula → Formula
  | .tt           => .tt
  | .ff           => .ff
  | .eq b t₁ t₂   => .eq (b.substB σ) (t₁.substB σ) (t₂.substB σ)
  | .leq b t₁ t₂   => .leq (b.substB σ) (t₁.substB σ) (t₂.substB σ)
  | .and φ₁ φ₂    => .and (φ₁.substB σ) (φ₂.substB σ)
  | .or φ₁ φ₂     => .or (φ₁.substB σ) (φ₂.substB σ)
  | .not φ        => .not (φ.substB σ)
  | .imp φ₁ φ₂    => .imp (φ₁.substB σ) (φ₂.substB σ)
  | .ex b φ       => .ex (b.substB σ) (φ.substB σ)
  | .all b φ      => .all (b.substB σ) (φ.substB σ)

def Refinement.substB (σ : BSubst) : Refinement → Refinement
  | .fmla φ       => .fmla (φ.substB σ)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1.substB σ, a.2.substB σ⟩))
  | .conj r₁ r₂   => .conj (r₁.substB σ) (r₂.substB σ)

/-- Replace type-binder level `k` by the sort `b'`, shifting deeper levels down
    by one (proper locally-nameless binder instantiation, as `Term.openBVar`). -/
def BSubst.instAt (k : Nat) (b' : Base) : BSubst :=
  ⟨fun j => if j = k then b' else if k < j then .tbvar (j - 1) else .tbvar j, .tfvar⟩

/-- Open type-binder level `k` with the free type variable `a`. -/
def BSubst.openAt (k : Nat) (a : TVar) : BSubst := BSubst.instAt k (.tfvar a)

/-- Open the type binder at level `k` with the free type variable `a`
    (locally nameless; levels bump under `Ty.forall`). -/
def Ty.openTv (k : Nat) (a : TVar) : Ty → Ty
  | .refine b r  => .refine (b.substB (BSubst.openAt k a)) (r.substB (BSubst.openAt k a))
  | .arrow s t   => .arrow (s.openTv k a) (t.openTv k a)
  | .forall κ t  => .forall κ (t.openTv (k+1) a)
  | .prod s t    => .prod (s.openTv k a) (t.openTv k a)
  | .data C n args r => .data C n (fun i => (args i).openTv k a) (r.substB (BSubst.openAt k a))

@[simp] theorem Ty.skel_openTv (k : Nat) (a : TVar) (t : Ty) :
    (t.openTv k a).skel = t.skel := by
  induction t generalizing k <;> simp_all [Ty.openTv, Ty.skel]

/-- The sort a type contributes when it instantiates a type variable (only
    meaningful for refined base types; arbitrary otherwise — no refinement can
    mention a ⋆-kinded variable). -/
def Ty.sortOf : Ty → Base
  | .refine b _ => b
  | _           => .int

/-- λ_RF's `refine(s, r)`: conjoin `r` into the top-level refinement of a
    refined base type; other types (instances of ⋆-kinded variables, refined
    only with `true`) are returned unchanged. -/
def Ty.strengthen (s : Ty) (r : Refinement) : Ty :=
  match s with
  | .refine b r' => .refine b (.conj r' r)
  | s            => s

/-- T-TApp's substitution `t[s/α]` for the type binder at level `k`: retype every
    refinement along `α ↦ sortOf s`, and replace each `α{r}` by `refine(s, r)`. -/
def Ty.instTy (k : Nat) (s : Ty) : Ty → Ty
  | .refine b r  =>
      if b = .tbvar k then s.strengthen (r.substB (BSubst.instAt k s.sortOf))
      else .refine (b.substB (BSubst.instAt k s.sortOf)) (r.substB (BSubst.instAt k s.sortOf))
  | .arrow t₁ t₂ => .arrow (Ty.instTy k s t₁) (Ty.instTy k s t₂)
  | .forall κ t  => .forall κ (Ty.instTy (k+1) s t)
  | .prod t₁ t₂  => .prod (Ty.instTy k s t₁) (Ty.instTy k s t₂)
  | .data C n args r =>
      .data C n (fun i => Ty.instTy k s (args i)) (r.substB (BSubst.instAt k s.sortOf))

/-- The kind of a type: refined `Int`/`Bool` and `B`-kinded type variables are
    base (`B`); everything else is `⋆`. -/
def Ty.kindOf : Ty → Kind
  | .refine .int _               => .B
  | .refine .bool _              => .B
  | .refine (.tfvar (_, κ)) _    => κ
  | _                            => .star

/-- Kind ordering: `B ≤ ⋆` (a base type may instantiate a ⋆-kinded variable). -/
def Kind.le (k₁ k₂ : Kind) : Prop := k₁ = .B ∨ k₂ = .star

instance (k₁ k₂ : Kind) : Decidable (Kind.le k₁ k₂) := by
  unfold Kind.le; infer_instance

/-! ### Generalization: closing a free type variable

  `Ty.closeTv k a` abstracts the free type variable `a` as the type binder at
  level `k` (shifting deeper levels up) — the inverse of `Ty.openTv`. `Ty.gen as t`
  quantifies `t` over the type variables `as`: it is how a recursive function's
  own name gets a polymorphic type (polymorphic recursion). -/

def BSubst.closeAt (k : Nat) (a : TVar) : BSubst :=
  ⟨fun j => if k ≤ j then .tbvar (j+1) else .tbvar j,
   fun a' => if a' = a then .tbvar k else .tfvar a'⟩

def Ty.closeTv (k : Nat) (a : TVar) : Ty → Ty
  | .refine b r  => .refine (b.substB (BSubst.closeAt k a)) (r.substB (BSubst.closeAt k a))
  | .arrow s t   => .arrow (s.closeTv k a) (t.closeTv k a)
  | .forall κ t  => .forall κ (t.closeTv (k+1) a)
  | .prod s t    => .prod (s.closeTv k a) (t.closeTv k a)
  | .data C n args r => .data C n (fun i => (args i).closeTv k a) (r.substB (BSubst.closeAt k a))

/-- `∀ as. t`, outermost first. -/
@[simp] def Ty.gen : List TVar → Ty → Ty
  | [],      t => t
  | a :: as, t => .forall a.2 ((Ty.gen as t).closeTv 0 a)

/-! ### Free type variables and fresh type-variable names

  Free type variables can occur in the sorts of deep-embedded terms, so `ftv`
  traverses refinements too. -/

def Base.ftv : Base → List TVar
  | .tfvar a => [a]
  | _        => []

def Term.ftv : {b : Base} → Term b → List TVar
  | _, .const b _  => b.ftv
  | _, .bvar b _   => b.ftv
  | _, .fvar b _   => b.ftv
  | _, .add t₁ t₂  => Term.ftv t₁ ++ Term.ftv t₂
  | _, .mbvar _ _  => []
  | _, .mfvar _ _  => []
  | _, .ibvar _    => []
  | _, .bbvar _    => []
  | _, .not t      => Term.ftv t
  | _, .and t₁ t₂  => Term.ftv t₁ ++ Term.ftv t₂
  | _, .leqI t₁ t₂ => Term.ftv t₁ ++ Term.ftv t₂
  | _, .ite _ c t e => Term.ftv c ++ Term.ftv t ++ Term.ftv e

def Formula.ftv : Formula → List TVar
  | .tt | .ff     => []
  | .eq b t₁ t₂   => b.ftv ++ t₁.ftv ++ t₂.ftv
  | .leq b t₁ t₂   => b.ftv ++ t₁.ftv ++ t₂.ftv
  | .and φ₁ φ₂ | .or φ₁ φ₂ | .imp φ₁ φ₂ => φ₁.ftv ++ φ₂.ftv
  | .not φ        => φ.ftv
  | .ex b φ | .all b φ => b.ftv ++ φ.ftv

def Refinement.ftv : Refinement → List TVar
  | .fmla φ      => φ.ftv
  | .kapp _ args => args.flatMap (fun a => a.1.ftv ++ a.2.ftv)
  | .conj r₁ r₂  => r₁.ftv ++ r₂.ftv

def Ty.ftv : Ty → List TVar
  | .refine b r  => b.ftv ++ r.ftv
  | .arrow s t   => s.ftv ++ t.ftv
  | .forall _ t  => t.ftv
  | .prod s t    => s.ftv ++ t.ftv
  | .data _ n args r => ((List.finRange n).flatMap fun i => (args i).ftv) ++ r.ftv

/-! ## 5. Exp operations (locally nameless) -/

/-- Replace `bvar k` with `fvar x` (used when entering a binder). -/
def Exp.openVar (k : Nat) (x : EVar) : Exp → Exp
  | .bvar j        => if j = k then .fvar x else .bvar j
  | .fvar y        => .fvar y
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .lam body      => .lam (body.openVar (k+1) x)
  | .letin e₁ e₂   => .letin (e₁.openVar k x) (e₂.openVar (k+1) x)
  | .app e₁ e₂     => .app (e₁.openVar k x) (e₂.openVar k x)
  | .ann e t       => .ann (e.openVar k x) t
  | .and e₁ e₂     => .and (e₁.openVar k x) (e₂.openVar k x)
  | .not e         => .not (e.openVar k x)
  | .leq e₁ e₂     => .leq (e₁.openVar k x) (e₂.openVar k x)
  | .ite e₀ e₁ e₂  => .ite (e₀.openVar k x) (e₁.openVar k x) (e₂.openVar k x)
  | .add e₁ e₂     => .add (e₁.openVar k x) (e₂.openVar k x)
  | .unreach       => .unreach
  | .fix body      => .fix (body.openVar (k+2) x)
  | .tabs κ e      => .tabs κ (e.openVar k x)
  -- the instance may mention enclosing term binders: open them too
  | .tapp e t      => .tapp (e.openVar k x) (t.openVar k x)
  | .pair e₁ e₂    => .pair (e₁.openVar k x) (e₂.openVar k x)
  | .split e₁ e₂   => .split (e₁.openVar k x) (e₂.openVar (k+2) x)
  -- the instance may mention enclosing term binders: open them too
  | .ctor C j τs e => .ctor C j (τs.map (Ty.openVar k x)) (e.openVar k x)
  | .case e n alts => .case (e.openVar k x) n (fun j => (alts j).openVar (k+1) x)

/-- Structural skeleton size: counts constructor depth, ignoring leaf details
    (so `Exp.skel` is preserved under `openVar` / `subst`). Used as a
    termination measure for algorithmic functions in `Checker/VCGen.lean`. -/
@[simp]
def Exp.skel : Exp → Nat
  | .bvar _        => 0
  | .fvar _        => 0
  | .iconst _      => 0
  | .bconst _      => 0
  | .lam body      => 1 + body.skel
  | .letin e₁ e₂   => 1 + e₁.skel + e₂.skel
  | .app e₁ e₂     => 1 + e₁.skel + e₂.skel
  | .ann e _       => 1 + e.skel
  | .and e₁ e₂     => 1 + e₁.skel + e₂.skel
  | .not e         => 1 + e.skel
  | .leq e₁ e₂     => 1 + e₁.skel + e₂.skel
  | .ite e₀ e₁ e₂  => 1 + e₀.skel + e₁.skel + e₂.skel
  | .add e₁ e₂     => 1 + e₁.skel + e₂.skel
  | .unreach       => 0
  | .fix body      => 1 + body.skel
  | .tabs _ e      => 1 + e.skel
  | .tapp e _      => 1 + e.skel
  | .pair e₁ e₂    => 1 + e₁.skel + e₂.skel
  | .split e₁ e₂   => 1 + e₁.skel + e₂.skel
  | .ctor _ _ _ e  => 1 + e.skel
  | .case e _ alts => 1 + e.skel + (List.ofFn fun j => (alts j).skel).sum

theorem Exp.skel_case_lt (e : Exp) (n : Nat) (alts : Fin n → Exp) (j : Fin n) :
    (alts j).skel < (Exp.case e n alts).skel := by
  have := List.le_sum_of_mem_nat (List.mem_ofFn.mpr ⟨j, rfl⟩ :
    (alts j).skel ∈ List.ofFn fun j => (alts j).skel)
  simp only [Exp.skel]; omega

@[simp]
theorem Exp.skel_openVar (k : Nat) (x : EVar) (e : Exp) :
    (e.openVar k x).skel = e.skel := by
  induction e generalizing k with
  | bvar j        => simp [Exp.openVar]; split <;> rfl
  | fvar _        => rfl
  | iconst _      => rfl
  | bconst _      => rfl
  | lam _ ih      => simp [Exp.openVar, Exp.skel, ih]
  | letin _ _ ih₁ ih₂  => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | app _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | ann _ _ ih | tapp _ _ ih | tabs _ _ ih => simp [Exp.openVar, Exp.skel, ih]
  | and _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | not _ ih           => simp [Exp.openVar, Exp.skel, ih]
  | leq _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | ite _ _ _ ih₀ ih₁ ih₂ => simp [Exp.openVar, Exp.skel, ih₀, ih₁, ih₂]
  | add _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | unreach            => rfl
  | fix _ ih           => simp [Exp.openVar, Exp.skel, ih]
  | pair _ _ ih₁ ih₂ | split _ _ ih₁ ih₂ => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | ctor _ _ _ _ ih    => simp [Exp.openVar, Exp.skel, ih]
  | case _ _ _ ih ihs  => simp [Exp.openVar, Exp.skel, ih, ihs]

/-- Open the type binder at level `k` with the free type variable `a` inside the
    type annotations of an expression (levels bump under `Exp.tabs`). -/
def Exp.openTv (k : Nat) (a : TVar) : Exp → Exp
  | .bvar j        => .bvar j
  | .fvar y        => .fvar y
  | .iconst n      => .iconst n
  | .bconst b      => .bconst b
  | .lam body      => .lam (body.openTv k a)
  | .letin e₁ e₂   => .letin (e₁.openTv k a) (e₂.openTv k a)
  | .app e₁ e₂     => .app (e₁.openTv k a) (e₂.openTv k a)
  | .ann e t       => .ann (e.openTv k a) (t.openTv k a)
  | .and e₁ e₂     => .and (e₁.openTv k a) (e₂.openTv k a)
  | .not e         => .not (e.openTv k a)
  | .leq e₁ e₂     => .leq (e₁.openTv k a) (e₂.openTv k a)
  | .ite e₀ e₁ e₂  => .ite (e₀.openTv k a) (e₁.openTv k a) (e₂.openTv k a)
  | .add e₁ e₂     => .add (e₁.openTv k a) (e₂.openTv k a)
  | .unreach       => .unreach
  | .fix body      => .fix (body.openTv k a)
  | .tabs κ e      => .tabs κ (e.openTv (k+1) a)
  | .tapp e t      => .tapp (e.openTv k a) (t.openTv k a)
  | .pair e₁ e₂    => .pair (e₁.openTv k a) (e₂.openTv k a)
  | .split e₁ e₂   => .split (e₁.openTv k a) (e₂.openTv k a)
  | .ctor C j τs e => .ctor C j (τs.map (Ty.openTv k a)) (e.openTv k a)
  | .case e n alts => .case (e.openTv k a) n (fun j => (alts j).openTv k a)

@[simp] theorem Exp.skel_openTv (k : Nat) (a : TVar) (e : Exp) :
    (e.openTv k a).skel = e.skel := by
  induction e generalizing k <;> simp_all [Exp.openTv, Exp.skel]

/-! ## 7. TEnv free variables -/

/-- Flat union of all type free-variables in Γ (no scoping filter). Used for
    freshness conditions: x ∉ TEnv.tyFv Γ ↔ ∀ (y,t) ∈ Γ, x ∉ t.fv. -/
def TEnv.tyFv : TEnv → List EVar
  | []          => []
  | (_, t) :: Γ => t.fv ++ TEnv.tyFv Γ


/-! ## 8. Closing substitution (for big-step / fundamental lemma) -/

/-- Closing substitution driven by the runtime environment `γ`. Since `γ` is a
    *total* function `EVar → Val`, this is a structural *simultaneous* value
    substitution: every free name `x` is replaced by `(γ.map x).toExp`. No domain
    is needed — on a well-typed term every free name is bound in the model, and
    the `iconst 0` default never occurs at a name that is actually read.-/
def Exp.substEnv (γ : REnv) : Exp → Exp
  | .bvar j       => .bvar j
  | .fvar x       => (γ.map x).toExp
  | .iconst n     => .iconst n
  | .bconst b     => .bconst b
  | .lam body     => .lam (Exp.substEnv γ body)
  | .letin e₁ e₂  => .letin (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .app e₁ e₂    => .app (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .ann e t      => .ann (Exp.substEnv γ e) t
  | .add e₁ e₂    => .add (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .leq e₁ e₂    => .leq (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .not e        => .not (Exp.substEnv γ e)
  | .and e₁ e₂    => .and (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .ite e₀ e₁ e₂ => .ite (Exp.substEnv γ e₀) (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .unreach      => .unreach
  | .fix body     => .fix (Exp.substEnv γ body)
  | .tabs κ e     => .tabs κ (Exp.substEnv γ e)
  -- types are erased before running, so the closing substitution drops instances
  | .tapp e _     => .tapp (Exp.substEnv γ e) (.refine .int (.fmla .tt))
  | .pair e₁ e₂   => .pair (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .split e₁ e₂  => .split (Exp.substEnv γ e₁) (Exp.substEnv γ e₂)
  | .ctor C j _ e  => .ctor C j [] (Exp.substEnv γ e)
  | .case e n alts => .case (Exp.substEnv γ e) n (fun j => Exp.substEnv γ (alts j))

/-- Free type variables of the type annotations in an expression. -/
def Exp.ftv : Exp → List TVar
  | .bvar _ | .fvar _ | .iconst _ | .bconst _ | .unreach => []
  | .lam b | .not b | .fix b | .tabs _ b => b.ftv
  | .letin e₁ e₂ | .app e₁ e₂ | .and e₁ e₂ | .leq e₁ e₂ | .add e₁ e₂
  | .pair e₁ e₂ | .split e₁ e₂ => e₁.ftv ++ e₂.ftv
  | .ite e₀ e₁ e₂ => e₀.ftv ++ e₁.ftv ++ e₂.ftv
  | .ann e t | .tapp e t => e.ftv ++ t.ftv
  | .ctor _ _ τs e => τs.flatMap Ty.ftv ++ e.ftv
  | .case e n alts => e.ftv ++ (List.finRange n).flatMap fun j => (alts j).ftv

/-- Free type variables of the types in a context. -/
def TEnv.ftv : TEnv → List TVar
  | []          => []
  | (_, t) :: Γ => t.ftv ++ TEnv.ftv Γ

/-- The type variables of `t` that the context does not mention (in order of
    first occurrence): those a recursive function's own name is generalized over. -/
def TEnv.genVars (Γ : TEnv) (t : Ty) : List TVar :=
  (t.ftv.filter (fun a => a ∉ TEnv.ftv Γ)).eraseDups

/-- Does `e` instantiate the variable `f` at a type (`f[τ]`)? -/
@[simp] def Exp.tappsVar (f : EVar) : Exp → Bool
  | .bvar _ | .fvar _ | .iconst _ | .bconst _ | .unreach => false
  | .lam e | .not e | .fix e | .tabs _ e | .ann e _ | .ctor _ _ _ e => e.tappsVar f
  | .letin e₁ e₂ | .app e₁ e₂ | .and e₁ e₂ | .leq e₁ e₂ | .add e₁ e₂ | .pair e₁ e₂
  | .split e₁ e₂ => e₁.tappsVar f || e₂.tappsVar f
  | .ite e₀ e₁ e₂ => e₀.tappsVar f || e₁.tappsVar f || e₂.tappsVar f
  | .tapp (.fvar g) _ => g == f
  | .tapp e _ => e.tappsVar f
  | .case e n alts => e.tappsVar f || (List.finRange n).any (fun j => (alts j).tappsVar f)

/-! ## 9. Freshness helper

  `EVar.fresh L` returns a name not in `L`, by producing a string longer than
  any element of `L`. The freshness proof lives in Stage 2b. -/

def EVar.maxLen : List EVar → Nat
  | []      => 0
  | x :: xs => Nat.max x.length (EVar.maxLen xs)

def EVar.fresh (L : List EVar) : EVar :=
  String.ofList (List.replicate (EVar.maxLen L + 1) 'x')

/-- A type-variable name with the given kind, fresh for `L` (by name). -/
def TVar.fresh (L : List TVar) (κ : Kind) : TVar :=
  (EVar.fresh (L.map Prod.fst), κ)

/-! ## Datatype instantiation

  A constructor's payload type mentions the datatype's parameters as `tbvar i`.
  Instantiating it at the type arguments `τs` substitutes the outermost
  parameter first, so that every step is an `instTy` of the outermost free type
  variable (the shape the semantic substitution lemma handles). -/

/-- `instTysFrom i τs P` instantiates parameters `i, i+1, …` of `P` by `τs`. -/
def Ty.instTysFrom (i : Nat) : List Ty → Ty → Ty
  | [],      P => P
  | τ :: τs, P => Ty.instTy i τ (Ty.instTysFrom (i+1) τs P)

/-- The payload `P` at the type arguments `τs`. -/
@[reducible] def Ty.instTys (τs : List Ty) (P : Ty) : Ty := Ty.instTysFrom 0 τs P

end STLC
