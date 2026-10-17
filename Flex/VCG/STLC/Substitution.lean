import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Model

namespace STLC

/-! ## 1. Term operations -/

/-- Free variables of a term (includes `nuName` if present). -/
def Term.fv : {b : Base} → Term b → List EVar
  | _, .const _ _   => []
  | _, .bvar _ _    => []
  | _, .fvar _ x    => [x]
  | _, .add t₁ t₂   => Term.fv t₁ ++ Term.fv t₂
  | _, .mbvar _ _   => []
  | _, .mfvar _ x   => [x]
  | _, .not t       => Term.fv t
  | _, .and t₁ t₂   => Term.fv t₁ ++ Term.fv t₂

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
  | _, .not t        => .not (Term.openBVar k x t)
  | _, .and t₁ t₂    => .and (Term.openBVar k x t₁) (Term.openBVar k x t₂)

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
@[simp] def self : EVar → Ty → Ty
  -- ⋆-kinded type variables are never compared (λ_RF's `self(_, _, ⋆)`)
  | _, .refine (.tfvar (a, .star)) r => .refine (.tfvar (a, .star)) r
  | x, .refine b _     => .refine b (.fmla (.eq b (.bvar b 0) (.fvar b x)))
  | _, .arrow t1 t2    => .arrow t1 t2
  | _, .forall k t     => .forall k t
  | _, .prod s t       => .prod s t
  | _, .data C n args r => .data C n args r

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

theorem Term.fv_openBVar {k : Nat} {x z : EVar} : ∀ {b : Base} (t : Term b),
    z ∈ (t.openBVar k x).fv → z ∈ t.fv ∨ z = x := by
  intro b t
  induction t with
  | bvar b j =>
    simp only [Term.openBVar]
    split
    · simp [Term.fv]
    · split <;> simp [Term.fv]
  | const => simp [Term.openBVar, Term.fv]
  | fvar => simp only [Term.openBVar, Term.fv, List.mem_singleton]; exact Or.inl
  | mbvar m j =>
    simp only [Term.openBVar]
    split
    · simp [Term.fv]
    · split <;> simp [Term.fv]
  | mfvar => simp only [Term.openBVar, Term.fv, List.mem_singleton]; exact Or.inl
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ =>
    simp only [Term.openBVar, Term.fv, List.mem_append]
    rintro (h | h)
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | not _ ih => simpa [Term.openBVar, Term.fv] using ih

theorem Formula.fv_openBVar {x z : EVar} (φ : Formula) : ∀ {k : Nat},
    z ∈ (φ.openBVar k x).fv → z ∈ φ.fv ∨ z = x := by
  induction φ with
  | tt | ff => simp [Formula.openBVar, Formula.fv]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro k
    simp only [Formula.openBVar, Formula.fv, List.mem_append]
    rintro (h | h)
    · rcases Term.fv_openBVar t₁ h with h | h <;> simp [h]
    · rcases Term.fv_openBVar t₂ h with h | h <;> simp [h]
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro k
    simp only [Formula.openBVar, Formula.fv, List.mem_append]
    rintro (h | h)
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | not _ ih | ex _ _ ih | all _ _ ih => intro k h; exact ih h

theorem Refinement.fv_openBVar {k : Nat} {x z : EVar} (r : Refinement) :
    z ∈ (r.openBVar k x).fv → z ∈ r.fv ∨ z = x := by
  induction r with
  | fmla φ => exact Formula.fv_openBVar φ
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.fv, List.flatMap_map, List.mem_flatMap]
    rintro ⟨a, ha, h⟩
    rcases Term.fv_openBVar a.2 h with h | h
    · exact Or.inl ⟨a, ha, h⟩
    · exact Or.inr h
  | conj _ _ ih₁ ih₂ =>
    simp only [Refinement.openBVar, Refinement.fv, List.mem_append]
    rintro (h | h)
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]

theorem Ty.fv_openVar {x z : EVar} (t : Ty) : ∀ {k : Nat},
    z ∈ (t.openVar k x).fv → z ∈ t.fv ∨ z = x := by
  induction t with
  | refine b r => intro k h; exact Refinement.fv_openBVar r h
  | arrow _ _ ih₁ ih₂ | prod _ _ ih₁ ih₂ =>
    intro k
    simp only [Ty.openVar, Ty.fv, List.mem_append]
    rintro (h | h)
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | «forall» _ _ ih => intro k h; exact ih h
  | data C n args r ih =>
    intro k
    simp only [Ty.openVar, Ty.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
    rintro (⟨i, h⟩ | h)
    · rcases ih i h with h | h
      · exact Or.inl (Or.inl ⟨i, h⟩)
      · exact Or.inr h
    · rcases Refinement.fv_openBVar r h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

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
  | _, .not t      => Term.hasBVar b k t
  | _, .and t₁ t₂  => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂

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
  | _, .not t      => Term.hasMBVar k t
  | _, .and t₁ t₂  => Term.hasMBVar k t₁ ∨ Term.hasMBVar k t₂

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

/-- `Ty.WFBVarCtx ctx t`: at nesting depth k, all `BVar b k` in `t`'s
    refinement formulas satisfy `(some bᵣ :: ctx)[k]? = some (some b)`, where
    `bᵣ` is the refinement's own base. Level 0 is ν (always base `bᵣ`); level
    `k+1` is the k-th outer arrow binder (`ctx[k]`). -/
def Ty.WFBVarCtx : List (Option Base) → Ty → Prop
  | ctx, .refine br r =>
      ∀ (b : Base) (k : Nat), Refinement.hasBVar b k r → (some br :: ctx)[k]? = some (some b)
  | ctx, .arrow s t  =>
      Ty.WFBVarCtx ctx s ∧ Ty.WFBVarCtx (s.optBase :: ctx) t
  -- no term binder; the recorded sorts are re-expressed under the new type binder
  | ctx, .forall _ t =>
      Ty.WFBVarCtx (ctx.map (Option.map Base.shiftT)) t
  | ctx, .prod s t  =>
      Ty.WFBVarCtx ctx s ∧ Ty.WFBVarCtx (s.optBase :: ctx) t
  -- ν is a datatype value (no sort): only measures may observe it
  | ctx, .data _ _ args r =>
      (∀ (b : Base) (k : Nat), Refinement.hasBVar b k r → (none :: ctx)[k]? = some (some b)) ∧
      ∀ i, Ty.WFBVarCtx ctx (args i)

/-- Shorthand: `t` is well-formed with no outer binders. -/
def Ty.WFBVars (t : Ty) : Prop := Ty.WFBVarCtx [] t

/-- A typing context is WFBVars iff every binding's type is `Ty.WFBVars`. (With
    ν locally nameless there is no reserved name to keep out of the domain.) -/
def TEnv.WFBVars (Γ : TEnv) : Prop :=
  ∀ x t, (x, t) ∈ Γ → Ty.WFBVars t

/-- All type annotations syntactically present in `e` are `Ty.WFBVars`.
    Used as a precondition on soundness theorems so the `.ann` case has the
    WFBVars evidence to construct the corresponding `Hastype` node. -/
def Exp.WFBVars : Exp → Prop
  | .bvar _ | .fvar _ | .iconst _ | .bconst _ | .unreach => True
  | .lam e        => Exp.WFBVars e
  | .letin e₁ e₂  => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .app e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .ann e t      => Ty.WFBVars t ∧ Exp.WFBVars e
  | .and e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .not e        => Exp.WFBVars e
  | .leq e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .ite e₀ e₁ e₂ => Exp.WFBVars e₀ ∧ Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .add e₁ e₂    => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .fix e        => Exp.WFBVars e
  | .tabs _ e     => Exp.WFBVars e
  -- the instance is checked by `Ty.wfB` (after opening) instead
  | .tapp e _     => Exp.WFBVars e
  | .pair e₁ e₂   => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  | .split e₁ e₂  => Exp.WFBVars e₁ ∧ Exp.WFBVars e₂
  -- instances are checked by `DEnv.instOK` (after opening) instead
  | .ctor _ _ _ e  => Exp.WFBVars e
  | .case e _ alts => Exp.WFBVars e ∧ ∀ j, Exp.WFBVars (alts j)

theorem TEnv.WFBVars.empty : TEnv.WFBVars [] := by intros x t h ; trivial

/-- Cons preserves `TEnv.WFBVars` given the new binding has WFBVars type. -/
theorem TEnv.WFBVars.cons {Γ : TEnv} {x : EVar} {t : Ty}
    (hΓ : TEnv.WFBVars Γ) (ht : Ty.WFBVars t) :
    TEnv.WFBVars ((x, t) :: Γ) := by
  intro y s h
  simp only [List.mem_cons, Prod.mk.injEq] at h
  rcases h with ⟨_, hst⟩ | h
  · exact hst ▸ ht
  · exact hΓ y s h

/-- Lookup in a WFBVars context yields a WFBVars type. -/
theorem TEnv.WFBVars.lookup {Γ : TEnv} (hΓ : TEnv.WFBVars Γ) {x : EVar} {t : Ty}
    (hlk : Γ.lookup x = some t) : Ty.WFBVars t := by
  induction Γ with
  | nil => simp [List.lookup] at hlk
  | cons hd tl ih =>
    obtain ⟨y, s⟩ := hd
    simp only [List.lookup] at hlk
    by_cases hxy : x = y
    · have heq : (x == y) = true := by simp [hxy]
      rw [heq] at hlk
      have hst : s = t := Option.some.inj hlk
      subst hst
      exact hΓ y s (by simp)
    · have hne : (x == y) = false := by simp [hxy]
      rw [hne] at hlk
      have hΓ_tl : TEnv.WFBVars tl := fun z r h => hΓ z r (by simp [List.mem_cons, h])
      exact ih hΓ_tl hlk

/-! ### `hasBVar` under the shifting open

  A `BVar b i` occurs in `t.openBVar k x` iff it came from level `i` (below the
  opened level `k`) or from level `i+1` (at/above `k`, shifted down). This
  characterization drives `Ty.WFBVarCtx_openVar_last`. -/

theorem Term.hasBVar_openBVar {b'' : Base} (t : Term b'') (b : Base) (i k : Nat) (x : EVar) :
    Term.hasBVar b i (Term.openBVar k x t) ↔
      (i < k ∧ Term.hasBVar b i t) ∨ (k ≤ i ∧ Term.hasBVar b (i+1) t) := by
  induction t with
  | const _ _ => simp [Term.openBVar, Term.hasBVar]
  | bvar b' j =>
    by_cases hbb : b = b'
    · subst hbb
      by_cases hjk : j = k
      · subst hjk; simp [Term.openBVar, Term.hasBVar]; omega
      · by_cases hlt : k < j
        · simp [Term.openBVar, hjk, hlt, Term.hasBVar]; omega
        · simp [Term.openBVar, hjk, hlt, Term.hasBVar]; omega
    · by_cases hjk : j = k
      · subst hjk; simp [Term.openBVar, Term.hasBVar, hbb]
      · by_cases hlt : k < j
        · simp [Term.openBVar, hjk, hlt, Term.hasBVar, hbb]
        · simp [Term.openBVar, hjk, hlt, Term.hasBVar, hbb]
  | fvar _ _ => simp [Term.openBVar, Term.hasBVar]
  | mbvar m j => simp only [Term.openBVar]; split <;> (try split) <;> simp [Term.hasBVar]
  | mfvar _ _ => simp [Term.openBVar, Term.hasBVar]
  | add t₁ t₂ ih1 ih2 => simp only [Term.openBVar, Term.hasBVar, ih1, ih2]; grind
  | not t ih  => simp only [Term.openBVar, Term.hasBVar, ih]
  | and t₁ t₂ ih1 ih2 => simp only [Term.openBVar, Term.hasBVar, ih1, ih2]; grind

theorem Formula.hasBVar_openBVar (φ : Formula) (b : Base) (i k : Nat) (x : EVar) :
    Formula.hasBVar b i (φ.openBVar k x) ↔
      (i < k ∧ Formula.hasBVar b i φ) ∨ (k ≤ i ∧ Formula.hasBVar b (i+1) φ) := by
  induction φ generalizing i k with
  | tt | ff => simp [Formula.hasBVar, Formula.openBVar]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    simp only [Formula.hasBVar, Formula.openBVar, Term.hasBVar_openBVar]; grind
  | and φ₁ φ₂ ih1 ih2 | or φ₁ φ₂ ih1 ih2 | imp φ₁ φ₂ ih1 ih2 =>
    simp only [Formula.hasBVar, Formula.openBVar, ih1, ih2]; grind
  | not φ ih => simp only [Formula.hasBVar, Formula.openBVar, ih]
  | ex _ φ ih | all _ φ ih =>
    simp only [Formula.hasBVar, Formula.openBVar]
    rw [ih (i+1) (k+1)]
    exact or_congr (and_congr (by omega) Iff.rfl) (and_congr (by omega) Iff.rfl)

theorem Refinement.hasBVar_openBVar (r : Refinement) (b : Base) (i k : Nat) (x : EVar) :
    Refinement.hasBVar b i (r.openBVar k x) ↔
      (i < k ∧ Refinement.hasBVar b i r) ∨ (k ≤ i ∧ Refinement.hasBVar b (i+1) r) := by
  induction r with
  | conj r₁ r₂ ih1 ih2 =>
    simp only [Refinement.openBVar, Refinement.hasBVar, ih1, ih2]; grind
  | fmla φ => exact Formula.hasBVar_openBVar φ b i k x
  | kapp kn args =>
    simp only [Refinement.openBVar, Refinement.hasBVar]
    constructor
    · rintro ⟨a, hmem, hbv⟩
      simp only [List.mem_map] at hmem
      obtain ⟨a', hmem', rfl⟩ := hmem
      rcases (Term.hasBVar_openBVar a'.2 b i k x).mp hbv with ⟨hlt, h⟩ | ⟨hle, h⟩
      · exact Or.inl ⟨hlt, a', hmem', h⟩
      · exact Or.inr ⟨hle, a', hmem', h⟩
    · have hmk : ∀ a ∈ args, (⟨a.1, Term.openBVar k x a.2⟩ : Σ b : Base, Term b)
          ∈ args.map (fun a => ⟨a.1, Term.openBVar k x a.2⟩) :=
        fun a ha => by simp only [List.mem_map]; exact ⟨a, ha, rfl⟩
      rintro (⟨hlt, a, hmem, h⟩ | ⟨hle, a, hmem, h⟩)
      · exact ⟨_, hmk a hmem, (Term.hasBVar_openBVar a.2 b i k x).mpr (Or.inl ⟨hlt, h⟩)⟩
      · exact ⟨_, hmk a hmem, (Term.hasBVar_openBVar a.2 b i k x).mpr (Or.inr ⟨hle, h⟩)⟩

/-- `optBase` is unchanged by `openVar` (shape refine/arrow is preserved). -/
theorem Ty.optBase_openVar (t : Ty) (k : Nat) (y : EVar) :
    (t.openVar k y).optBase = t.optBase := by
  cases t <;> simp [Ty.openVar, Ty.optBase]

/-- Opening at level `ctx.length` (the last binder position) consumes the last
    context entry. For the `app` case use ctx = [], opt = s.optBase:
    `WFBVarCtx [s.optBase] t → WFBVarCtx [] (t.openVar 0 y)`. -/
theorem Ty.WFBVarCtx_openVar_last (t : Ty) (ctx : List (Option Base)) (opt : Option Base)
    (y : EVar) (hWF : Ty.WFBVarCtx (ctx ++ [opt]) t) :
    Ty.WFBVarCtx ctx (t.openVar ctx.length y) := by
  induction t generalizing ctx opt with
  | refine b r =>
    -- ν occupies formula-level 0 (base `b`), so the arrow binder opened by
    -- `openVar ctx.length` lives at formula-level `ctx.length + 1`, and the
    -- WFBVarCtx index list is `some b :: …`. `openBVar` is base-agnostic and
    -- shifting, so `hasBVar` in the opened refinement comes from level `k`
    -- (below the opened level) or the shifted level `k+1` (at/above it).
    simp only [Ty.openVar, Ty.WFBVarCtx] at hWF ⊢
    intro b' k hbv
    rcases (Refinement.hasBVar_openBVar r b' k (ctx.length + 1) y).mp hbv with
      ⟨hlt, hbvr⟩ | ⟨hle, hbvr⟩
    · -- k < ctx.length+1: the occurrence was already at level k in r; the extra
      -- `[opt]` slot sits beyond index k, so it doesn't affect the lookup.
      have hWF' := hWF b' k hbvr
      cases k with
      | zero => simpa using hWF'
      | succ k' =>
        have hk' : k' < ctx.length := by omega
        simp only [List.getElem?_cons_succ] at hWF' ⊢
        rw [List.getElem?_append_left hk'] at hWF'
        exact hWF'
    · -- ctx.length+1 ≤ k: the shifted occurrence sits at index k+1, past the end
      -- of `some b :: (ctx ++ [opt])` (length ctx.length+2) → the lookup is none,
      -- contradicting well-formedness.
      exfalso
      have hWF' := hWF b' (k + 1) hbvr
      rw [List.getElem?_eq_none_iff.mpr (by simp; omega)] at hWF'
      exact absurd hWF' (by simp)
  | arrow s t ihs iht =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.openVar]
    refine ⟨ihs ctx opt hWF.1, ?_⟩
    -- Codomain uses IH with ctx' = s.optBase :: ctx
    have ih := iht (s.optBase :: ctx) opt (by simpa using hWF.2)
    simp only [List.length_cons] at ih
    rw [Ty.optBase_openVar]
    exact ih
  | «forall» kd t ih =>
    simp only [Ty.WFBVarCtx, Ty.openVar] at hWF ⊢
    have h := ih (ctx.map (Option.map Base.shiftT)) (opt.map Base.shiftT)
      (by simpa [List.map_append] using hWF)
    simpa using h
  | prod s t ihs iht =>
    simp only [Ty.WFBVarCtx] at hWF ⊢
    simp only [Ty.openVar]
    refine ⟨ihs ctx opt hWF.1, ?_⟩
    have ih := iht (s.optBase :: ctx) opt (by simpa using hWF.2)
    simp only [List.length_cons] at ih
    rw [Ty.optBase_openVar]
    exact ih
  | data C n args r ih =>
    simp only [Ty.WFBVarCtx, Ty.openVar] at hWF ⊢
    refine ⟨?_, fun i => ih i ctx opt (hWF.2 i)⟩
    intro b' k hbv
    rcases (Refinement.hasBVar_openBVar r b' k (ctx.length + 1) y).mp hbv with
      ⟨hlt, hbvr⟩ | ⟨hle, hbvr⟩
    · have hWF' := hWF.1 b' k hbvr
      cases k with
      | zero => simpa using hWF'
      | succ k' =>
        have hk' : k' < ctx.length := by omega
        simp only [List.getElem?_cons_succ] at hWF' ⊢
        rw [List.getElem?_append_left hk'] at hWF'
        exact hWF'
    · exfalso
      have hWF' := hWF.1 b' (k + 1) hbvr
      rw [List.getElem?_eq_none_iff.mpr (by simp; omega)] at hWF'
      exact absurd hWF' (by simp)

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
  | _, .not t     => .not (Term.substB σ t)
  | _, .and t₁ t₂ => .and (Term.substB σ t₁) (Term.substB σ t₂)

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

@[simp] theorem Val.proj_inj (s : BSort) (v : s.ty) : Val.proj s (Val.inj s v) = v := by
  cases s <;> rfl

theorem Val.inj_injective (s : BSort) {v w : s.ty} : Val.inj s v = Val.inj s w ↔ v = w := by
  cases s <;> simp

@[simp] theorem Term.fv_substB (σ : BSubst) : ∀ {b : Base} (t : Term b),
    (t.substB σ).fv = t.fv := by
  intro b t
  induction t with
  | const _ _ | bvar _ _ | fvar _ _ | mbvar _ _ | mfvar _ _ => rfl
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ =>
    simp only [Term.substB, Term.fv]; exact congr (congrArg (· ++ ·) ih₁) ih₂
  | not _ ih => simp only [Term.substB, Term.fv]; exact ih

@[simp] theorem Formula.fv_substB (σ : BSubst) (φ : Formula) : (φ.substB σ).fv = φ.fv := by
  induction φ with
  | tt | ff => rfl
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    simp only [Formula.substB, Formula.fv]
    exact congr (congrArg (· ++ ·) (Term.fv_substB σ t₁)) (Term.fv_substB σ t₂)
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    simp only [Formula.substB, Formula.fv]; exact congr (congrArg (· ++ ·) ih₁) ih₂
  | not _ ih | ex _ _ ih | all _ _ ih => simp only [Formula.substB, Formula.fv]; exact ih

@[simp] theorem Refinement.fv_substB (σ : BSubst) (r : Refinement) :
    (r.substB σ).fv = r.fv := by
  induction r with
  | fmla φ => simp [Refinement.substB, Refinement.fv]
  | kapp kn args =>
    simp only [Refinement.substB, Refinement.fv, List.flatMap_map]
    congr 1; funext a; exact Term.fv_substB σ a.2
  | conj r₁ r₂ ih₁ ih₂ => simp [Refinement.substB, Refinement.fv, ih₁, ih₂]

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

@[simp] theorem Ty.fv_openTv (k : Nat) (a : TVar) (t : Ty) : (t.openTv k a).fv = t.fv := by
  induction t generalizing k <;> simp_all [Ty.openTv, Ty.fv]

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

/-! ### Well-formedness checker for types with type variables

  `Ty.wfB kctx ctx t` decides, in one pass:
  * every bound variable's sort agrees with its binder (as `Ty.WFBVarCtx`);
  * every `tbvar` is bound (`kctx` lists the enclosing `∀` kinds);
  * ⋆-kinded type variables are refined only with `true`;
  * terms at a type-variable sort are bound variables of a `B`-kinded sort only —
    no constants, no free variables at bound type-variable sorts, no quantifiers
    at type-variable sorts, no type-variable κ arguments.
  The last restrictions are exactly what makes type instantiation semantically
  sound: equality at a type-variable sort then coincides with equality at the
  instance sort. -/

def Base.isTv : Base → Bool
  | .tbvar _ | .tfvar _ => true
  | _ => false

/-- A sort at which terms may occur. -/
def Base.sortOK (kctx : List Kind) : Base → Bool
  | .int | .bool    => true
  | .tbvar j        => kctx[j]? == some .B
  | .tfvar (_, κ)   => κ == .B

/-- A sort at which free variables may occur. -/
@[simp] def Base.fvOK : Base → Bool
  | .int | .bool    => true
  | .tbvar _        => false
  | .tfvar (_, κ)   => κ == .B

/-- A sort that may be refined (bound type variables must be in scope). -/
def Base.tyOK (kctx : List Kind) : Base → Bool
  | .tbvar j => j < kctx.length
  | _        => true

def Base.isStarB (kctx : List Kind) : Base → Bool
  | .tbvar j      => kctx[j]? == some .star
  | .tfvar (_, κ) => κ == .star
  | _             => false

def Term.wfB (kctx : List Kind) (ctx : List (Option Base)) : {b : Base} → Term b → Bool
  | _, .const b _ => !b.isTv
  | _, .bvar b i  => ctx[i]? == some (some b) && b.sortOK kctx
  | _, .fvar b _  => b.fvOK
  | _, .add t₁ t₂ => Term.wfB kctx ctx t₁ && Term.wfB kctx ctx t₂
  | _, .mbvar _ i => decide (i < ctx.length)
  | _, .mfvar _ _ => true
  | _, .not t     => Term.wfB kctx ctx t
  | _, .and t₁ t₂ => Term.wfB kctx ctx t₁ && Term.wfB kctx ctx t₂

def Formula.wfB (kctx : List Kind) (ctx : List (Option Base)) : Formula → Bool
  | .tt | .ff       => true
  | .eq _ t₁ t₂     => t₁.wfB kctx ctx && t₂.wfB kctx ctx
  | .leq _ t₁ t₂     => t₁.wfB kctx ctx && t₂.wfB kctx ctx
  | .and φ₁ φ₂      => φ₁.wfB kctx ctx && φ₂.wfB kctx ctx
  | .or φ₁ φ₂       => φ₁.wfB kctx ctx && φ₂.wfB kctx ctx
  | .imp φ₁ φ₂      => φ₁.wfB kctx ctx && φ₂.wfB kctx ctx
  | .not φ          => φ.wfB kctx ctx
  | .ex b φ         => !b.isTv && φ.wfB kctx (some b :: ctx)
  | .all b φ        => !b.isTv && φ.wfB kctx (some b :: ctx)

/-- The refinement is trivially true (`tt`, or a conjunction of such — as
    produced by instantiating a `true`-refined type variable). -/
def Refinement.isTT : Refinement → Bool
  | .fmla .tt   => true
  | .conj r₁ r₂ => r₁.isTT && r₂.isTT
  | _           => false

def Refinement.wfB (kctx : List Kind) (ctx : List (Option Base)) : Refinement → Bool
  | .fmla φ       => φ.wfB kctx ctx
  | .kapp _ args  => args.all (fun a => !a.1.isTv && Term.wfB kctx ctx a.2)
  | .conj r₁ r₂   => r₁.wfB kctx ctx && r₂.wfB kctx ctx

def Ty.wfB (kctx : List Kind) (ctx : List (Option Base)) : Ty → Bool
  | .refine b r  => b.tyOK kctx && (!b.isStarB kctx || r.isTT) && r.wfB kctx (some b :: ctx)
  | .arrow s t   => s.wfB kctx ctx && t.wfB kctx (s.optBase :: ctx)
  | .forall κ t  => t.wfB (κ :: kctx) (ctx.map (Option.map Base.shiftT))
  | .prod s t    => s.wfB kctx ctx && t.wfB kctx (s.optBase :: ctx)
  | .data _ n args r =>
      r.wfB kctx (none :: ctx) && (List.finRange n).all fun i => (args i).wfB kctx ctx

theorem Term.wfB_hasBVar {kctx : List Kind} {ctx : List (Option Base)} :
    ∀ {b'' : Base} (t : Term b''), t.wfB kctx ctx = true →
      ∀ b k, Term.hasBVar b k t → ctx[k]? = some (some b) := by
  intro b'' t
  induction t with
  | const _ _ | fvar _ _ | mbvar _ _ | mfvar _ _ => intro _ b k h; simp [Term.hasBVar] at h
  | bvar b' i =>
    intro hw b k h
    simp only [Term.hasBVar] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Term.wfB, Bool.and_eq_true, beq_iff_eq] at hw
    exact hw.1
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ =>
    intro hw b k h
    simp only [Term.wfB, Bool.and_eq_true] at hw
    simp only [Term.hasBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 b k h
    · exact ih₂ hw.2 b k h
  | not _ ih =>
    intro hw b k h
    simp only [Term.wfB] at hw
    exact ih hw b k h

theorem Formula.wfB_hasBVar (φ : Formula) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    φ.wfB kctx ctx = true → ∀ b k, Formula.hasBVar b k φ → ctx[k]? = some (some b) := by
  induction φ with
  | tt | ff => intro _ _ _ b k h; simp [Formula.hasBVar] at h
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro kctx ctx hw b k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasBVar] at h
    rcases h with h | h
    · exact Term.wfB_hasBVar t₁ hw.1 b k h
    · exact Term.wfB_hasBVar t₂ hw.2 b k h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro kctx ctx hw b k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 b k h
    · exact ih₂ hw.2 b k h
  | not _ ih =>
    intro kctx ctx hw b k h
    simp only [Formula.wfB] at hw
    exact ih hw b k h
  | ex b₀ _ ih | all b₀ _ ih =>
    intro kctx ctx hw b k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasBVar] at h
    have := ih hw.2 b (k+1) h
    simpa using this

theorem Refinement.wfB_hasBVar (r : Refinement) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    r.wfB kctx ctx = true → ∀ b k, Refinement.hasBVar b k r → ctx[k]? = some (some b) := by
  induction r with
  | fmla φ => intro kctx ctx hw; exact Formula.wfB_hasBVar φ hw
  | kapp kn args =>
    intro kctx ctx hw b k h
    simp only [Refinement.wfB, List.all_eq_true, Bool.and_eq_true] at hw
    simp only [Refinement.hasBVar] at h
    obtain ⟨a, ha, hbv⟩ := h
    exact Term.wfB_hasBVar a.2 (hw a ha).2 b k hbv
  | conj _ _ ih₁ ih₂ =>
    intro kctx ctx hw b k h
    simp only [Refinement.wfB, Bool.and_eq_true] at hw
    simp only [Refinement.hasBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 b k h
    · exact ih₂ hw.2 b k h

theorem Term.wfB_hasMBVar {kctx : List Kind} {ctx : List (Option Base)} :
    ∀ {b'' : Base} (t : Term b''), t.wfB kctx ctx = true → ∀ k, Term.hasMBVar k t → k < ctx.length := by
  intro b'' t
  induction t with
  | const _ _ | bvar _ _ | fvar _ _ | mfvar _ _ => intro _ k h; simp [Term.hasMBVar] at h
  | mbvar m j =>
    intro hw k h
    simp only [Term.hasMBVar] at h; subst h
    simpa [Term.wfB] using hw
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ =>
    intro hw k h
    simp only [Term.wfB, Bool.and_eq_true] at hw
    simp only [Term.hasMBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 k h
    · exact ih₂ hw.2 k h
  | not _ ih => intro hw k h; exact ih hw k h

theorem Formula.wfB_hasMBVar (φ : Formula) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    φ.wfB kctx ctx = true → ∀ k, Formula.hasMBVar k φ → k < ctx.length := by
  induction φ with
  | tt | ff => intro _ _ _ k h; simp [Formula.hasMBVar] at h
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro kctx ctx hw k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasMBVar] at h
    rcases h with h | h
    · exact Term.wfB_hasMBVar t₁ hw.1 k h
    · exact Term.wfB_hasMBVar t₂ hw.2 k h
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro kctx ctx hw k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasMBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 k h
    · exact ih₂ hw.2 k h
  | not _ ih =>
    intro kctx ctx hw k h
    simp only [Formula.wfB] at hw
    exact ih hw k h
  | ex b₀ _ ih | all b₀ _ ih =>
    intro kctx ctx hw k h
    simp only [Formula.wfB, Bool.and_eq_true] at hw
    simp only [Formula.hasMBVar] at h
    have := ih hw.2 (k+1) h
    simpa using this

theorem Refinement.wfB_hasMBVar (r : Refinement) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    r.wfB kctx ctx = true → ∀ k, Refinement.hasMBVar k r → k < ctx.length := by
  induction r with
  | fmla φ => intro kctx ctx hw; exact Formula.wfB_hasMBVar φ hw
  | kapp kn args =>
    intro kctx ctx hw k h
    simp only [Refinement.wfB, List.all_eq_true, Bool.and_eq_true] at hw
    simp only [Refinement.hasMBVar] at h
    obtain ⟨a, ha, hbv⟩ := h
    exact Term.wfB_hasMBVar a.2 (hw a ha).2 k hbv
  | conj _ _ ih₁ ih₂ =>
    intro kctx ctx hw k h
    simp only [Refinement.wfB, Bool.and_eq_true] at hw
    simp only [Refinement.hasMBVar] at h
    rcases h with h | h
    · exact ih₁ hw.1 k h
    · exact ih₂ hw.2 k h

/-- The checker is sound for bound-variable sort consistency. -/
theorem Ty.wfB_WFBVarCtx (t : Ty) : ∀ {kctx : List Kind} {ctx : List (Option Base)},
    t.wfB kctx ctx = true → Ty.WFBVarCtx ctx t := by
  induction t with
  | refine b r =>
    intro kctx ctx hw
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    exact Refinement.wfB_hasBVar r hw.2
  | arrow s t ihs iht =>
    intro kctx ctx hw
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    exact ⟨ihs hw.1, iht hw.2⟩
  | «forall» κ t ih =>
    intro kctx ctx hw
    simp only [Ty.wfB] at hw
    exact ih hw
  | prod s t ihs iht =>
    intro kctx ctx hw
    simp only [Ty.wfB, Bool.and_eq_true] at hw
    exact ⟨ihs hw.1, iht hw.2⟩
  | data C n args r ih =>
    intro kctx ctx hw
    simp only [Ty.wfB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at hw
    exact ⟨Refinement.wfB_hasBVar r hw.1, fun i => ih i (hw.2 i)⟩

theorem Ty.wfB_WFBVars (t : Ty) (h : t.wfB [] [] = true) : Ty.WFBVars t :=
  Ty.wfB_WFBVarCtx t h

/-! ### Bound-variable sort consistency under type-binder opening -/

theorem Term.hasBVar_substB (σ : BSubst) (b : Base) (k : Nat) :
    ∀ {b'' : Base} (t : Term b''), Term.hasBVar b k (t.substB σ) →
      ∃ b₀, b = b₀.substB σ ∧ Term.hasBVar b₀ k t := by
  intro b'' t
  induction t with
  | const _ _ | fvar _ _ | mbvar _ _ | mfvar _ _ => intro h; simp [Term.substB, Term.hasBVar] at h
  | bvar b' i =>
    intro h
    simp only [Term.substB, Term.hasBVar] at h
    exact ⟨b', h.1, rfl, h.2⟩
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ =>
    intro h
    simp only [Term.substB, Term.hasBVar] at h
    rcases h with h | h
    · obtain ⟨b₀, hb, h⟩ := ih₁ h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := ih₂ h; exact ⟨b₀, hb, Or.inr h⟩
  | not _ ih => intro h; simp only [Term.substB, Term.hasBVar] at h; exact ih h

theorem Formula.hasBVar_substB (σ : BSubst) (b : Base) (φ : Formula) :
    ∀ k, Formula.hasBVar b k (φ.substB σ) → ∃ b₀, b = b₀.substB σ ∧ Formula.hasBVar b₀ k φ := by
  induction φ with
  | tt | ff => intro k h; simp [Formula.substB, Formula.hasBVar] at h
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro k h
    simp only [Formula.substB, Formula.hasBVar] at h
    rcases h with h | h
    · obtain ⟨b₀, hb, h⟩ := Term.hasBVar_substB σ b k t₁ h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := Term.hasBVar_substB σ b k t₂ h; exact ⟨b₀, hb, Or.inr h⟩
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro k h
    simp only [Formula.substB, Formula.hasBVar] at h
    rcases h with h | h
    · obtain ⟨b₀, hb, h⟩ := ih₁ k h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := ih₂ k h; exact ⟨b₀, hb, Or.inr h⟩
  | not _ ih => intro k h; simp only [Formula.substB, Formula.hasBVar] at h; exact ih k h
  | ex _ _ ih | all _ _ ih =>
    intro k h; simp only [Formula.substB, Formula.hasBVar] at h; exact ih (k+1) h

theorem Refinement.hasBVar_substB (σ : BSubst) (b : Base) (r : Refinement) (k : Nat)
    (h : Refinement.hasBVar b k (r.substB σ)) :
    ∃ b₀, b = b₀.substB σ ∧ Refinement.hasBVar b₀ k r := by
  induction r with
  | fmla φ => exact Formula.hasBVar_substB σ b φ k h
  | kapp kn args =>
    simp only [Refinement.substB, Refinement.hasBVar, List.mem_map] at h
    obtain ⟨_, ⟨a, ha, rfl⟩, hbv⟩ := h
    obtain ⟨b₀, hb, hbv⟩ := Term.hasBVar_substB σ b k a.2 hbv
    exact ⟨b₀, hb, a, ha, hbv⟩
  | conj _ _ ih₁ ih₂ =>
    simp only [Refinement.substB, Refinement.hasBVar] at h
    rcases h with h | h
    · obtain ⟨b₀, hb, h⟩ := ih₁ h; exact ⟨b₀, hb, Or.inl h⟩
    · obtain ⟨b₀, hb, h⟩ := ih₂ h; exact ⟨b₀, hb, Or.inr h⟩

/-- Opening commutes with entering a further type binder. -/
theorem Base.shiftT_substB_openAt (k : Nat) (a : TVar) (b : Base) :
    (b.substB (BSubst.openAt k a)).shiftT = b.shiftT.substB (BSubst.openAt (k+1) a) := by
  cases b with
  | tbvar j =>
    simp only [Base.substB, BSubst.openAt, BSubst.instAt, Base.shiftT]
    by_cases h₁ : j = k
    · subst h₁; simp
    · by_cases h₂ : k < j
      · simp [h₁, h₂] <;> omega
      · simp [h₁, h₂] <;> omega
  | _ => rfl

/-- Opening a type binder preserves bound-variable sort consistency (with the
    recorded sorts opened alike). -/
theorem Ty.WFBVarCtx_openTv (t : Ty) : ∀ (k : Nat) (a : TVar) (ctx : List (Option Base)),
    Ty.WFBVarCtx ctx t →
    Ty.WFBVarCtx (ctx.map (Option.map (Base.substB (BSubst.openAt k a)))) (t.openTv k a) := by
  induction t with
  | refine br r =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    intro b i hbv
    obtain ⟨b₀, rfl, hbv₀⟩ := Refinement.hasBVar_substB _ b r i hbv
    have := h b₀ i hbv₀
    show ((some br :: ctx).map (Option.map (Base.substB (BSubst.openAt k a))))[i]? = _
    rw [List.getElem?_map, this]; rfl
  | arrow s t ihs iht =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨ihs k a ctx h.1, ?_⟩
    have := iht k a (s.optBase :: ctx) h.2
    have hopt : (s.openTv k a).optBase = s.optBase.map (Base.substB (BSubst.openAt k a)) := by
      cases s <;> rfl
    rw [hopt]; simpa using this
  | «forall» κ t ih =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    have := ih (k+1) a (ctx.map (Option.map Base.shiftT)) h
    have hmap : (ctx.map (Option.map (Base.substB (BSubst.openAt k a)))).map (Option.map Base.shiftT)
        = (ctx.map (Option.map Base.shiftT)).map (Option.map (Base.substB (BSubst.openAt (k+1) a))) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro o _
      cases o <;> simp [Base.shiftT_substB_openAt]
    rw [hmap]; exact this
  | prod s t ihs iht =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨ihs k a ctx h.1, ?_⟩
    have := iht k a (s.optBase :: ctx) h.2
    have hopt : (s.openTv k a).optBase = s.optBase.map (Base.substB (BSubst.openAt k a)) := by
      cases s <;> rfl
    rw [hopt]; simpa using this
  | data C n args r ih =>
    intro k a ctx h
    simp only [Ty.openTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨?_, fun i => ih i k a ctx (h.2 i)⟩
    intro b i hbv
    obtain ⟨b₀, rfl, hbv₀⟩ := Refinement.hasBVar_substB _ b r i hbv
    have := h.1 b₀ i hbv₀
    show ((none :: ctx).map (Option.map (Base.substB (BSubst.openAt k a))))[i]? = _
    rw [List.getElem?_map, this]; rfl

theorem Ty.WFBVars_openTv (t : Ty) (k : Nat) (a : TVar) (h : Ty.WFBVars t) :
    Ty.WFBVars (t.openTv k a) := by
  have := Ty.WFBVarCtx_openTv t k a [] h
  simpa using this

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

@[simp] theorem Ty.fv_closeTv (k : Nat) (a : TVar) (t : Ty) : (t.closeTv k a).fv = t.fv := by
  induction t generalizing k <;> simp_all [Ty.closeTv, Ty.fv]

@[simp] theorem Ty.fv_gen (as : List TVar) (t : Ty) : (Ty.gen as t).fv = t.fv := by
  induction as <;> simp_all [Ty.gen, Ty.fv]

theorem Base.shiftT_substB_closeAt (k : Nat) (a : TVar) (b : Base) :
    (b.substB (BSubst.closeAt k a)).shiftT = b.shiftT.substB (BSubst.closeAt (k+1) a) := by
  cases b with
  | tbvar j =>
    simp only [Base.substB, BSubst.closeAt, Base.shiftT]
    by_cases h : k ≤ j
    · simp [h, show k + 1 ≤ j + 1 by omega]
    · simp [h, show ¬ k + 1 ≤ j + 1 by omega]
  | tfvar a' =>
    simp only [Base.substB, BSubst.closeAt]
    by_cases h : a' = a <;> simp [h, Base.shiftT]
  | _ => rfl

theorem Ty.WFBVarCtx_closeTv (t : Ty) : ∀ (k : Nat) (a : TVar) (ctx : List (Option Base)),
    Ty.WFBVarCtx ctx t →
    Ty.WFBVarCtx (ctx.map (Option.map (Base.substB (BSubst.closeAt k a)))) (t.closeTv k a) := by
  induction t with
  | refine br r =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    intro b i hbv
    obtain ⟨b₀, rfl, hbv₀⟩ := Refinement.hasBVar_substB _ b r i hbv
    have := h b₀ i hbv₀
    show ((some br :: ctx).map (Option.map (Base.substB (BSubst.closeAt k a))))[i]? = _
    rw [List.getElem?_map, this]; rfl
  | arrow s t ihs iht =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨ihs k a ctx h.1, ?_⟩
    have := iht k a (s.optBase :: ctx) h.2
    have hopt : (s.closeTv k a).optBase = s.optBase.map (Base.substB (BSubst.closeAt k a)) := by
      cases s <;> rfl
    rw [hopt]; simpa using this
  | «forall» κ t ih =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    have := ih (k+1) a (ctx.map (Option.map Base.shiftT)) h
    have hmap : (ctx.map (Option.map (Base.substB (BSubst.closeAt k a)))).map (Option.map Base.shiftT)
        = (ctx.map (Option.map Base.shiftT)).map (Option.map (Base.substB (BSubst.closeAt (k+1) a))) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro o _
      cases o <;> simp [Base.shiftT_substB_closeAt]
    rw [hmap]; exact this
  | prod s t ihs iht =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨ihs k a ctx h.1, ?_⟩
    have := iht k a (s.optBase :: ctx) h.2
    have hopt : (s.closeTv k a).optBase = s.optBase.map (Base.substB (BSubst.closeAt k a)) := by
      cases s <;> rfl
    rw [hopt]; simpa using this
  | data C n args r ih =>
    intro k a ctx h
    simp only [Ty.closeTv, Ty.WFBVarCtx] at h ⊢
    refine ⟨?_, fun i => ih i k a ctx (h.2 i)⟩
    intro b i hbv
    obtain ⟨b₀, rfl, hbv₀⟩ := Refinement.hasBVar_substB _ b r i hbv
    have := h.1 b₀ i hbv₀
    show ((none :: ctx).map (Option.map (Base.substB (BSubst.closeAt k a))))[i]? = _
    rw [List.getElem?_map, this]; rfl

theorem Ty.WFBVars_gen (as : List TVar) (t : Ty) (h : Ty.WFBVars t) : Ty.WFBVars (Ty.gen as t) := by
  induction as with
  | nil => exact h
  | cons a as ih =>
    have := Ty.WFBVarCtx_closeTv _ 0 a [] ih
    simpa [Ty.gen, Ty.WFBVars, Ty.WFBVarCtx] using this

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
  | _, .not t      => Term.ftv t
  | _, .and t₁ t₂  => Term.ftv t₁ ++ Term.ftv t₂

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

/-! ## 5. Exp operations (locally nameless)

  (Val is declared in `Syntax.lean`; its operations follow below in §5b.) -/

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
    termination measure for algorithmic functions in `VCGen.lean`. -/
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

theorem Exp.WFBVars_openTv (e : Exp) (k : Nat) (a : TVar) (h : Exp.WFBVars e) :
    Exp.WFBVars (e.openTv k a) := by
  induction e generalizing k with
  | ann e t ih =>
    simp only [Exp.WFBVars, Exp.openTv] at h ⊢
    exact ⟨Ty.WFBVars_openTv t k a h.1, ih k h.2⟩
  | _ => simp_all [Exp.WFBVars, Exp.openTv]

@[simp] theorem Exp.lc_at_openTv (k : Nat) (a : TVar) (e : Exp) (n : Nat) :
    (e.openTv k a).lc_at n ↔ e.lc_at n := by
  induction e generalizing k n <;> simp_all [Exp.openTv, Exp.lc_at]

@[simp] theorem Exp.fv_openTv (k : Nat) (a : TVar) (e : Exp) :
    (e.openTv k a).fv = e.fv := by
  induction e generalizing k <;> simp_all [Exp.openTv, Exp.fv]

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

theorem TEnv.genVars_fresh {Γ : TEnv} {t : Ty} {a : TVar} (h : a ∈ TEnv.genVars Γ t) :
    a ∉ TEnv.ftv Γ := by
  simp only [TEnv.genVars, List.mem_eraseDups, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

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

/-! ### Type erasure

  Types never influence evaluation, so programs are run after erasing them
  (`Run`, Semantics.lean). Erasure is what makes opening a type binder
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

@[simp] theorem Exp.erase_erase (e : Exp) : e.erase.erase = e.erase := by
  induction e <;> simp_all [Exp.erase]

@[simp] theorem Exp.erase_openTv (k : Nat) (a : TVar) (e : Exp) :
    (e.openTv k a).erase = e.erase := by
  induction e generalizing k <;> simp_all [Exp.openTv, Exp.erase]

theorem Exp.erase_openExp (k : Nat) (u e : Exp) :
    (Exp.openExp k u e).erase = Exp.openExp k u.erase e.erase := by
  induction e generalizing k with
  | bvar j => by_cases h : j = k <;> simp [Exp.openExp, Exp.erase, h]
  | _ => simp_all [Exp.openExp, Exp.erase]

theorem Exp.fv_erase_subset (e : Exp) : ∀ z ∈ e.erase.fv, z ∈ e.fv := by
  induction e <;> simp_all [Exp.erase, Exp.fv] <;> grind

theorem Exp.lc_at_erase (e : Exp) (k : Nat) (h : e.lc_at k) : e.erase.lc_at k := by
  induction e generalizing k <;> simp_all [Exp.erase, Exp.lc_at]

theorem Exp.typeFree_erase (e : Exp) : e.erase.TypeFree := by
  induction e <;> simp_all [Exp.erase, Exp.TypeFree]

theorem Exp.erase_of_typeFree (e : Exp) (h : e.TypeFree) : e.erase = e := by
  induction e <;> simp_all [Exp.erase, Exp.TypeFree]

/-- A type-free expression is unaffected by opening a type binder. -/
theorem Exp.openTv_of_typeFree (k : Nat) (a : TVar) (e : Exp) (h : e.TypeFree) :
    e.openTv k a = e := by
  induction e generalizing k <;> simp_all [Exp.openTv, Exp.TypeFree]

/-- The closing substitution commutes with erasure, provided the substituted
    values are erased. -/
theorem Exp.erase_substEnv (γ : REnv) (e : Exp)
    (hγ : ∀ z ∈ e.fv, Val.Erased (γ.map z)) :
    (Exp.substEnv γ e).erase = Exp.substEnv γ e.erase := by
  induction e with
  | fvar x => exact Exp.erase_of_typeFree _ (hγ x (by simp [Exp.fv]))
  | case e n alts ih ihs =>
    simp only [Exp.substEnv, Exp.erase, Exp.fv, List.mem_append, List.mem_flatMap,
      List.mem_finRange, true_and] at hγ ⊢
    rw [ih (fun z hz => hγ z (Or.inl hz))]
    congr 1; funext j; exact ihs j (fun z hz => hγ z (Or.inr ⟨j, hz⟩))
  | _ => simp_all [Exp.substEnv, Exp.erase, Exp.fv]

/-- The closing substitution commutes with opening a type binder, provided the
    substituted values are erased (hence type-free). -/
theorem Exp.substEnv_openTv (γ : REnv) (k : Nat) (a : TVar) (e : Exp)
    (hγ : ∀ z ∈ e.fv, Val.Erased (γ.map z)) :
    Exp.substEnv γ (e.openTv k a) = (Exp.substEnv γ e).openTv k a := by
  induction e generalizing k with
  | fvar x =>
    simp only [Exp.openTv, Exp.substEnv]
    exact (Exp.openTv_of_typeFree k a _ (hγ x (by simp [Exp.fv]))).symm
  | case e n alts ih ihs =>
    simp only [Exp.substEnv, Exp.openTv, Exp.fv, List.mem_append, List.mem_flatMap,
      List.mem_finRange, true_and] at hγ ⊢
    rw [ih k (fun z hz => hγ z (Or.inl hz))]
    congr 1; funext j; exact ihs j k (fun z hz => hγ z (Or.inr ⟨j, hz⟩))
  | _ => simp_all [Exp.substEnv, Exp.openTv, Exp.fv, Ty.openTv, Base.substB, Refinement.substB,
      Formula.substB]

/-! ## 9. Freshness helper

  `EVar.fresh L` returns a name not in `L`, by producing a string longer than
  any element of `L`. The freshness proof lives in Stage 2b. -/

def EVar.maxLen : List EVar → Nat
  | []      => 0
  | x :: xs => Nat.max x.length (EVar.maxLen xs)

def EVar.fresh (L : List EVar) : EVar :=
  String.ofList (List.replicate (EVar.maxLen L + 1) 'x')

/-! ## 10. REnv helpers -/

@[simp] theorem REnv.get_update_same (b : Base) (γ : REnv) (x : EVar) (v : b.sem γ.sorts) :
    REnv.get b (γ.update b x v) x = v := by
  simp [REnv.get, REnv.update, REnv.write, REnv.lookup]

/-! ## 11. EVar.fresh proof -/

private theorem EVar.maxLen_ge {L : List EVar} {s : EVar} (h : s ∈ L) :
    s.length ≤ EVar.maxLen L := by
  induction L with
  | nil => simp at h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [EVar.maxLen]; exact Nat.le_max_left _ _
    · simp [EVar.maxLen]
      exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

private theorem EVar.fresh_length (L : List EVar) :
    (EVar.fresh L).length = EVar.maxLen L + 1 := by
  show (String.ofList (List.replicate (EVar.maxLen L + 1) 'x')).length
       = EVar.maxLen L + 1
  rw [String.length_ofList, List.length_replicate]

theorem EVar.fresh_not_mem (L : List EVar) : EVar.fresh L ∉ L := by
  intro h
  have h₁ : (EVar.fresh L).length = EVar.maxLen L + 1 := EVar.fresh_length L
  have h₂ : (EVar.fresh L).length ≤ EVar.maxLen L := EVar.maxLen_ge h
  rw [h₁] at h₂
  omega

/-- A type-variable name with the given kind, fresh for `L` (by name). -/
def TVar.fresh (L : List TVar) (κ : Kind) : TVar :=
  (EVar.fresh (L.map Prod.fst), κ)

theorem TVar.fresh_not_mem (L : List TVar) (κ : Kind) : TVar.fresh L κ ∉ L := fun h =>
  EVar.fresh_not_mem (L.map Prod.fst) (List.mem_map.mpr ⟨_, h, rfl⟩)


/-- A fresh name is `≠` any member of the list it was drawn from — decided by
    *length* (`EVar.maxLen`), not by comparing the `x`-strings character by
    character (which is prohibitively deep for nested contexts). Stated as
    `beq = false` so it fires as a `simp` rewrite on `if · == · …`. -/
@[simp] theorem EVar.fresh_beq_mem_left (L : List EVar) (x : EVar) (h : x ∈ L) :
    (EVar.fresh L == x) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq; subst heq; exact EVar.fresh_not_mem L h

@[simp] theorem EVar.fresh_beq_mem_right (L : List EVar) (x : EVar) (h : x ∈ L) :
    (x == EVar.fresh L) = false := by
  apply beq_eq_false_iff_ne.mpr
  intro heq; subst heq; exact EVar.fresh_not_mem L h

/-! ## 15. `Exp.substEnv` push-through lemmas

  Under the structural definition each constructor case is *definitional*
  (`rfl`); the lemmas are kept (as `@[simp]`) so existing call sites and the
  `simp` set continue to fire by name. -/

@[simp]
theorem Exp.substEnv_fvar (γ : REnv) (x : EVar) :
    Exp.substEnv γ (.fvar x) = (γ.map x).toExp := rfl

@[simp]
theorem Exp.substEnv_iconst (γ : REnv) (n : Int) :
    Exp.substEnv γ (.iconst n) = .iconst n := rfl

@[simp]
theorem Exp.substEnv_bconst (γ : REnv) (b : Bool) :
    Exp.substEnv γ (.bconst b) = .bconst b := rfl

@[simp]
theorem Exp.substEnv_lam (γ : REnv) (body : Exp) :
    Exp.substEnv γ (.lam body) = .lam (Exp.substEnv γ body) := rfl

@[simp]
theorem Exp.substEnv_letin (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.letin e₁ e₂) = .letin (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_app (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.app e₁ e₂) = .app (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_ann (γ : REnv) (e : Exp) (t : Ty) :
    Exp.substEnv γ (.ann e t) = .ann (Exp.substEnv γ e) t := rfl

@[simp]
theorem Exp.substEnv_add (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.add e₁ e₂) = .add (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_leq (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.leq e₁ e₂) = .leq (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_not (γ : REnv) (e : Exp) :
    Exp.substEnv γ (.not e) = .not (Exp.substEnv γ e) := rfl

@[simp]
theorem Exp.substEnv_and (γ : REnv) (e₁ e₂ : Exp) :
    Exp.substEnv γ (.and e₁ e₂) = .and (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_ite (γ : REnv) (e₀ e₁ e₂ : Exp) :
    Exp.substEnv γ (.ite e₀ e₁ e₂) = .ite (Exp.substEnv γ e₀) (Exp.substEnv γ e₁) (Exp.substEnv γ e₂) := rfl

@[simp]
theorem Exp.substEnv_unreach (γ : REnv) :
    Exp.substEnv γ .unreach = .unreach := rfl

@[simp]
theorem Exp.substEnv_fix (γ : REnv) (body : Exp) :
    Exp.substEnv γ (.fix body) = .fix (Exp.substEnv γ body) := rfl

@[simp]
theorem Exp.substEnv_tabs (γ : REnv) (κ : Kind) (e : Exp) :
    Exp.substEnv γ (.tabs κ e) = .tabs κ (Exp.substEnv γ e) := rfl

@[simp]
theorem Exp.substEnv_tapp (γ : REnv) (e : Exp) (t : Ty) :
    Exp.substEnv γ (.tapp e t) = .tapp (Exp.substEnv γ e) (.refine .int (.fmla .tt)) := rfl

/-- A closed expression is fixed, up to erasure, under the closing substitution
    (which drops type-application and constructor instances). -/
theorem Exp.substEnv_closed (γ : REnv) (e : Exp) (he : e.fv = []) :
    (Exp.substEnv γ e).erase = e.erase := by
  induction e with
  | fvar y => simp [Exp.fv] at he
  | case e n alts ih ihs =>
    simp only [Exp.fv, List.append_eq_nil_iff, List.flatMap_eq_nil_iff, List.mem_finRange,
      true_implies] at he
    simp only [Exp.substEnv, Exp.erase, ih he.1]
    congr 1; funext j; exact ihs j (he.2 j)
  | _ => simp_all [Exp.substEnv, Exp.erase, Exp.fv]

theorem Val.toExp_closed_of_closed {v : Val} (h : Val.closed v) : v.toExp.fv = [] := h

theorem Val.toExp_lc_at_zero {v : Val} (h : Val.lc v) : Exp.lc_at 0 v.toExp := h

/-- If every free name of `e` is mapped to a closed value by `γ`, then the
    closing substitution produces a closed expression. -/
theorem Exp.substEnv_fv_nil (γ : REnv) (e : Exp)
    (hcl : ∀ z ∈ e.fv, Val.closed (γ.map z)) :
    (Exp.substEnv γ e).fv = [] := by
  induction e with
  | bvar _ | iconst _ | bconst _ | unreach => rfl
  | fvar x => exact Val.toExp_closed_of_closed (hcl x (by simp [Exp.fv]))
  | lam body ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | fix body ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | ann e t ih | tapp e t ih | tabs t e ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | not e ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨ih₁ fun z hz => hcl z (by simp [Exp.fv, hz]),
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨⟨ih₀ fun z hz => hcl z (by simp [Exp.fv, hz]),
            ih₁ fun z hz => hcl z (by simp [Exp.fv, hz])⟩,
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩
  | pair e₁ e₂ ih₁ ih₂ | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff]
    exact ⟨ih₁ fun z hz => hcl z (by simp [Exp.fv, hz]),
           ih₂ fun z hz => hcl z (by simp [Exp.fv, hz])⟩
  | ctor C j τs e ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
  | case e n alts ih ihs =>
    simp only [Exp.substEnv, Exp.fv, List.append_eq_nil_iff, List.flatMap_eq_nil_iff,
      List.mem_finRange, true_implies]
    exact ⟨ih fun z hz => hcl z (by simp [Exp.fv, hz]),
           fun j => ihs j fun z hz => hcl z (by simp only [Exp.fv, List.mem_append,
             List.mem_flatMap, List.mem_finRange, true_and]; exact Or.inr ⟨j, hz⟩)⟩

/-! ## 17b. openVar of lc_at is identity -/

/-- Converse of openVar_of_lc_at: if opening e at depth k with any name gives lc_at k,
    then e itself is lc_at (k+1). This is the standard LN "body is lc" lemma. -/
theorem Exp.lc_at_of_openVar (e : Exp) (k : Nat) (x : EVar)
    (h : (e.openVar k x).lc_at k) : e.lc_at (k + 1) := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.openVar] at h
    simp only [Exp.lc_at]
    by_cases hjk : j = k
    · subst hjk; omega
    · simp only [hjk, ↓reduceIte, Exp.lc_at] at h; omega
  | fvar _ => trivial
  | iconst _ => trivial
  | bconst _ => trivial
  | unreach => trivial
  | lam body ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih (k + 1) h
  | fix body ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih (k + 2) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ (k + 1) h.2⟩
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | ann e t ih | tapp e t ih | tabs t e ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih k h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | not e ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih k h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₀ k h.1, ih₁ k h.2.1, ih₂ k h.2.2⟩
  | add e₁ e₂ ih₁ ih₂ | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩
  | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ (k + 2) h.2⟩
  | ctor C j τs e ih =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ih k h
  | case e n alts ih ihs =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih k h.1, fun j => ihs j (k + 1) (h.2 j)⟩

/-- Opening a binder with `y` adds at most `y` to the free names. -/
theorem Exp.fv_openVar {e : Exp} {k : Nat} {y z : EVar}
    (h : z ∈ (e.openVar k y).fv) : z ∈ e.fv ∨ z = y := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.openVar] at h
    split at h <;> simp_all [Exp.fv]
  | fvar _ | iconst _ | bconst _ | unreach => simp_all [Exp.openVar, Exp.fv]
  | lam _ ih | ann _ _ ih | not _ ih | fix _ ih | tapp _ _ ih | tabs _ _ ih =>
    simp only [Exp.openVar, Exp.fv] at h ⊢; exact ih h
  | letin _ _ ih₁ ih₂ | app _ _ ih₁ ih₂ | and _ _ ih₁ ih₂
  | leq _ _ ih₁ ih₂ | add _ _ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | ite _ _ _ ih₀ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.fv, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · rcases ih₀ h with h | h <;> simp [h]
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | pair _ _ ih₁ ih₂ | split _ _ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.fv, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases ih₁ h with h | h <;> simp [h]
    · rcases ih₂ h with h | h <;> simp [h]
  | ctor _ _ _ _ ih => simp only [Exp.openVar, Exp.fv] at h ⊢; exact ih h
  | case _ _ _ ih ihs =>
    simp only [Exp.openVar, Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange,
      true_and] at h ⊢
    rcases h with h | ⟨j, h⟩
    · rcases ih h with h | h <;> simp [h]
    · rcases ihs j h with h | h
      · exact Or.inl (Or.inr ⟨j, h⟩)
      · exact Or.inr h

/-- openExp with any u is identity when e has lc_at k (no BVar k inside). -/
theorem Exp.openExp_of_lc_at (e : Exp) (k : Nat) (u : Exp) (h : Exp.lc_at k e) :
    Exp.openExp k u e = e := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.lc_at] at h
    simp only [Exp.openExp, if_neg (Nat.ne_of_lt h)]
  | fvar _ => rfl
  | iconst _ => rfl
  | bconst _ => rfl
  | unreach => rfl
  | lam body ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih (k+1) h
  | fix body ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih (k+2) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih₁ k h.1, ih₂ (k+1) h.2]
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | ann e t ih | tapp e t ih | tabs t e ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih k h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | not e ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih k h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih₀ k h.1, ih₁ k h.2.1, ih₂ k h.2.2]
  | add e₁ e₂ ih₁ ih₂ | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2
  | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih₁ k h.1, ih₂ (k+2) h.2]
  | ctor C j τs e ih =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1; exact ih k h
  | case e n alts ih ihs =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]
    rw [ih k h.1]; congr 1; funext j; exact ihs j (k+1) (h.2 j)

/-- lc_at is monotone: lc_at j implies lc_at k for k ≥ j. -/
theorem Exp.lc_at_mono (e : Exp) {j k : Nat} (hjk : j ≤ k) (h : Exp.lc_at j e) :
    Exp.lc_at k e := by
  induction e generalizing j k with
  | bvar i => exact Nat.lt_of_lt_of_le h hjk
  | fvar _ => trivial
  | iconst _ => trivial
  | bconst _ => trivial
  | unreach => trivial
  | lam body ih =>
    simp only [Exp.lc_at] at *
    exact ih (Nat.succ_le_succ hjk) h
  | fix body ih =>
    simp only [Exp.lc_at] at *
    exact ih (by omega) h
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ (Nat.succ_le_succ hjk) h.2⟩
  | app e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | ann e t ih | tapp e t ih | tabs t e ih =>
    simp only [Exp.lc_at] at *
    exact ih hjk h
  | and e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | not e ih =>
    simp only [Exp.lc_at] at *
    exact ih hjk h
  | leq e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₀ hjk h.1, ih₁ hjk h.2.1, ih₂ hjk h.2.2⟩
  | add e₁ e₂ ih₁ ih₂ | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩
  | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ (by omega) h.2⟩
  | ctor C j τs e ih =>
    simp only [Exp.lc_at] at *
    exact ih hjk h
  | case e n alts ih ihs =>
    simp only [Exp.lc_at] at *
    exact ⟨ih hjk h.1, fun j => ihs j (by omega) (h.2 j)⟩

/-! ## 17b. subst/substEnv preserve lc_at -/

theorem Exp.substEnv_lc_at (γ : REnv) (e : Exp) (k : Nat)
    (hγ : ∀ z ∈ e.fv, Val.lc (γ.map z)) (hlc_e : e.lc_at k) :
    (e.substEnv γ).lc_at k := by
  induction e generalizing k with
  | bvar j => simpa [Exp.substEnv] using hlc_e
  | iconst _ | bconst _ | unreach => trivial
  | fvar x =>
    exact Exp.lc_at_mono _ (Nat.zero_le k) (Val.toExp_lc_at_zero (hγ x (by simp [Exp.fv])))
  | lam body ih =>
    exact ih (k+1) (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | fix body ih =>
    exact ih (k+2) (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | ann e t ih | tapp e t ih | tabs t e ih =>
    exact ih k (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | not e ih =>
    exact ih k (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | letin e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ (k+1) (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    obtain ⟨h₀, h₁, h₂⟩ := hlc_e
    exact ⟨ih₀ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₀,
           ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | pair e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | split e₁ e₂ ih₁ ih₂ =>
    obtain ⟨h₁, h₂⟩ := hlc_e
    exact ⟨ih₁ k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₁,
           ih₂ (k+2) (fun z hz => hγ z (by simp [Exp.fv, hz])) h₂⟩
  | ctor C j τs e ih =>
    exact ih k (fun z hz => hγ z (by simpa [Exp.fv] using hz)) hlc_e
  | case e n alts ih ihs =>
    obtain ⟨h₀, h₁⟩ := hlc_e
    exact ⟨ih k (fun z hz => hγ z (by simp [Exp.fv, hz])) h₀,
           fun j => ihs j (k+1) (fun z hz => hγ z (by
             simp only [Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
             exact Or.inr ⟨j, hz⟩)) (h₁ j)⟩


/-! ## 19. substEnv-openVal: key lemma for lam/letin cases -/

theorem REnv.write_self (γ : REnv) (x : EVar) (v : Val) : (γ.write x v).map x = v := by
  simp

theorem REnv.write_other (γ : REnv) (x : EVar) (v : Val) {y : EVar} (h : x ≠ y) :
    (γ.write x v).map y = γ.map y := by
  have hxy : (x == y) = false := by simp [h]
  simp [hxy]

/-- Writing a cell's current value back is the identity (no `HasBase` needed,
    since `write` is lossless). Drives the simplified `app` case of the
    fundamental lemma. -/
theorem REnv.write_idem (γ : REnv) (x : EVar) : γ.write x (γ.map x) = γ := by
  apply REnv.ext
  · funext y
    by_cases hxy : x = y
    · subst hxy; simp
    · simp [hxy]
  · rfl
  · rfl

/-- The closing substitution depends only on `γ` over the free names of `e`. -/
theorem Exp.substEnv_congr (e : Exp) (γ₁ γ₂ : REnv)
    (h : ∀ z ∈ e.fv, γ₁.map z = γ₂.map z) :
    Exp.substEnv γ₁ e = Exp.substEnv γ₂ e := by
  induction e with
  | bvar _ | iconst _ | bconst _ | unreach => rfl
  | fvar x => simp only [Exp.substEnv, h x (by simp [Exp.fv])]
  | lam e ih | ann e _ ih | not e ih | fix e ih | tapp e _ ih | tabs _ e ih =>
    simp only [Exp.substEnv, ih fun z hz => h z (by simpa [Exp.fv] using hz)]
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₀ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]
  | pair e₁ e₂ ih₁ ih₂ | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.substEnv,
      ih₁ fun z hz => h z (by simp [Exp.fv, hz]),
      ih₂ fun z hz => h z (by simp [Exp.fv, hz])]
  | ctor _ _ _ e ih =>
    simp only [Exp.substEnv, ih fun z hz => h z (by simpa [Exp.fv] using hz)]
  | case e n alts ih ihs =>
    simp only [Exp.substEnv, ih fun z hz => h z (by simp [Exp.fv, hz])]
    congr 1; funext j
    exact ihs j fun z hz => h z (by
      simp only [Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
      exact Or.inr ⟨j, hz⟩)

/-- Extending `γ` at a name `y` not free in `e` does not change `substEnv`. -/
theorem Exp.substEnv_write_fresh (e : Exp) (γ : REnv) (y : EVar) (v : Val)
    (h : y ∉ e.fv) :
    Exp.substEnv (γ.write y v) e = Exp.substEnv γ e := by
  apply Exp.substEnv_congr
  intro z hz
  exact REnv.write_other γ y v (by rintro rfl; exact h hz)

/-- Key lemma for the lam/letin cases: opening the binder with a fresh `z` and
    then closing under `γ.write z va` equals closing the body under `γ` and then
    plugging `va` into the bound position. -/
theorem Exp.substEnv_write_openVar (e : Exp) (γ : REnv) (va : Val) (z : EVar) (k : Nat)
    (hz_fv : z ∉ e.fv) (hγ : ∀ w ∈ e.fv, Val.lc (γ.map w)) :
    Exp.substEnv (γ.write z va) (Exp.openVar k z e) =
      Exp.openExp k va.toExp (Exp.substEnv γ e) := by
  induction e generalizing k with
  | bvar j =>
    by_cases hjk : j = k
    · subst hjk; simp [Exp.openVar, Exp.substEnv, Exp.openExp]
    · simp [Exp.openVar, Exp.substEnv, Exp.openExp, hjk]
  | iconst _ | bconst _ | unreach => rfl
  | fvar y =>
    have hyz : z ≠ y := fun he => hz_fv (by simp [Exp.fv, he])
    show Exp.substEnv (γ.write z va) (.fvar y) = Exp.openExp k va.toExp ((γ.map y).toExp)
    rw [Exp.substEnv_fvar, REnv.write_other γ z va hyz]
    exact (Exp.openExp_of_lc_at _ k va.toExp
      (Exp.lc_at_mono _ (Nat.zero_le k)
        (Val.toExp_lc_at_zero (hγ y (by simp [Exp.fv]))))).symm
  | lam e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih (k+1) (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | fix e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih (k+2) (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | ann e t ih | tapp e t ih | tabs t e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | not e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | letin e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ (k+1) hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂ | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ k hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    obtain ⟨⟨hz₀, hz₁⟩, hz₂⟩ := hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₀ k hz₀ (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₁ k hz₁ (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ k hz₂ (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | pair e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ k hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | split e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.mem_append, not_or] at hz_fv
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih₁ k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw])),
      ih₂ (k+2) hz_fv.2 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
  | ctor C j τs e ih =>
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp]
    rw [ih k (by simpa [Exp.fv] using hz_fv)
        (fun w hw => hγ w (by simpa [Exp.fv] using hw))]
  | case e n alts ih ihs =>
    simp only [Exp.fv, List.mem_append, not_or, List.mem_flatMap, List.mem_finRange,
      true_and, not_exists] at hz_fv
    have hmem : ∀ j, ∀ w ∈ (alts j).fv, w ∈ (Exp.case e n alts).fv := fun j w hw => by
      simp only [Exp.fv, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
      exact Or.inr ⟨j, hw⟩
    simp only [Exp.openVar, Exp.substEnv, Exp.openExp,
      ih k hz_fv.1 (fun w hw => hγ w (by simp [Exp.fv, hw]))]
    congr 1; funext j
    exact ihs j (k+1) (hz_fv.2 j) (fun w hw => hγ w (hmem j w hw))

/-- `write` (on the name map) commutes with `push` (on the de Bruijn stack):
    they touch disjoint fields of `REnv`. -/
theorem REnv.push_write_comm (γ : REnv) (w : Val) (x : EVar) (v : Val) :
    (γ.write x v).push w = (γ.push w).write x v := by
  apply REnv.ext <;> rfl


/-! ## Rename keystone: interpretation

  Renaming `x → y` corresponds to copying `y`'s cell into `x` with the Val-level
  `write`. -/

theorem REnv.get_write_other (b : Base) (γ : REnv) (x : EVar) (v : Val) {y : EVar}
    (h : x ≠ y) : REnv.get b (γ.write x v) y = REnv.get b γ y := by
  have hxy : (x == y) = false := by simp [h]
  simp [REnv.get, REnv.lookup, hxy]

/-! ## write-at-fresh-variable invariance of interpretation

  Writing *any* `Val` at a name not occurring in a term/formula leaves its
  interpretation unchanged. Generalizes `interp_update_fresh_*` to arbitrary
  written values (incl. closures) — needed because the merged extension
  `γ.write`.write may store a closure at a fresh higher-order binder. -/

theorem Term.interp_write_fresh {b : Base} (t : Term b)
    (x : EVar) (v : Val) (γ : REnv) (h : x ∉ t.fv) :
    Term.interp (γ.write x v) t = Term.interp γ t := by
  induction t with
  | const _ _ => rfl
  | bvar bv _ => cases bv <;> rfl
  | fvar bv y =>
    have hxy : x ≠ y := fun he => h (by subst he; simp [Term.fv])
    exact REnv.get_write_other bv γ x v hxy
  | mbvar _ _ => rfl
  | mfvar m y =>
    have hxy : x ≠ y := fun he => h (by subst he; simp [Term.fv])
    simp [Term.interp, REnv.write, hxy]
  | add t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]
  | not t ih => simp only [Term.interp, ih h]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [Term.fv, List.mem_append, not_or] at h
    simp only [Term.interp, ih₁ h.1, ih₂ h.2]

theorem Formula.interp_write_fresh (φ : Formula)
    (x : EVar) (v : Val) (γ : REnv)
    (hfv : x ∉ φ.fv) :
    Formula.interp (γ.write x v) φ ↔ Formula.interp γ φ := by
  have not_mem_l : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₁ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inl ha))
  have not_mem_r : ∀ (a : EVar) (l₁ l₂ : List EVar), a ∉ l₁ ++ l₂ → a ∉ l₂ :=
    fun a l₁ l₂ hh ha => hh (List.mem_append.mpr (Or.inr ha))
  induction φ generalizing γ with
  | tt => simp [Formula.interp]
  | ff => simp [Formula.interp]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp,
      Term.interp_write_fresh t₁ x v γ (not_mem_l _ _ _ hfv),
      Term.interp_write_fresh t₂ x v γ (not_mem_r _ _ _ hfv)]
  | and φ₁ φ₂ ih₁ ih₂ | or φ₁ φ₂ ih₁ ih₂ | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [Formula.fv, List.mem_append, not_or] at hfv
    simp only [Formula.interp, ih₁ γ hfv.1, ih₂ γ hfv.2]
  | not φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    exact not_congr (ih γ hfv)
  | ex _ φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    refine exists_congr (fun n => ?_)
    rw [REnv.push_write_comm]
    exact ih (γ.push _) hfv
  | all _ φ ih =>
    simp only [Formula.fv] at hfv
    simp only [Formula.interp]
    refine forall_congr' (fun n => ?_)
    rw [REnv.push_write_comm]
    exact ih (γ.push _) hfv

/-! ## Model-level bridge for the shifting open: `openBVar` = `insertBV`

  `openBVar k` opens the de Bruijn level `k` to the free name `x` and shifts
  deeper indices down; interpreting the opened term through a `write`-updated
  name map (`x ↦ w`) agrees with interpreting the original through a value
  `insertBV`-ed into the de Bruijn stack at level `k`. The bridge is
  **premise-free** beyond `k ≤ len` and freshness `x ∉ fv` — no well-formedness
  hypothesis — which is what keeps the VCGen soundness chain WF-free. ν-opening
  is the `k = 0` case (`insertBV 0 = push`), which is what lets `Subtyp.refine`
  be stated in *opened* form (mirroring `Subtyp.arrow`). We prove the general
  `insertBV k` form so the induction goes under `Formula` quantifiers. -/

theorem REnv.write_push (γ : REnv) (x : EVar) (w u : Val) :
    (γ.write x w).push u = (γ.push u).write x w := rfl

theorem Term.interp_openBVar {b : Base} (x : EVar) (w : Val) :
    ∀ (t : Term b) (γ : REnv) (k : Nat),
      k ≤ γ.bv.length → x ∉ t.fv →
      Term.interp (γ.write x w) (t.openBVar k x) = Term.interp (γ.insertBV k w) t := by
  intro t
  induction t with
  | const b c => intro γ k _ _; rfl
  | bvar b j =>
      intro γ k hk _
      by_cases hjk : j = k
      · subst hjk
        simp only [Term.openBVar, Term.interp, REnv.get, REnv.lookup,
          REnv.write, beq_self_eq_true, if_true, REnv.getBV, REnv.insertBV_bv, REnv.insertBV_sorts,
          List.getElem?_insertIdx_self, hk, if_true, Option.getD_some]
      · simp only [Term.openBVar, if_neg hjk, Term.interp, REnv.getBV,
          REnv.insertBV_bv, REnv.insertBV_sorts]
        by_cases hlt : k < j
        · rw [if_pos hlt, Term.interp, REnv.getBV,
            List.getElem?_insertIdx_of_gt hlt]
        · rw [if_neg hlt, Term.interp, REnv.getBV,
            List.getElem?_insertIdx_of_lt (by omega)]
  | fvar b y =>
      intro γ k _ hx
      simp only [Term.fv, List.mem_singleton] at hx
      simp only [Term.openBVar, Term.interp, REnv.get, REnv.lookup, REnv.write,
        REnv.insertBV_map, REnv.insertBV_sorts, beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true,
        if_false]
  | mbvar m j =>
      intro γ k hk _
      by_cases hjk : j = k
      · subst hjk
        simp only [Term.openBVar, Term.interp, REnv.write, beq_self_eq_true, if_true,
          REnv.insertBV_bv, REnv.insertBV_sorts, List.getElem?_insertIdx_self, hk, if_true,
          Option.getD_some]
      · simp only [Term.openBVar, if_neg hjk]
        by_cases hlt : k < j
        · rw [if_pos hlt]
          simp only [Term.interp, REnv.insertBV_bv, REnv.insertBV_sorts]
          rw [List.getElem?_insertIdx_of_gt hlt]
        · rw [if_neg hlt]
          simp only [Term.interp, REnv.insertBV_bv, REnv.insertBV_sorts]
          rw [List.getElem?_insertIdx_of_lt (by omega)]
  | mfvar m y =>
      intro γ k _ hx
      simp only [Term.fv, List.mem_singleton] at hx
      simp only [Term.openBVar, Term.interp, REnv.write, REnv.insertBV_map, REnv.insertBV_sorts,
        beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true, if_false]
  | add t₁ t₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Term.fv, List.mem_append, not_or] at hx
      simp only [Term.openBVar, Term.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | not t ih =>
      intro γ k hk hx
      simp only [Term.fv] at hx
      simp only [Term.openBVar, Term.interp, ih γ k hk hx]
  | and t₁ t₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Term.fv, List.mem_append, not_or] at hx
      simp only [Term.openBVar, Term.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]

theorem Formula.interp_openBVar (x : EVar) (w : Val) :
    ∀ (φ : Formula) (γ : REnv) (k : Nat),
      k ≤ γ.bv.length → x ∉ φ.fv →
      (Formula.interp (γ.write x w) (φ.openBVar k x) ↔ Formula.interp (γ.insertBV k w) φ) := by
  intro φ
  induction φ with
  | tt => intro γ k _ _; simp [Formula.openBVar, Formula.interp]
  | ff => intro γ k _ _; simp [Formula.openBVar, Formula.interp]
  | eq b t₁ t₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp,
        Term.interp_openBVar x w t₁ γ k hk hx.1,
        Term.interp_openBVar x w t₂ γ k hk hx.2]
      exact Iff.rfl
  | leq _ t₁ t₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp,
        Term.interp_openBVar x w t₁ γ k hk hx.1,
        Term.interp_openBVar x w t₂ γ k hk hx.2]
      exact Iff.rfl
  | and φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | or φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | not φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.openBVar, Formula.interp, ih γ k hk hx]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp, ih₁ γ k hk hx.1, ih₂ γ k hk hx.2]
  | ex b φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.openBVar, Formula.interp]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [REnv.write_push] at hv
        rw [REnv.push_insertBV_comm]
        exact (ih (γ.push (Val.inj (b.resolve γ.sorts) v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mp hv
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [REnv.write_push]
        rw [REnv.push_insertBV_comm] at hv
        exact (ih (γ.push (Val.inj (b.resolve γ.sorts) v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mpr hv
  | all b φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.openBVar, Formula.interp]
      constructor
      · intro h v
        rw [REnv.push_insertBV_comm]
        have := h v
        rw [REnv.write_push] at this
        exact (ih (γ.push (Val.inj (b.resolve γ.sorts) v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mp this
      · intro h v
        rw [REnv.write_push]
        have := h v
        rw [REnv.push_insertBV_comm] at this
        exact (ih (γ.push (Val.inj (b.resolve γ.sorts) v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mpr this

/-- Model-level bridge (refinement level): interpreting the `openBVar`-opened
    refinement against a `write`-updated name-map slot equals interpreting the
    original against a value `insertBV`-ed into the de Bruijn stack at level `k`.
    Premise-free beyond `k ≤ len` and freshness. The `k = 0` case
    (`insertBV 0 = push`) bridges the generator's named `.all` binder and the
    opened `Subtyp.refine` with the `push`-based denotation. -/
theorem Refinement.interp_openBVar (κ : KEnv) (r : Refinement) (γ : REnv)
    (x : EVar) (w : Val) (k : Nat) (hk : k ≤ γ.bv.length) (hx : x ∉ r.fv) :
    Refinement.interp κ (r.openBVar k x) (γ.write x w) ↔
    Refinement.interp κ r (γ.insertBV k w) := by
  induction r with
  | conj r₁ r₂ ih₁ ih₂ =>
      simp only [Refinement.fv, List.mem_append, not_or] at hx
      simp only [Refinement.openBVar, Refinement.interp]
      exact and_congr (ih₁ hx.1) (ih₂ hx.2)
  | fmla φ =>
      simp only [Refinement.openBVar, Refinement.interp]
      exact Formula.interp_openBVar x w φ γ k hk (by simpa [Refinement.fv] using hx)
  | kapp kn args =>
      have hmap :
          (List.map (fun a => Base.canonArg (γ.write x w).sorts a.1 (Term.interp (γ.write x w) a.2))
            (List.map (fun a => (⟨a.1, Term.openBVar k x a.2⟩ : Σ b : Base, Term b)) args))
          = List.map (fun a => Base.canonArg (γ.insertBV k w).sorts a.1
              (Term.interp (γ.insertBV k w) a.2)) args := by
        rw [List.map_map]
        apply List.map_congr_left
        intro a ha
        have hxa : x ∉ Term.fv a.2 := by
          simp only [Refinement.fv] at hx
          exact fun h => hx (List.mem_flatMap.mpr ⟨a, ha, h⟩)
        have h := Term.interp_openBVar x w a.2 γ k hk hxa
        simp only [Function.comp_apply, h]
        rfl
      simp only [Refinement.openBVar, Refinement.interp, hmap]

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

/-- Every intermediate stage of `instTysFrom i τs P` is well-formed (stage `i`
    still has parameters `0 … i-1` free). -/
def Ty.instTysOK (ks : List Kind) (i : Nat) : List Ty → Ty → Bool
  | [],      P => P.wfB (ks.take i) []
  | τ :: τs, P => (Ty.instTysFrom i (τ :: τs) P).wfB (ks.take i) [] && Ty.instTysOK ks (i+1) τs P

/-- The declaration of datatype `C`. -/
def DEnv.nCtors (de : DEnv) (C : String) : Option Nat := (de.decl? C).map (·.ctors.length)

/-- `C[τs]` is a legal instance: the arity matches, each argument is a closed
    well-formed type of a kind its parameter admits, and every constructor's
    payload instantiates to well-formed types (at every stage). -/
def DEnv.instOK (de : DEnv) (C : String) (τs : List Ty) : Bool :=
  match de.decl? C with
  | none   => false
  | some d =>
      d.params.length == τs.length &&
      (List.zip τs d.params).all (fun p => decide (Kind.le p.1.kindOf p.2) && p.1.wfB [] []) &&
      d.ctors.all (fun c => Ty.instTysOK d.params 0 τs c.2)

/-- The polarity of a position in a type. -/
inductive Pol where
  | pos  : Pol
  | neg  : Pol
  | both : Pol
  deriving Repr, DecidableEq

def Pol.flip : Pol → Pol
  | .pos => .neg
  | .neg => .pos
  | .both => .both

/-- The polarity of an argument position of a datatype with the given variance. -/
def Pol.comp (p : Pol) : Variance → Pol
  | .co     => p
  | .contra => p.flip
  | .inv    => .both

/-- A parameter of this variance may occur at this polarity. -/
def Variance.allows : Variance → Pol → Bool
  | .inv,    _    => true
  | .co,     .pos => true
  | .contra, .neg => true
  | _,       _    => false

/-- The parameters (`tbvar d`, `tbvar (d+1)`, … — `d` counts enclosing `∀`s)
    occur in `t` only at polarities their declared variances `vs` allow. A
    datatype argument's polarity follows that datatype's declared variance. -/
def Ty.varOK (de : DEnv) (vs : List Variance) : Nat → Pol → Ty → Bool
  | d, p, .refine (.tbvar j) _ => if j < d then true else ((vs[j - d]?).getD .inv).allows p
  | _, _, .refine _ _     => true
  | d, p, .arrow s t      => Ty.varOK de vs d p.flip s && Ty.varOK de vs d p t
  | d, p, .forall _ t     => Ty.varOK de vs (d+1) p t
  | d, p, .prod s t       => Ty.varOK de vs d p s && Ty.varOK de vs d p t
  | d, p, .data C n args _ => (List.finRange n).all fun l => Ty.varOK de vs d (p.comp (de.var C l)) (args l)

/-- Well-formed measures: distinct names, and every body reads only fields of
    its constructor. -/
def DataDecl.measOK (d : DataDecl) : Bool :=
  decide (d.measures.map Prod.fst).Nodup &&
  d.measures.all fun mb => (mb.2.zip d.ctorFields).all fun bc => bc.1.idxOK bc.2.2.length

/-- Well-formed declarations: payloads have no free term or type variables, and
    respect the declared variances; measures are well-formed. -/
def DEnv.wfB (de : DEnv) : Bool :=
  (de.all fun d => d.2.ctors.all fun c =>
    c.2.fv.isEmpty && c.2.ftv.isEmpty && Ty.varOK de d.2.variances 0 .pos c.2) &&
  de.all fun d => d.2.measOK

theorem DEnv.payload?_lt {de : DEnv} {C : String} {j m : Nat} {P : Ty}
    (hm : de.nCtors C = some m) (hP : de.payload? C j = some P) : j < m := by
  simp only [DEnv.nCtors, DEnv.payload?] at hm hP
  cases hd : de.decl? C with
  | none => simp [hd] at hm
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq, Option.bind_some] at hm hP
    subst hm
    cases h : d.ctors[j]? with
    | none => simp [h] at hP
    | some c => exact (List.getElem?_eq_some_iff.mp h).1

theorem DEnv.payload?_of_lt {de : DEnv} {C : String} {j m : Nat}
    (hm : de.nCtors C = some m) (hj : j < m) : ∃ P, de.payload? C j = some P := by
  simp only [DEnv.nCtors, DEnv.payload?] at hm ⊢
  cases hd : de.decl? C with
  | none => simp [hd] at hm
  | some d =>
    simp only [hd, Option.map_some, Option.some.injEq, Option.bind_some] at hm ⊢
    subst hm
    exact ⟨d.ctors[j].2, by simp [List.getElem?_eq_getElem hj]⟩

/-- What `instOK` guarantees. -/
theorem DEnv.instOK_spec {de : DEnv} {C : String} {τs : List Ty} (h : de.instOK C τs = true) :
    ∃ d, de.decl? C = some d ∧ d.params.length = τs.length ∧
      (∀ i (hi : i < τs.length), ∃ k, d.params[i]? = some k ∧ Kind.le τs[i].kindOf k ∧
        τs[i].wfB [] [] = true) ∧
      ∀ c ∈ d.ctors, Ty.instTysOK d.params 0 τs c.2 = true := by
  unfold DEnv.instOK at h
  cases hd : de.decl? C with
  | none => simp [hd] at h
  | some d =>
    simp only [hd, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hlen, hargs⟩, hctors⟩ := h
    refine ⟨d, rfl, hlen, fun i hi => ?_, hctors⟩
    have hmem : (τs[i], d.params[i]'(by omega)) ∈ List.zip τs d.params := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp [List.length_zip]; omega, by simp [List.getElem_zip]⟩
    have := hargs _ hmem
    simp only [decide_eq_true_eq] at this
    exact ⟨_, List.getElem?_eq_getElem (by omega), this⟩

/-- The type arguments of a legal instance are well-formed. -/
theorem Formula.hasBVar_conjAll {b : Base} {k : Nat} : ∀ (φs : List Formula),
    Formula.hasBVar b k (Formula.conjAll φs) → ∃ φ ∈ φs, Formula.hasBVar b k φ
  | [], h => by simp [Formula.conjAll, Formula.hasBVar] at h
  | φ :: φs, h => by
    simp only [Formula.conjAll, Formula.hasBVar] at h
    rcases h with h | h
    · exact ⟨φ, List.mem_cons_self, h⟩
    · obtain ⟨ψ, hψ, h⟩ := Formula.hasBVar_conjAll φs h
      exact ⟨ψ, List.mem_cons_of_mem _ hψ, h⟩

theorem MBody.toTerm_noBVar {msr : String → Nat → Term .int}
    (hm : ∀ m i b k, ¬ Term.hasBVar b k (msr m i)) :
    ∀ (body : MBody) b k, ¬ Term.hasBVar b k (body.toTerm msr)
  | .const _, b, k => by simp [MBody.toTerm, Term.hasBVar]
  | .meas m i, b, k => hm m i b k
  | .add x y, b, k => by
    simp only [MBody.toTerm, Term.hasBVar, not_or]
    exact ⟨MBody.toTerm_noBVar hm x b k, MBody.toTerm_noBVar hm y b k⟩

/-- A constructor's measure facts mention no sorted bound variable (they read
    ν and the fields only through measures). -/
theorem DEnv.ctorRefine_noBVar (de : DEnv) (C : String) (j : Nat) (e : Exp) :
    ∀ b k, ¬ (de.ctorRefine C j e).hasBVar b k := by
  intro b k h
  unfold DEnv.ctorRefine at h
  split at h
  · simp only [DEnv.ctorFacts, Refinement.hasBVar] at h
    obtain ⟨φ, hφ, h⟩ := Formula.hasBVar_conjAll _ h
    simp only [List.mem_map] at hφ
    obtain ⟨mb, _, rfl⟩ := hφ
    simp only [Formula.hasBVar, Term.hasBVar, false_or] at h
    exact MBody.toTerm_noBVar (fun _ _ _ _ h => by split at h <;> simp [Term.hasBVar] at h) _ _ _ h
  · simp [Refinement.hasBVar, Formula.hasBVar] at h

theorem DEnv.caseFacts_noBVar (de : DEnv) (C : String) (j n : Nat) (x : EVar) :
    ∀ b k, ¬ (de.caseFacts C j n x).hasBVar b k := by
  intro b k h
  simp only [DEnv.caseFacts, Refinement.hasBVar] at h
  obtain ⟨φ, hφ, h⟩ := Formula.hasBVar_conjAll _ h
  simp only [List.mem_map] at hφ
  obtain ⟨mb, _, rfl⟩ := hφ
  simp only [Formula.hasBVar, Term.hasBVar, false_or] at h
  exact MBody.toTerm_noBVar (fun _ _ _ _ h => by simp [Term.hasBVar] at h) _ _ _ h

theorem Ty.WFBVarCtx_strengthenLast {r : Refinement} (hr : ∀ b k, ¬ r.hasBVar b k) :
    ∀ (n : Nat) (t : Ty) (ctx : List (Option Base)), Ty.WFBVarCtx ctx t →
      Ty.WFBVarCtx ctx (t.strengthenLast n r)
  | 0, .refine b r', ctx, h => by
    simp only [Ty.strengthenLast, Ty.WFBVarCtx, Refinement.hasBVar] at h ⊢
    rintro b' k (hk | hk)
    · exact h b' k hk
    · exact absurd hk (hr b' k)
  | 0, .data C k a r', ctx, h => by
    simp only [Ty.strengthenLast, Ty.WFBVarCtx, Refinement.hasBVar] at h ⊢
    refine ⟨?_, h.2⟩
    rintro b' i (hk | hk)
    · exact h.1 b' i hk
    · exact absurd hk (hr b' i)
  | n + 1, .prod s t, ctx, h => by
    simp only [Ty.strengthenLast, Ty.WFBVarCtx] at h ⊢
    exact ⟨h.1, Ty.WFBVarCtx_strengthenLast hr n t _ h.2⟩
  | 0, .arrow _ _, _, h | 0, .forall _ _, _, h | 0, .prod _ _, _, h => by
    simpa [Ty.strengthenLast] using h
  | _ + 1, .refine _ _, _, h | _ + 1, .arrow _ _, _, h | _ + 1, .forall _ _, _, h
  | _ + 1, .data _ _ _ _, _, h => by
    simpa [Ty.strengthenLast] using h

theorem DEnv.altTy_WFBVars (de : DEnv) (C : String) (j : Nat) (x? : Option EVar) {tz : Ty}
    (h : Ty.WFBVars tz) : Ty.WFBVars (de.altTy C j x? tz) := by
  cases x? with
  | none => exact h
  | some x => exact Ty.WFBVarCtx_strengthenLast (DEnv.caseFacts_noBVar _ _ _ _ _) _ tz [] h

theorem DEnv.instOK_WFBVars {de : DEnv} {C : String} {τs : List Ty} {r : Refinement}
    (h : de.instOK C τs = true) (hr : ∀ b k, ¬ r.hasBVar b k) :
    Ty.WFBVars (Ty.dataL C τs r) := by
  obtain ⟨d, _, _, hargs, _⟩ := DEnv.instOK_spec h
  refine ⟨fun b k h => absurd h (hr b k), fun i => ?_⟩
  obtain ⟨_, _, _, hw⟩ := hargs i.val i.isLt
  exact Ty.wfB_WFBVarCtx _ hw

/-- The first stage checked by `instTysOK` is the full instantiation. -/
theorem Ty.instTysOK_wfB {ks : List Kind} {i : Nat} {τs : List Ty} {P : Ty}
    (h : Ty.instTysOK ks i τs P = true) : (Ty.instTysFrom i τs P).wfB (ks.take i) [] = true := by
  cases τs with
  | nil => simpa [Ty.instTysOK, Ty.instTysFrom] using h
  | cons τ τs =>
    simp only [Ty.instTysOK, Bool.and_eq_true] at h
    exact h.1

/-- A payload at a legal instance is a closed well-formed type. -/
theorem DEnv.instOK_payload_wfB {de : DEnv} {C : String} {τs : List Ty} {j : Nat} {P : Ty}
    (h : de.instOK C τs = true) (hP : de.payload? C j = some P) :
    (Ty.instTys τs P).wfB [] [] = true := by
  obtain ⟨d, hd, _, _, hctors⟩ := DEnv.instOK_spec h
  simp only [DEnv.payload?, hd, Option.bind_some, Option.map_eq_some_iff] at hP
  obtain ⟨c, hc, rfl⟩ := hP
  have := Ty.instTysOK_wfB (hctors c (List.mem_of_getElem? hc))
  simpa using this

theorem List.mem_of_lookup_eq_some' {β : Type} :
    ∀ {l : List (String × β)} {a : String} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp at h
  | (a', b') :: tl, a, b, h => by
    simp only [List.lookup] at h
    by_cases ha : a = a'
    · subst ha
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h; simp
    · have hne : (a == a') = false := by simp [ha]
      simp only [hne] at h
      exact List.mem_cons_of_mem _ (List.mem_of_lookup_eq_some' h)

/-- The declaration and payload behind a successful `payload?` lookup. -/
theorem DEnv.payload?_mem {de : DEnv} {C : String} {j : Nat} {P : Ty}
    (hP : de.payload? C j = some P) :
    ∃ d c, de.decl? C = some d ∧ (C, d) ∈ de ∧ c ∈ d.ctors ∧ c.2 = P := by
  simp only [DEnv.payload?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hP
  obtain ⟨d, hd, c, hc, rfl⟩ := hP
  exact ⟨d, c, hd, List.mem_of_lookup_eq_some' hd, List.mem_of_getElem? hc, rfl⟩

theorem DEnv.wfB_payload_all {de : DEnv} (h : de.wfB = true) {C : String} {j : Nat} {P : Ty}
    (hP : de.payload? C j = some P) :
    ∃ d, de.decl? C = some d ∧ P.fv = [] ∧ P.ftv = [] ∧ Ty.varOK de d.variances 0 .pos P = true := by
  obtain ⟨d, c, hd, hmem, hc, rfl⟩ := DEnv.payload?_mem hP
  simp only [DEnv.wfB, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 (C, d) hmem c hc
  simp only [Bool.and_eq_true, List.isEmpty_iff] at this
  exact ⟨d, hd, this.1.1, this.1.2, this.2⟩

/-- Payloads of well-formed declarations have no free term or type variables. -/
theorem DEnv.wfB_payload {de : DEnv} (h : de.wfB = true) {C : String} {j : Nat} {P : Ty}
    (hP : de.payload? C j = some P) : P.fv = [] ∧ P.ftv = [] := by
  obtain ⟨_, _, h1, h2, _⟩ := DEnv.wfB_payload_all h hP
  exact ⟨h1, h2⟩

/-- The facts a legal instance gives about one constructor's payload. -/
theorem DEnv.instOK_payload_ok {de : DEnv} {C : String} {τs : List Ty} {j : Nat} {P : Ty}
    (h : de.instOK C τs = true) (hP : de.payload? C j = some P) :
    ∃ ks : List Kind, ks.length = τs.length ∧
      (∀ l (hl : l < τs.length), ∃ kd, ks[l]? = some kd ∧ Kind.le τs[l].kindOf kd ∧
        τs[l].wfB [] [] = true) ∧
      Ty.instTysOK ks 0 τs P = true := by
  obtain ⟨d, hd, hlen, hargs, hctors⟩ := DEnv.instOK_spec h
  simp only [DEnv.payload?, hd, Option.bind_some, Option.map_eq_some_iff] at hP
  obtain ⟨c, hc, rfl⟩ := hP
  exact ⟨d.params, hlen, hargs, hctors c (List.mem_of_getElem? hc)⟩

/-- The last stage checked by `instTysOK` is the payload itself. -/
theorem Ty.instTysOK_last {ks : List Kind} {P : Ty} :
    ∀ {i : Nat} {τs : List Ty}, Ty.instTysOK ks i τs P = true →
      P.wfB (ks.take (i + τs.length)) [] = true
  | i, [], h => by simpa [Ty.instTysOK] using h
  | i, τ :: τs, h => by
    simp only [Ty.instTysOK, Bool.and_eq_true] at h
    have := Ty.instTysOK_last h.2
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

end STLC
