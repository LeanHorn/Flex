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
  | _, .not t        => .not (Term.openBVar k x t)
  | _, .and t₁ t₂    => .and (Term.openBVar k x t₁) (Term.openBVar k x t₂)

/-! ## 2. Formula operations -/

/-- Free variables of a formula. The quantifiers are locally nameless, so they
    bind no name and just pass their body's fv through. -/
def Formula.fv : Formula → List EVar
  | .tt           => []
  | .ff           => []
  | .eq _ t₁ t₂   => t₁.fv ++ t₂.fv
  | .leqI t₁ t₂   => t₁.fv ++ t₂.fv
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
  | .leqI t₁ t₂   => .leqI (t₁.openBVar k x) (t₂.openBVar k x)
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

/-- Open the `BVar` at level `k` (base-agnostic, shifting; see `Term.openBVar`).
    ν-instantiation is the `k = 0` case: `r.openBVar 0 x` replaces ν (`bvar _ 0`)
    with the free name `x` and shifts deeper indices down. -/
def Refinement.openBVar (k : Nat) (x : EVar)
    (r : Refinement) : Refinement :=
  match r with
  | .fmla φ       => .fmla (φ.openBVar k x)
  | .kapp kn args => .kapp kn (args.map (fun a => ⟨a.1, Term.openBVar k x a.2⟩))

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
  | x, .refine .int  _ => .refine .int  (.fmla
      (.eq .int (.bvar .int  0) (.fvar .int  x)))
  | x, .refine .bool _ => .refine .bool (.fmla
      (.eq .bool (.bvar .bool 0) (.fvar .bool x)))
  | _, .arrow t1 t2    => .arrow t1 t2

/-! ## 4. Ty operations (locally nameless)

  `Ty.openVar k x t` opens the `BVar` at level `k` to `fvar x` throughout
  refinements in `t`. Crossing a `Ty.arrow` binder bumps the level: `arrow`'s
  domain stays at the parent level, its codomain is at `k+1`.
-/

def Ty.fv : Ty → List EVar
  | .refine _ r => r.fv
  | .arrow s t  => Ty.fv s ++ Ty.fv t

/-- Open a `Ty`'s outermost binder at level `k` with free name `x`. Opens the
    refinement `BVar` at level `k+1` — the `+1` because ν occupies formula-level
    0, so arrow binders live one level out. One base-agnostic, shifting
    `openBVar` handles both bases at once. -/
def Ty.openVar (k : Nat) (x : EVar) : Ty → Ty
  | .refine b r => .refine b (r.openBVar (k+1) x)
  | .arrow s t  => .arrow (s.openVar k x) (t.openVar (k+1) x)

@[simp]
theorem Ty.skel_openVar (k : Nat) (x : EVar) (t : Ty) :
    (t.openVar k x).skel = t.skel := by
  induction t generalizing k with
  | refine _ _ => rfl
  | arrow s t ihs iht => simp [Ty.openVar, Ty.skel, ihs, iht]

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
  | _, .not t      => Term.hasBVar b k t
  | _, .and t₁ t₂  => Term.hasBVar b k t₁ ∨ Term.hasBVar b k t₂

/-- `Formula.hasBVar b k φ`: φ contains at least one `Term.bvar b k`. -/
def Formula.hasBVar (b : Base) (k : Nat) : Formula → Prop
  | .tt | .ff => False
  | .eq _ t₁ t₂ | .leqI t₁ t₂ =>
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

/-- Extract the base of a refinement type; None for arrow types. -/
def Ty.optBase : Ty → Option Base
  | .refine b _ => some b
  | .arrow _ _  => none

/-- `Ty.WFBVarCtx ctx t`: at nesting depth k, all `BVar b k` in `t`'s
    refinement formulas satisfy `(some bᵣ :: ctx)[k]? = some (some b)`, where
    `bᵣ` is the refinement's own base. Level 0 is ν (always base `bᵣ`); level
    `k+1` is the k-th outer arrow binder (`ctx[k]`). -/
def Ty.WFBVarCtx : List (Option Base) → Ty → Prop
  | ctx, .refine br r =>
      ∀ (b : Base) (k : Nat), Refinement.hasBVar b k r → (some br :: ctx)[k]? = some (some b)
  | ctx, .arrow s t  =>
      Ty.WFBVarCtx ctx s ∧ Ty.WFBVarCtx (s.optBase :: ctx) t

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
  | add t₁ t₂ ih1 ih2 => simp only [Term.openBVar, Term.hasBVar, ih1, ih2]; grind
  | not t ih  => simp only [Term.openBVar, Term.hasBVar, ih]
  | and t₁ t₂ ih1 ih2 => simp only [Term.openBVar, Term.hasBVar, ih1, ih2]; grind

theorem Formula.hasBVar_openBVar (φ : Formula) (b : Base) (i k : Nat) (x : EVar) :
    Formula.hasBVar b i (φ.openBVar k x) ↔
      (i < k ∧ Formula.hasBVar b i φ) ∨ (k ≤ i ∧ Formula.hasBVar b (i+1) φ) := by
  induction φ generalizing i k with
  | tt | ff => simp [Formula.hasBVar, Formula.openBVar]
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
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
  cases r with
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
  induction t generalizing ctx with
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
    refine ⟨ihs ctx hWF.1, ?_⟩
    -- Codomain uses IH with ctx' = s.optBase :: ctx
    have ih := iht (s.optBase :: ctx) (by simpa using hWF.2)
    simp only [List.length_cons] at ih
    rw [Ty.optBase_openVar]
    exact ih

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
  | ann _ _ ih         => simp [Exp.openVar, Exp.skel, ih]
  | and _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | not _ ih           => simp [Exp.openVar, Exp.skel, ih]
  | leq _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | ite _ _ _ ih₀ ih₁ ih₂ => simp [Exp.openVar, Exp.skel, ih₀, ih₁, ih₂]
  | add _ _ ih₁ ih₂    => simp [Exp.openVar, Exp.skel, ih₁, ih₂]
  | unreach            => rfl
  | fix _ ih           => simp [Exp.openVar, Exp.skel, ih]

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

/-! ## 9. Freshness helper

  `EVar.fresh L` returns a name not in `L`, by producing a string longer than
  any element of `L`. The freshness proof lives in Stage 2b. -/

def EVar.maxLen : List EVar → Nat
  | []      => 0
  | x :: xs => Nat.max x.length (EVar.maxLen xs)

def EVar.fresh (L : List EVar) : EVar :=
  String.ofList (List.replicate (EVar.maxLen L + 1) 'x')

/-! ## 10. REnv helpers -/

@[simp] theorem REnv.get_update_same (b : Base) (γ : REnv) (x : EVar) (v : b.interp) :
    REnv.get b (γ.update b x v) x = v := by
  cases b <;> simp [REnv.get]

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

/-- A closed expression is fixed under the closing substitution. -/
theorem Exp.substEnv_closed (γ : REnv) (e : Exp) (he : e.fv = []) :
    Exp.substEnv γ e = e := by
  induction e with
  | bvar _ | iconst _ | bconst _ | unreach => rfl
  | fvar y => simp [Exp.fv] at he
  | lam body ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | fix body ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | ann e t ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | not e ih => simp only [Exp.fv] at he; simp only [Exp.substEnv, ih he]
  | letin e₁ e₂ ih₁ ih₂ | app e₁ e₂ ih₁ ih₂ | and e₁ e₂ ih₁ ih₂
  | leq e₁ e₂ ih₁ ih₂ | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.fv, List.append_eq_nil_iff] at he
    simp only [Exp.substEnv, ih₁ he.1, ih₂ he.2]
  | ite e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
    simp only [Exp.fv, List.append_eq_nil_iff] at he
    simp only [Exp.substEnv, ih₀ he.1.1, ih₁ he.1.2, ih₂ he.2]

theorem Val.toExp_closed_of_closed {v : Val} (h : Val.closed v) : v.toExp.fv = [] := by
  cases v with
  | iconst _   => simp [Val.toExp, Exp.fv]
  | bconst _   => simp [Val.toExp, Exp.fv]
  | clos body  =>
    simp [Val.closed, Val.fv] at h
    simp [Val.toExp, Exp.fv, h]
  | fclos body =>
    simp [Val.closed, Val.fv] at h
    simp [Val.toExp, Exp.fv, h]

theorem Val.toExp_lc_at_zero {v : Val} (h : Val.lc v) : Exp.lc_at 0 v.toExp := by
  cases v with
  | iconst _  => simp [Val.toExp, Exp.lc_at]
  | bconst _  => simp [Val.toExp, Exp.lc_at]
  | clos body =>
    simp only [Val.lc] at h
    simp only [Val.toExp, Exp.lc_at]
    exact h
  | fclos body =>
    simp only [Val.lc] at h
    simp only [Val.toExp, Exp.lc_at]
    exact h

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
  | ann e t ih => exact ih fun z hz => hcl z (by simpa [Exp.fv] using hz)
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
  | ann e t ih =>
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
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.openVar, Exp.lc_at] at h ⊢
    exact ⟨ih₁ k h.1, ih₂ k h.2⟩

/-- Opening a binder with `y` adds at most `y` to the free names. -/
theorem Exp.fv_openVar {e : Exp} {k : Nat} {y z : EVar}
    (h : z ∈ (e.openVar k y).fv) : z ∈ e.fv ∨ z = y := by
  induction e generalizing k with
  | bvar j =>
    simp only [Exp.openVar] at h
    split at h <;> simp_all [Exp.fv]
  | fvar _ | iconst _ | bconst _ | unreach => simp_all [Exp.openVar, Exp.fv]
  | lam _ ih | ann _ _ ih | not _ ih | fix _ ih =>
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
  | ann e t ih =>
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
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at h; simp only [Exp.openExp]; congr 1
    exact ih₁ k h.1; exact ih₂ k h.2

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
  | ann e t ih =>
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
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [Exp.lc_at] at *
    exact ⟨ih₁ hjk h.1, ih₂ hjk h.2⟩

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
  | ann e t ih =>
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

/-- The closing substitution depends only on `γ` over the free names of `e`. -/
theorem Exp.substEnv_congr (e : Exp) (γ₁ γ₂ : REnv)
    (h : ∀ z ∈ e.fv, γ₁.map z = γ₂.map z) :
    Exp.substEnv γ₁ e = Exp.substEnv γ₂ e := by
  induction e with
  | bvar _ | iconst _ | bconst _ | unreach => rfl
  | fvar x => simp only [Exp.substEnv, h x (by simp [Exp.fv])]
  | lam e ih | ann e _ ih | not e ih | fix e ih =>
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
  | ann e t ih =>
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
  | eq _ t₁ t₂ | leqI t₁ t₂ =>
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
          REnv.write, beq_self_eq_true, if_true, REnv.getBV, REnv.insertBV_bv,
          List.getElem?_insertIdx_self, hk, if_true, Option.getD_some]
      · simp only [Term.openBVar, if_neg hjk, Term.interp, REnv.getBV,
          REnv.insertBV_bv]
        by_cases hlt : k < j
        · rw [if_pos hlt, Term.interp, REnv.getBV,
            List.getElem?_insertIdx_of_gt hlt]
        · rw [if_neg hlt, Term.interp, REnv.getBV,
            List.getElem?_insertIdx_of_lt (by omega)]
  | fvar b y =>
      intro γ k _ hx
      simp only [Term.fv, List.mem_singleton] at hx
      simp only [Term.openBVar, Term.interp, REnv.get, REnv.lookup, REnv.write,
        REnv.insertBV_map, beq_eq_false_iff_ne.mpr hx, Bool.false_eq_true, if_false]
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
  | leqI t₁ t₂ =>
      intro γ k hk hx
      simp only [Formula.fv, List.mem_append, not_or] at hx
      simp only [Formula.openBVar, Formula.interp,
        Term.interp_openBVar x w t₁ γ k hk hx.1,
        Term.interp_openBVar x w t₂ γ k hk hx.2]
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
        exact (ih (γ.push (Val.inj b v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mp hv
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        rw [REnv.write_push]
        rw [REnv.push_insertBV_comm] at hv
        exact (ih (γ.push (Val.inj b v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mpr hv
  | all b φ ih =>
      intro γ k hk hx
      simp only [Formula.fv] at hx
      simp only [Formula.openBVar, Formula.interp]
      constructor
      · intro h v
        rw [REnv.push_insertBV_comm]
        have := h v
        rw [REnv.write_push] at this
        exact (ih (γ.push (Val.inj b v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mp this
      · intro h v
        rw [REnv.write_push]
        have := h v
        rw [REnv.push_insertBV_comm] at this
        exact (ih (γ.push (Val.inj b v)) (k + 1) (by simpa using Nat.succ_le_succ hk) hx).mpr this

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
  cases r with
  | fmla φ =>
      simp only [Refinement.openBVar, Refinement.interp]
      exact Formula.interp_openBVar x w φ γ k hk (by simpa [Refinement.fv] using hx)
  | kapp kn args =>
      have hmap :
          (List.map (fun a => (⟨a.1, Term.interp (γ.write x w) a.2⟩ : Σ b : Base, b.interp))
            (List.map (fun a => (⟨a.1, Term.openBVar k x a.2⟩ : Σ b : Base, Term b)) args))
          = List.map (fun a => (⟨a.1, Term.interp (γ.insertBV k w) a.2⟩ : Σ b : Base, b.interp)) args := by
        rw [List.map_map]
        apply List.map_congr_left
        intro a ha
        have hxa : x ∉ Term.fv a.2 := by
          simp only [Refinement.fv] at hx
          exact fun h => hx (List.mem_flatMap.mpr ⟨a, ha, h⟩)
        have h := Term.interp_openBVar x w a.2 γ k hk hxa
        simp only [Function.comp_apply, h]
      simp only [Refinement.openBVar, Refinement.interp, hmap]

end STLC
