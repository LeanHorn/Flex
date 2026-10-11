import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Semantics

namespace STLC

/-- Interpret a term under the single environment `γ`. `fvar` resolves through
    the name map (`REnv.get`); `bvar` resolves through the de Bruijn stack
    (`REnv.getBV`) — the values of ν and the enclosing quantifier/arrow binders
    live there.. -/
def Term.interp (γ : REnv) : {b : Base} → Term b → b.interp
  | _, .const _ c   => c
  | _, .bvar b k    => REnv.getBV b γ k
  | _, .fvar b x    => REnv.get b γ x
  | _, .add t₁ t₂   => Term.interp γ t₁ + Term.interp γ t₂
  | _, .not t       => !Term.interp γ t
  | _, .and t₁ t₂   => Term.interp γ t₁ && Term.interp γ t₂

/-- Interpret a (now κ-free) formula under `γ`. Each quantifier binds `BVar 0`,
    so it `push`es its witness value as the new innermost de Bruijn slot of `γ`
    and recurses. -/
def Formula.interp (γ : REnv) : Formula → Prop
  | .tt           => True
  | .ff           => False
  | .eq _ t₁ t₂   => Term.interp γ t₁ = Term.interp γ t₂
  | .leqI t₁ t₂   => Term.interp γ t₁ ≤ Term.interp γ t₂
  | .and φ₁ φ₂    => Formula.interp γ φ₁ ∧ Formula.interp γ φ₂
  | .or φ₁ φ₂     => Formula.interp γ φ₁ ∨ Formula.interp γ φ₂
  | .not φ        => ¬ Formula.interp γ φ
  | .imp φ₁ φ₂    => Formula.interp γ φ₁ → Formula.interp γ φ₂
  | .ex b φ       => ∃ x : b.interp,  Formula.interp (γ.push (Val.inj b x)) φ
  | .all b φ      => ∀ x : b.interp,  Formula.interp (γ.push (Val.inj b x)) φ

/-- Interpret a refinement under `γ`. This is the *only* interpretation
    that consults the κ-assignment. -/
def Refinement.interp (κ : KEnv) (r : Refinement) (γ : REnv) : Prop :=
  match r with
  | .fmla φ       => Formula.interp γ φ
  | .kapp kn args =>
      κ kn (args.map (fun a => ⟨a.1, Term.interp γ a.2⟩))
  | .conj r₁ r₂   => Refinement.interp κ r₁ γ ∧ Refinement.interp κ r₂ γ

/-- Interpret a syntactic constraint as a `κ`-indexed `REnv` predicate. -/
def Cstr.interp : Cstr → KEnv → REnv → Prop
  | .head r,     κ, γ => Refinement.interp κ r γ
  | .imp r c,    κ, γ => Refinement.interp κ r γ → c.interp κ γ
  | .all x b c,  κ, γ => ∀ v : b.interp, c.interp κ (REnv.update b γ x v)
  | .conj c₁ c₂, κ, γ => c₁.interp κ γ ∧ c₂.interp κ γ

/-! ## Semantic types for type variables

  A type variable is interpreted by a `SemTy`: a step-indexed, downward-closed
  predicate on (locally closed, closed) values. `Fits k` restricts the
  interpretations of a `B`-kinded variable to the values of one base sort —
  exactly the instances λ_RF allows (refined `Int`/`Bool`). -/

structure SemTy where
  rel  : Nat → Val → Prop
  mono : ∀ {j k : Nat} {v : Val}, j ≤ k → rel k v → rel j v
  wf   : ∀ {k : Nat} {v : Val}, rel k v → Val.lc v ∧ Val.closed v

/-- `R` is a legal interpretation of a type variable of kind `k`. -/
def SemTy.Fits (R : SemTy) : Kind → Prop
  | .B    => ∃ b, (b = .int ∨ b = .bool) ∧ ∀ k v, R.rel k v → v.optBase = some b
  | .star => True

/-- The interpretation used for unbound type variables (never consulted for
    well-scoped types): all locally closed, closed values. -/
def SemTy.top : SemTy :=
  ⟨fun _ v => Val.lc v ∧ Val.closed v, fun _ h => h, fun h => h⟩

/-- The integers, as a semantic type. Fits both kinds; the default
    interpretation of `B`-kinded type variables. -/
def SemTy.ints : SemTy :=
  ⟨fun _ v => ∃ n, v = .iconst n, fun _ h => h,
   fun h => by obtain ⟨n, rfl⟩ := h; exact ⟨trivial, rfl⟩⟩

theorem SemTy.ints_fits (k : Kind) : SemTy.ints.Fits k := by
  cases k with
  | B => exact ⟨.int, Or.inl rfl, fun _ v ⟨n, h⟩ => by subst h; rfl⟩
  | star => trivial

/-- Interpretation of type variables: a de Bruijn stack for the `tbvar`s
    (pushed when entering a `Ty.forall`) and a map for the `tfvar`s. -/
structure TyEnvSem where
  bv : List SemTy := []
  fv : TVar → SemTy := fun _ => SemTy.top

/-- The default interpretation: `B`-kinded variables as the integers, ⋆-kinded
    ones as all (closed) values. Satisfies `WK`. -/
def TyEnvSem.empty : TyEnvSem :=
  { bv := [], fv := fun a => match a.2 with | .B => SemTy.ints | .star => SemTy.top }

/-- Well-kindedness: every free type variable is interpreted by a semantic type
    fitting its kind (the kind is carried on the name). -/
def TyEnvSem.WK (δ : TyEnvSem) : Prop := ∀ a : TVar, (δ.fv a).Fits a.2

theorem TyEnvSem.empty_WK : TyEnvSem.empty.WK := by
  intro a
  rcases a with ⟨n, _ | _⟩
  · exact SemTy.ints_fits _
  · trivial

@[simp] def TyEnvSem.push (δ : TyEnvSem) (R : SemTy) : TyEnvSem := { δ with bv := R :: δ.bv }

/-- Denotation of a base sort at step index `k`. -/
def BaseDen (δ : TyEnvSem) (k : Nat) : Base → Val → Prop
  | .int,     v => ∃ n, v = .iconst n
  | .bool,    v => ∃ c, v = .bconst c
  | .tbvar j, v => (δ.bv[j]?.getD SemTy.top).rel k v
  | .tfvar a, v => (δ.fv a).rel k v

/-! ## Step-indexed logical relation

  `TyDenote κ δ k t γ v` — `v` is a value of type `t` (under the closing environment
  `γ` and the type-variable interpretation `δ`), *good for `k` more units of
  fuel*. A refined type `b{r}` holds the values of sort `b` satisfying `r` (with ν
  bound to the value itself). A function is good at index `k` if, for every
  `j < k` and argument good at `j`, running the body with fuel `j` never gets
  stuck and any value it returns (with `m` fuel left) is good at `m`. Since a
  β-step costs one unit of fuel, `j < k` is exactly what lets the `fix` case go
  through by induction on `k`. A polymorphic type `∀α:κ. t` holds the values
  that are in `t` under *every* legal interpretation of α — structural on the
  type, so impredicative instantiation costs nothing here. -/
def TyDenote : KEnv → TyEnvSem → Nat → Ty → REnv → Val → Prop
  | κ, δ, k, .refine b r, γ, v => BaseDen δ k b v ∧ Refinement.interp κ r (γ.push v)
  | κ, δ, k, .arrow s t,  γ, v =>
      (∃ body, v = .clos body ∨ v = .fclos body) ∧
        Val.lc v ∧ Val.closed v ∧
        ∀ j < k, ∀ va, TyDenote κ δ j s γ va →
          ∃ body o, Val.apply v va = some body ∧ Eval j body o ∧
            ∀ vr m, o = .val vr m → TyDenote κ δ m t (γ.push va) vr
  | κ, δ, k, .forall kd t, γ, v =>
      ∀ R : SemTy, R.Fits kd → TyDenote κ (δ.push R) k t γ v
termination_by _ _ _ t _ _ => t.skel
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Expression relation: with exactly `k` fuel, `e` does not get stuck, and any
    value it returns with `m` fuel left is good at index `m`. -/
def ExpDenote (κ : KEnv) (δ : TyEnvSem) (k : Nat) (t : Ty) (γ : REnv) (e : Exp) : Prop :=
  ∃ o, Eval k e o ∧ ∀ v m, o = .val v m → TyDenote κ δ m t γ v

/-- Downward closure of base denotations. -/
theorem BaseDen.mono {δ : TyEnvSem} {j k : Nat} {b : Base} {v : Val}
    (hjk : j ≤ k) (h : BaseDen δ k b v) : BaseDen δ j b v := by
  cases b with
  | int | bool => exact h
  | tbvar i => exact SemTy.mono _ hjk h
  | tfvar a => exact SemTy.mono _ hjk h

/-- Downward closure: a value good for `k` steps is good for fewer. -/
theorem TyDenote.mono {κ : KEnv} {δ : TyEnvSem} {j k : Nat} {t : Ty} {γ : REnv} {v : Val}
    (hjk : j ≤ k) (h : TyDenote κ δ k t γ v) : TyDenote κ δ j t γ v := by
  induction t generalizing δ γ v with
  | refine b r =>
    simp only [TyDenote] at h ⊢
    exact ⟨BaseDen.mono hjk h.1, h.2⟩
  | arrow s t =>
    simp only [TyDenote] at h ⊢
    obtain ⟨hf, hlc, hcl, hLR⟩ := h
    exact ⟨hf, hlc, hcl, fun i hi => hLR i (by omega)⟩
  | «forall» kd t ih =>
    simp only [TyDenote] at h ⊢
    exact fun R hR => ih (h R hR)

end STLC
