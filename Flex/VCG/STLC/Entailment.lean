import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Substitution

open STLC

/-! ## Entailment

  Refinements / formulas / models are all parameterized by a κ-assignment
  `κ : KEnv` (the interpretation of uninterpreted predicate symbols). The
  user typically writes `∃ κ : KEnv, Entail κ ...` and lets the solver pick.

  `Entail κ Γ c` (with `c : REnv → Prop`) is the entailment used by
  VCGen-produced `Constraint`s. Refinement subtyping is expressed semantically
  (see `Subtyp.refine` in `Typing.lean`), so no `Formula`-form entailment is
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

@[simp] theorem Ty.hyp?_int (r : Refinement) : (Ty.refine .int r).hyp? = some (.int, r) := rfl
@[simp] theorem Ty.hyp?_bool (r : Refinement) : (Ty.refine .bool r).hyp? = some (.bool, r) := rfl
@[simp] theorem Ty.hyp?_tfvarB (a : String) (r : Refinement) :
    (Ty.refine (.tfvar (a, .B)) r).hyp? = some (.tfvar (a, .B), r) := rfl
@[simp] theorem Ty.hyp?_tfvarStar (a : String) (r : Refinement) :
    (Ty.refine (.tfvar (a, .star)) r).hyp? = none := rfl
@[simp] theorem Ty.hyp?_tbvar (j : Nat) (r : Refinement) :
    (Ty.refine (.tbvar j) r).hyp? = none := rfl
@[simp] theorem Ty.hyp?_arrow (s t : Ty) : (Ty.arrow s t).hyp? = none := rfl
@[simp] theorem Ty.hyp?_forall (k : Kind) (t : Ty) : (Ty.forall k t).hyp? = none := rfl
@[simp] theorem Ty.hyp?_prod (s t : Ty) : (Ty.prod s t).hyp? = none := rfl
@[simp] theorem Ty.hyp?_data (C : String) (n : Nat) (args : Fin n → Ty) (r : Refinement) :
    (Ty.data C n args r).hyp? = none := rfl

/-- The hypothesis a datatype binding contributes: its refinement, which reads
    the bound value only through measures (no sort, so no `HasBase`). -/
def STLC.Ty.dhyp? : Ty → Option Refinement
  | .data _ _ _ r => some r
  | _             => none

@[simp] theorem Ty.dhyp?_data (C : String) (n : Nat) (args : Fin n → Ty) (r : Refinement) :
    (Ty.data C n args r).dhyp? = some r := rfl
@[simp] theorem Ty.dhyp?_refine (b : Base) (r : Refinement) : (Ty.refine b r).dhyp? = none := rfl
@[simp] theorem Ty.dhyp?_arrow (s t : Ty) : (Ty.arrow s t).dhyp? = none := rfl
@[simp] theorem Ty.dhyp?_forall (k : Kind) (t : Ty) : (Ty.forall k t).dhyp? = none := rfl
@[simp] theorem Ty.dhyp?_prod (s t : Ty) : (Ty.prod s t).dhyp? = none := rfl

/-- A binding never has both kinds of hypothesis. -/
theorem Ty.hyp?_of_dhyp? {t : Ty} {r : Refinement} (h : t.dhyp? = some r) : t.hyp? = none := by
  cases t <;> simp_all [Ty.dhyp?]

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

@[simp] theorem ModelsEnv.nil (κ : KEnv) (γ : REnv) : ModelsEnv κ γ [] := trivial

/-- Unfolding `ModelsEnv` at a binding whose hypothesis is known. -/
theorem ModelsEnv.cons_some {κ : KEnv} {γ : REnv} {x : EVar} {t : Ty} {Γ : TEnv}
    {b : Base} {r : Refinement} (h : t.hyp? = some (b, r)) :
    ModelsEnv κ γ ((x, t) :: Γ) ↔
      (REnv.HasBase γ x b ∧ Refinement.interp κ r (γ.push (γ.lookup x))) ∧ ModelsEnv κ γ Γ := by
  simp only [ModelsEnv, h]

theorem ModelsEnv.cons_none {κ : KEnv} {γ : REnv} {x : EVar} {t : Ty} {Γ : TEnv}
    (h : t.hyp? = none) (hd : t.dhyp? = none) :
    ModelsEnv κ γ ((x, t) :: Γ) ↔ ModelsEnv κ γ Γ := by
  simp only [ModelsEnv, h, hd, true_and]

/-- Unfolding `ModelsEnv` at a datatype binding. -/
theorem ModelsEnv.cons_data {κ : KEnv} {γ : REnv} {x : EVar} {t : Ty} {Γ : TEnv}
    {r : Refinement} (hd : t.dhyp? = some r) :
    ModelsEnv κ γ ((x, t) :: Γ) ↔
      Refinement.interp κ r (γ.push (γ.lookup x)) ∧ ModelsEnv κ γ Γ := by
  simp only [ModelsEnv, Ty.hyp?_of_dhyp? hd, hd]

/-- A model of an extended context is a model of the context. -/
theorem ModelsEnv.tail {κ : KEnv} {γ : REnv} {x : EVar} {t : Ty} {Γ : TEnv}
    (h : ModelsEnv κ γ ((x, t) :: Γ)) : ModelsEnv κ γ Γ := h.2

/-- `κ; Γ ⊢ c`: `c` (as a Lean predicate over `REnv`) holds in every model of
    Γ under κ whose measure interpretation respects the declared bounds.
    VCGen-produced constraints use this. -/
@[simp]
def Entail (de : DEnv) (κ : KEnv) (Γ : TEnv) (c : REnv → Prop) : Prop :=
  ∀ γ, de.BoundsHold γ.sorts.meas → ModelsEnv κ γ Γ → c γ

/-- Under `HasBase`, the raw stored `Val` *is* the injected base-`b` read:
    `γ.lookup x = Val.inj b (get b γ x)`. Bridges `ModelsEnv`'s `push (γ.lookup x)`
    to the `push (Val.inj b v)` form the `∀ v` consumers (`Entail.ext`, `implyBind`)
    expect. -/
theorem Val.eq_inj_proj {s : BSort} {v : Val} (h : Val.HasSort s v) :
    v = Val.inj s (Val.proj s v) := by
  cases s with
  | int  => obtain ⟨n, rfl⟩ := h; rfl
  | bool => obtain ⟨c, rfl⟩ := h; rfl

theorem REnv.lookup_eq_inj_get (b : Base) (γ : REnv) (x : EVar) (hb : γ.HasBase x b) :
    γ.lookup x = Val.inj (b.resolve γ.sorts) (REnv.get b γ x) :=
  Val.eq_inj_proj hb

/-- Updating slot `x` with its current value is the identity — provided the cell
    actually holds a base-`b` value (otherwise the read defaults and the write
    re-stamps the wrong constructor). -/
theorem REnv.update_self (b : Base) (γ : REnv) (x : EVar) (hb : γ.HasBase x b) :
    REnv.update b γ x (REnv.get b γ x) = γ := by
  have h := REnv.lookup_eq_inj_get b γ x hb
  apply REnv.ext
  · funext y
    by_cases hxy : x = y
    · subst hxy
      simp only [beq_self_eq_true, ite_true]
      exact h.symm
    · simp [hxy]
  · rfl
  · rfl

/-- ENT-EMP: `∀ γ, c γ ⟹ κ; ∅ ⊢ c`. -/
@[simp]
theorem Entail.emp {de : DEnv} {κ : KEnv} {c : REnv → Prop} (h : ∀ γ, c γ) :
    Entail de κ [] c := by
  intro γ _ _; exact h γ

/-- ENT-EXT (predicate form): `κ; Γ ⊢ ∀v:b. r v → c[x↦v]  ⟹  κ; Γ, x:t ⊢ c`
    for a binding whose hypothesis is `r` at sort `b`.
    Instantiate with `REnv.get b γ x`, then close by `REnv.update_self`. -/
theorem Entail.ext {de : DEnv} {κ : KEnv} {Γ : TEnv} {x : EVar} {t : Ty} {b : Base}
    {r : Refinement} {c : REnv → Prop} (ht : t.hyp? = some (b, r))
    (h : Entail de κ Γ (fun γ => ∀ v : b.sem γ.sorts,
              Refinement.interp κ r (γ.push (Val.inj (b.resolve γ.sorts) v)) →
                c (REnv.update b γ x v))) :
    Entail de κ ((x, t) :: Γ) c := by
  intro γ hB hm
  obtain ⟨⟨hb, hr⟩, hΓ⟩ := (ModelsEnv.cons_some ht).mp hm
  rw [REnv.lookup_eq_inj_get b γ x hb] at hr
  have key := h γ hB hΓ (REnv.get b γ x) hr
  rw [REnv.update_self b γ x hb] at key
  exact key

/-- ENT-EXT for a binding with no hypothesis (function, polymorphic, or
    ⋆-kinded type-variable types). -/
theorem Entail.ext_none {de : DEnv} {κ : KEnv} {Γ : TEnv} {x : EVar} {t : Ty} {c : REnv → Prop}
    (ht : t.hyp? = none) (hd : t.dhyp? = none) (h : Entail de κ Γ c) :
    Entail de κ ((x, t) :: Γ) c :=
  fun γ hB hm => h γ hB ((ModelsEnv.cons_none ht hd).mp hm)

/-- ENT-EXT for a datatype binding: its refinement becomes a hypothesis about
    the slot itself (no quantifier — the slot holds a datatype value, which has
    no sort). -/
theorem Entail.ext_data {de : DEnv} {κ : KEnv} {Γ : TEnv} {x : EVar} {t : Ty} {r : Refinement}
    {c : REnv → Prop} (hd : t.dhyp? = some r)
    (h : Entail de κ Γ (fun γ => Refinement.interp κ r (γ.push (γ.lookup x)) → c γ)) :
    Entail de κ ((x, t) :: Γ) c := fun γ hB hm =>
  let ⟨hr, hΓ⟩ := (ModelsEnv.cons_data hd).mp hm
  h γ hB hΓ hr
