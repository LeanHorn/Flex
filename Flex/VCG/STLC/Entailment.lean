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

/-- A model for Γ under κ-assignment: every binding with a refined hypothesis
    stores a value of the binding's sort (`HasBase`) satisfying it. The
    `HasBase` conjunct is what lets `Entail.ext` round-trip a refined slot
    through `b.interp`. -/
def ModelsEnv (κ : KEnv) : REnv → TEnv → Prop
  | _, []           => True
  | γ, (x, t) :: Γ  =>
      (match t.hyp? with
       | some (b, r) => REnv.HasBase γ x b ∧ Refinement.interp κ r (γ.push (γ.lookup x))
       | none        => True)
      ∧ ModelsEnv κ γ Γ

@[simp] theorem ModelsEnv.nil (κ : KEnv) (γ : REnv) : ModelsEnv κ γ [] := trivial

/-- Unfolding `ModelsEnv` at a binding whose hypothesis is known. -/
theorem ModelsEnv.cons_some {κ : KEnv} {γ : REnv} {x : EVar} {t : Ty} {Γ : TEnv}
    {b : Base} {r : Refinement} (h : t.hyp? = some (b, r)) :
    ModelsEnv κ γ ((x, t) :: Γ) ↔
      (REnv.HasBase γ x b ∧ Refinement.interp κ r (γ.push (γ.lookup x))) ∧ ModelsEnv κ γ Γ := by
  simp only [ModelsEnv, h]

theorem ModelsEnv.cons_none {κ : KEnv} {γ : REnv} {x : EVar} {t : Ty} {Γ : TEnv}
    (h : t.hyp? = none) :
    ModelsEnv κ γ ((x, t) :: Γ) ↔ ModelsEnv κ γ Γ := by
  simp only [ModelsEnv, h, true_and]

/-- A model of an extended context is a model of the context. -/
theorem ModelsEnv.tail {κ : KEnv} {γ : REnv} {x : EVar} {t : Ty} {Γ : TEnv}
    (h : ModelsEnv κ γ ((x, t) :: Γ)) : ModelsEnv κ γ Γ := h.2

/-- `κ; Γ ⊢ c`: `c` (as a Lean predicate over `REnv`) holds in every model of
    Γ under κ. VCGen-produced constraints use this. -/
@[simp]
def Entail (κ : KEnv) (Γ : TEnv) (c : REnv → Prop) : Prop :=
  ∀ γ, ModelsEnv κ γ Γ → c γ

/-- Under `HasBase`, the raw stored `Val` *is* the injected base-`b` read:
    `γ.lookup x = Val.inj b (get b γ x)`. Bridges `ModelsEnv`'s `push (γ.lookup x)`
    to the `push (Val.inj b v)` form the `∀ v` consumers (`Entail.ext`, `implyBind`)
    expect. -/
theorem REnv.lookup_eq_inj_get (b : Base) (γ : REnv) (x : EVar) (hb : γ.HasBase x b) :
    γ.lookup x = Val.inj b (REnv.get b γ x) := by
  cases b with
  | int  => obtain ⟨n, hn⟩ := hb; simp [REnv.lookup, REnv.get, hn]
  | bool => obtain ⟨c, hc⟩ := hb; simp [REnv.lookup, REnv.get, hc]
  | tbvar _ | tfvar _ =>
    rcases hb with ⟨n, hn⟩ | ⟨c, hc⟩
    · simp [REnv.lookup, REnv.get, hn]
    · simp [REnv.lookup, REnv.get, hc]

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

/-- ENT-EMP: `∀ γ, c γ ⟹ κ; ∅ ⊢ c`. -/
@[simp]
theorem Entail.emp {κ : KEnv} {c : REnv → Prop} (h : ∀ γ, c γ) :
    Entail κ [] c := by
  intro γ _; exact h γ

/-- ENT-EXT (predicate form): `κ; Γ ⊢ ∀v:b. r v → c[x↦v]  ⟹  κ; Γ, x:t ⊢ c`
    for a binding whose hypothesis is `r` at sort `b`.
    Instantiate with `REnv.get b γ x`, then close by `REnv.update_self`. -/
theorem Entail.ext {κ : KEnv} {Γ : TEnv} {x : EVar} {t : Ty} {b : Base} {r : Refinement}
    {c : REnv → Prop} (ht : t.hyp? = some (b, r))
    (h : Entail κ Γ (fun γ => ∀ v : b.interp,
              Refinement.interp κ r (γ.push (Val.inj b v)) → c (REnv.update b γ x v))) :
    Entail κ ((x, t) :: Γ) c := by
  intro γ hm
  obtain ⟨⟨hb, hr⟩, hΓ⟩ := (ModelsEnv.cons_some ht).mp hm
  rw [REnv.lookup_eq_inj_get b γ x hb] at hr
  have key := h γ hΓ (REnv.get b γ x) hr
  rw [REnv.update_self b γ x hb] at key
  exact key

/-- ENT-EXT for a binding with no hypothesis (function, polymorphic, or
    ⋆-kinded type-variable types). -/
theorem Entail.ext_none {κ : KEnv} {Γ : TEnv} {x : EVar} {t : Ty} {c : REnv → Prop}
    (ht : t.hyp? = none) (h : Entail κ Γ c) : Entail κ ((x, t) :: Γ) c :=
  fun γ hm => h γ ((ModelsEnv.cons_none ht).mp hm)
