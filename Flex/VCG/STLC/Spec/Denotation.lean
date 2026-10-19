import Flex.VCG.STLC.Spec.Logic
import Flex.VCG.STLC.Spec.Semantics

open STLC

/-! # The meaning of types

  `TyDenote κ δ k t γ v`: the value `v` belongs to type `t` at step index `k`,
  with type variables interpreted by `δ` and the refinements' free variables by
  `γ`. This is the conclusion of every headline theorem. -/

namespace STLC


/-! ## Semantic types for type variables

  A type variable is interpreted by a `SemTy`: a step-indexed, downward-closed
  predicate on (locally closed, closed, type-erased) values. `Fits k` restricts the
  interpretations of a `B`-kinded variable to the values of one base sort —
  exactly the instances λ_RF allows (refined `Int`/`Bool`). -/

structure SemTy where
  rel  : Nat → Val → Prop
  mono : ∀ {j k : Nat} {v : Val}, j ≤ k → rel k v → rel j v
  wf   : ∀ {k : Nat} {v : Val}, rel k v → Val.lc v ∧ Val.closed v ∧ Val.Erased v
  /-- The base the values have, for an interpretation of a `B`-kinded variable
      (refinements at the variable's sort are read at this base). -/
  sort : BSort

/-- `R` is a legal interpretation of a type variable of kind `k`. -/
def SemTy.Fits (R : SemTy) : Kind → Prop
  | .B    => ∀ k v, R.rel k v → v.optBase = some R.sort.toBase
  | .star => True

/-- The interpretation used for unbound type variables (never consulted for
    well-scoped types): all locally closed, closed values. -/
def SemTy.top : SemTy :=
  ⟨fun _ v => Val.lc v ∧ Val.closed v ∧ Val.Erased v, fun _ h => h, fun h => h, .int⟩

/-- The integers, as a semantic type. Fits both kinds; the default
    interpretation of `B`-kinded type variables. -/
def SemTy.ints : SemTy :=
  ⟨fun _ v => ∃ n, v = .iconst n, fun _ h => h,
   fun h => by obtain ⟨n, rfl⟩ := h; exact ⟨trivial, rfl, trivial⟩, .int⟩

/-- A semantic type that agrees with `R` up to index `i` (and is empty above).
    Downward closed and well-formed by construction, so it can be built inside
    the definition of `TyDenote` without any proof obligations. -/
def SemTy.upto (i : Nat) (R : Fin (i+1) → Val → Prop) (s : BSort) : SemTy :=
  ⟨fun j w => (∃ j' : Fin (i+1), j ≤ j'.val ∧ R j' w) ∧ Val.lc w ∧ Val.closed w ∧ Val.Erased w,
   fun hjk ⟨⟨j', hj', hR⟩, hw⟩ => ⟨⟨j', Nat.le_trans hjk hj', hR⟩, hw⟩,
   fun h => h.2, s⟩

/-- Interpretation of type variables: a de Bruijn stack for the `tbvar`s
    (pushed when entering a `Ty.forall`) and a map for the `tfvar`s — together
    with the program's datatype declarations, which give datatypes their meaning. -/
structure TyEnvSem where
  bv : List SemTy := []
  fv : TVar → SemTy := fun _ => SemTy.top
  denv : DEnv := []

/-- The default interpretation: `B`-kinded variables as the integers, ⋆-kinded
    ones as all (closed) values. Satisfies `WK`. -/
def TyEnvSem.empty (de : DEnv := []) : TyEnvSem :=
  { bv := [], fv := fun a => match a.2 with | .B => SemTy.ints | .star => SemTy.top, denv := de }

/-- The bases the type variables stand for under `δ` — and the measures, as
    the declarations define them. -/
def TyEnvSem.sorts (δ : TyEnvSem) : SortEnv :=
  { bv := δ.bv.map SemTy.sort, fv := fun a => (δ.fv a).sort, meas := δ.denv.measEval }

@[simp] def TyEnvSem.push (δ : TyEnvSem) (R : SemTy) : TyEnvSem := { δ with bv := R :: δ.bv }

/-- The base a refined type's values have under `δ` (`int`, arbitrarily, for
    other types). -/
def Ty.semSort (δ : TyEnvSem) : Ty → BSort
  | .refine b _ => b.resolve δ.sorts
  | _           => .int

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
  type, so impredicative instantiation costs nothing here.

  A dependent pair holds pairs whose second component is in the second type
  with the first component bound. A datatype `C[τ̄]{r}` holds constructor values
  satisfying `r` (with ν bound to the value), whose payload is in the constructor's payload type, *one step later* (matching
  a datatype value costs a unit of fuel), with the type parameters interpreted
  by the arguments' denotations (which close over `γ`, so a type argument may
  mention earlier fields). A payload type has no free variables, so it is read
  under the empty environment. Unfolding one step per match is what makes
  recursive datatypes well-founded: the definition recurses on `(k, t.skel)`
  lexicographically. -/

def TyDenote : KEnv → TyEnvSem → Nat → Ty → REnv → Val → Prop
  | κ, δ, k, .refine b r, γ, v =>
      BaseDen δ k b v ∧ Refinement.interp κ r ((γ.withSorts δ.sorts).push v)
  | κ, δ, k, .arrow s t,  γ, v =>
      (∃ body, v = .clos body ∨ v = .fclos body) ∧
        Val.lc v ∧ Val.closed v ∧ Val.Erased v ∧
        ∀ j < k, ∀ va, TyDenote κ δ j s γ va →
          ∃ body o, Val.apply v va = some body ∧ Eval j body o ∧
            ∀ vr m, o = .val vr m → m ≤ j → TyDenote κ δ m t (γ.push va) vr
  | κ, δ, k, .forall kd t, γ, v =>
      ∀ R : SemTy, R.Fits kd → TyDenote κ (δ.push R) k t γ v
  | κ, δ, k, .prod s t, γ, v =>
      ∃ v₁ v₂, v = .pair v₁ v₂ ∧ TyDenote κ δ k s γ v₁ ∧ TyDenote κ δ k t (γ.push v₁) v₂
  | κ, δ, k, .data C _ args r, γ, v =>
      Val.lc v ∧ Val.closed v ∧ Val.Erased v ∧
      Refinement.interp κ r ((γ.withSorts δ.sorts).push v) ∧
      ∃ j w P, v = .ctor C j w ∧ δ.denv.payload? C j = some P ∧
        ∀ i < k, TyDenote κ
          { bv := List.ofFn (fun l => SemTy.upto i (fun j' w' => TyDenote κ δ j'.val (args l) γ w')
                    ((args l).semSort δ)),
            fv := fun _ => SemTy.top, denv := δ.denv } i P REnv.empty w
termination_by _ _ k t _ _ => (k, t.skel)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right' <;> omega)
    | (apply Prod.Lex.right; omega)
    | (apply Prod.Lex.left; have := j'.isLt; omega)

end STLC
