import Flex.VCG.STLC.Syntax
import Flex.VCG.STLC.Substitution
import Flex.VCG.STLC.Typing
import Flex.VCG.STLC.Notation

open STLC

/-! # VC Generation for STLC (LN + deep Formula + κ)

  Algorithmic bidirectional refinement type-checker that produces a *syntactic*
  constraint `Cstr` — a Constrained Horn Clause tree with constructors
-/

namespace STLC

def implyBindCstr (x : EVar) (t : Ty) (c : Cstr) : Cstr :=
  match t.hyp? with
  | some (b, r) => .all x b (.imp (r.openBVar 0 x) c)
  | none        => c

end STLC

/-! ## Algorithmic subtyping / bidirectional checking -/

/-- Algorithmic subtyping. Returns `none` on shape mismatch. Termination
    by `Ty.skel` (preserved under `openVar`). Takes `Γ` so the fresh name
    for the arrow / base cases is picked away from the context domain. -/
def sub (Γ : TEnv) : Ty → Ty → Option Cstr
  | .refine b₁ r₁, .refine b₂ r₂ =>
      if b₁ = b₂ then
        let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv)
        -- `∀x:b. r₁[x] ⇒ r₂[x]`; sorts without a model hypothesis (⋆-kinded
        -- type variables) bind nothing — see `implyBindCstr`.
        some (implyBindCstr x (.refine b₁ r₁) (.head (r₂.openBVar 0 x)))
      else none
  | .arrow s₁ t₁, .arrow s₂ t₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ
                            ++ s₁.fv ++ s₂.fv ++ t₁.fv ++ t₂.fv)
      match sub Γ s₂ s₁, sub ((x, s₂) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) with
      | some c₁, some c₂ =>
          some (.conj c₁ (implyBindCstr x s₂ c₂))
      | _, _ => none
  | .forall k₁ t₁, .forall k₂ t₂ =>
      if k₁ = k₂ then
        let a := TVar.fresh (t₁.ftv ++ t₂.ftv) k₁
        sub Γ (t₁.openTv 0 a) (t₂.openTv 0 a)
      else none
  | _, _ => none
termination_by s t => s.skel + t.skel
decreasing_by all_goals
  first
    | (simp_wf; simp only [Ty.skel, Ty.skel_openVar, Ty.skel_openTv]; omega)
    | (simp only [Ty.skel, Ty.skel_openVar, Ty.skel_openTv]; omega)
    | omega

mutual
  def synth (Γ : TEnv) : Exp → Option (Cstr × Ty)
    | .fvar x    => Γ.lookup x |>.map (fun t => (Cstr.triv, self x t))
    | .iconst n  => some (Cstr.triv, prim n)
    | .bconst b  => some (Cstr.triv, primBool b)
    | .ann e t =>
        match check Γ e t with
        | some c => some (c, t)
        | none   => none
    | .app e₁ (.fvar y) =>
        match synth Γ e₁ with
        | some (c, .arrow s t) =>
            -- Hygiene: `y` must not capture into `t` when we open `t.openVar 0 y`.
            if y ∈ t.fv then none
            else
              match check Γ (.fvar y) s with
              | some c' => some (Cstr.conj c c', t.openVar 0 y)
              | none    => none
        | _ => none
    | .leq (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some (Cstr.triv, <ty| Bool{ν : (ν = true → x ≤ y) ∧ (x ≤ y → ν = true)} |>)
        | _, _ => none
    | .add (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .int _), some (.refine .int _) =>
            some (Cstr.triv, <ty| Int{ν : ν = x + y}|>)
        | _, _ => none
    | .not (.fvar x) =>
        match Γ.lookup x with
        | some (.refine .bool _) => some (Cstr.triv, <ty| Bool{ν : ν = ¬x}|>)
        | _ => none
    | .and (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine .bool _), some (.refine .bool _) =>
            some (Cstr.triv, <ty| Bool{ν : ν = x ∧ y} |>)
        | _, _ => none
    | .tapp e s =>
        match synth Γ e with
        | some (c, .forall k t) =>
            if Kind.le s.kindOf k ∧ (Ty.forall k t).wfB [] [] = true ∧ s.wfB [] [] = true ∧
                (Ty.instTy 0 s t).wfB [] [] = true then
              some (c, Ty.instTy 0 s t)
            else none
        | _ => none
    | _ => none
  termination_by e => 2 * e.skel
  decreasing_by all_goals
    (first | (simp only [Exp.skel]; omega) | omega)


  def check (Γ : TEnv) : Exp → Ty → Option Cstr
    | .unreach, _ => some .ff
    | .lam e, .arrow s₁ s₂ =>
        let x := EVar.fresh (TEnv.dom Γ ++ e.fv ++ s₁.fv ++ s₂.fv ++ TEnv.tyFv Γ)
        match check ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) with
        | some c => some (implyBindCstr x s₁ c)
        | none   => none
    | .fix e, .arrow s t =>
        -- Chk-Rec: check the body assuming `f : s → t` (assume–guarantee). The
        -- binding for `f` has arrow type, so it contributes no hypothesis.
        let f := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s.fv ++ t.fv)
        let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s.fv ++ t.fv ++ [f])
        match check ((x, s) :: (f, .arrow s t) :: Γ)
                ((e.openVar 1 f).openVar 0 x) (t.openVar 0 x) with
        | some c => some (implyBindCstr x s c)
        | none   => none
    | .tabs k e, .forall k' t =>
        if k = k' then
          let a := TVar.fresh (TEnv.ftv Γ ++ e.ftv ++ t.ftv) k
          check Γ (e.openTv 0 a) (t.openTv 0 a)
        else none
    | .letin e₁ e₂, t =>
        match synth Γ e₁ with
        | some (c₁, s) =>
            let x := EVar.fresh (TEnv.dom Γ ++ e₂.fv ++ s.fv ++ t.fv ++ TEnv.tyFv Γ)
            match check ((x, s) :: Γ) (e₂.openVar 0 x) t with
            | some c₂ => some (Cstr.conj c₁ (implyBindCstr x s c₂))
            | none    => none
        | none => none
    | .ite e₀ e₁ e₂, t =>
        match e₀ with
        | .fvar x =>
              match Γ.lookup x with
              | some (.refine .bool _) =>
                  -- Fresh guard variable `y` (standard `if`-rule): keep `x : {ν|r}` in
                  -- scope and add the path condition `x = true/false` via a fresh
                  -- binding whose refinement mentions `x` free. This preserves `r`
                  -- in each branch without conjoining into the (atomic) refinement.
                  let y := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ
                                        ++ e₁.fv ++ e₂.fv ++ t.fv ++ [x])
                  let r_true  : Ty := <ty| Bool{ν : x = true}|>
                  let r_false : Ty := <ty| Bool{ν : x = false}|>
                  match check ((y, r_true) :: Γ) e₁ t,
                        check ((y, r_false) :: Γ) e₂ t with
                  | some c₁, some c₂ =>
                      some (Cstr.conj (implyBindCstr y r_true  c₁)
                                      (implyBindCstr y r_false c₂))
                  | _, _ => none
              | _ => none
        | _ => none
    | e, t =>
        -- Catch-all (Chk-Syn): synthesize, then subtype.
        match synth Γ e with
        | some (c, s) =>
            match sub Γ s t with
            | some c' => some (Cstr.conj c c')
            | none    => none
        | none => none
  termination_by e _ => 2 * e.skel + 1
  decreasing_by all_goals
    (first | (simp only [Exp.skel, Exp.skel_openVar, Exp.skel_openTv]; omega) | omega)
end

/-- Top-level: produce a closed Lean `Prop` (parameterized by a κ-assignment)
    to hand to `solve_fixpoint`. The user writes `∃ κ, topVC κ [] e t`. -/
@[simp]
def topVC (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) : Prop :=
  match check Γ e t with
  | some c => ∀ γ : REnv, c.interp κ γ
  | none   => False
