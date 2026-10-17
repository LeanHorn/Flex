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
  | none        =>
    -- a datatype binding has no sort to quantify over: its refinement is a
    -- hypothesis about the (top-level universally quantified) slot `x`
    match t.dhyp? with
    | some r => .imp (r.openBVar 0 x) c
    | none   => c

/-- Conjoin the constraints produced for every element of a list (failing if
    any element fails). -/
def Cstr.conjAll {α : Type} (f : α → Option Cstr) : List α → Option Cstr
  | []      => some Cstr.triv
  | a :: as =>
      match f a, Cstr.conjAll f as with
      | some c, some cs => some (.conj c cs)
      | _, _ => none

theorem Cstr.conjAll_some {α : Type} {f : α → Option Cstr} :
    ∀ {l : List α} {c : Cstr}, Cstr.conjAll f l = some c →
      ∀ a ∈ l, ∃ ca, f a = some ca ∧ ∀ κ γ, c.interp κ γ → ca.interp κ γ
  | [], _, _, a, ha => by simp at ha
  | b :: bs, c, h, a, ha => by
    simp only [Cstr.conjAll] at h
    cases hb : f b with
    | none => simp [hb] at h
    | some cb =>
      cases hbs : Cstr.conjAll f bs with
      | none => simp [hb, hbs] at h
      | some cs =>
        simp only [hb, hbs, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨cb, hb, fun κ γ hc => hc.1⟩
        · obtain ⟨ca, hfa, himp⟩ := Cstr.conjAll_some hbs a ha
          exact ⟨ca, hfa, fun κ γ hc => himp κ γ hc.2⟩

end STLC

/-! ## Algorithmic subtyping / bidirectional checking -/

/-- Algorithmic subtyping. Returns `none` on shape mismatch. Termination
    by `Ty.skel` (preserved under `openVar`). Takes `Γ` so the fresh name
    for the arrow / base cases is picked away from the context domain. -/
def sub (de : DEnv) (Γ : TEnv) : Ty → Ty → Option Cstr
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
      match sub de Γ s₂ s₁, sub de ((x, s₂) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) with
      | some c₁, some c₂ =>
          some (.conj c₁ (implyBindCstr x s₂ c₂))
      | _, _ => none
  | .forall k₁ t₁, .forall k₂ t₂ =>
      if k₁ = k₂ then
        let a := TVar.fresh (TEnv.ftv Γ ++ t₁.ftv ++ t₂.ftv) k₁
        sub de Γ (t₁.openTv 0 a) (t₂.openTv 0 a)
      else none
  | .prod s₁ t₁, .prod s₂ t₂ =>
      let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ
                            ++ s₁.fv ++ s₂.fv ++ t₁.fv ++ t₂.fv)
      match sub de Γ s₁ s₂, sub de ((x, s₁) :: Γ) (t₁.openVar 0 x) (t₂.openVar 0 x) with
      | some c₁, some c₂ => some (.conj c₁ (implyBindCstr x s₁ c₂))
      | _, _ => none
  | .data C₁ n₁ a₁ r₁, .data C₂ n₂ a₂ r₂ =>
      -- type arguments related according to the declared variances
      if h : C₁ = C₂ ∧ n₁ = n₂ then
        let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ r₁.fv ++ r₂.fv)
        (Cstr.conjAll (fun i =>
          match de.var C₁ i.val with
          | .co     => sub de Γ (a₁ i) (a₂ (Fin.cast h.2 i))
          | .contra => sub de Γ (a₂ (Fin.cast h.2 i)) (a₁ i)
          | .inv    =>
            match sub de Γ (a₁ i) (a₂ (Fin.cast h.2 i)), sub de Γ (a₂ (Fin.cast h.2 i)) (a₁ i) with
            | some c, some c' => some (.conj c c')
            | _, _ => none) (List.finRange n₁)).map fun c =>
          .conj c (implyBindCstr x (.data C₁ n₁ a₁ r₁) (.head (r₂.openBVar 0 x)))
      else none
  | _, _ => none
termination_by s t => s.skel + t.skel
decreasing_by all_goals
  first
    | (simp_wf; simp only [Ty.skel, Ty.skel_openVar, Ty.skel_openTv]; omega)
    | (simp only [Ty.skel, Ty.skel_openVar, Ty.skel_openTv]; omega)
    | omega
    | (have := Ty.skel_data_lt C₁ n₁ a₁ r₁ i; have := Ty.skel_data_lt C₂ n₂ a₂ r₂ (Fin.cast h.2 i); omega)

mutual
  def synth (de : DEnv) (Γ : TEnv) : Exp → Option (Cstr × Ty)
    | .fvar x    => Γ.lookup x |>.map (fun t => (Cstr.triv, self x t))
    | .iconst n  => some (Cstr.triv, prim n)
    | .bconst b  => some (Cstr.triv, primBool b)
    | .ann e t =>
        match check de Γ e t with
        | some c => some (c, t)
        | none   => none
    | .app e₁ (.fvar y) =>
        match synth de Γ e₁ with
        | some (c, .arrow s t) =>
            -- Hygiene: `y` must not capture into `t` when we open `t.openVar 0 y`.
            if y ∈ t.fv then none
            else
              match check de Γ (.fvar y) s with
              | some c' => some (Cstr.conj c c', t.openVar 0 y)
              | none    => none
        | _ => none
    | .leq (.fvar x) (.fvar y) =>
        match Γ.lookup x, Γ.lookup y with
        | some (.refine b _), some (.refine b' _) =>
            if b = b' ∧ b.fvOK = true then some (Cstr.triv, leqTy b x y) else none
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
        match synth de Γ e with
        | some (c, .forall k t) =>
            if Kind.le s.kindOf k ∧ (Ty.forall k t).wfB [] [] = true ∧ s.wfB [] [] = true ∧
                (Ty.instTy 0 s t).wfB [] [] = true then
              some (c, Ty.instTy 0 s t)
            else none
        | _ => none
    | .ctor C j τs e =>
        match de.payload? C j with
        | some P =>
            if de.instOK C τs then
              match check de Γ e (Ty.instTys τs P) with
              | some c => some (c, Ty.dataL C τs (de.ctorRefine C j e))
              | none   => none
            else none
        | none => none
    | _ => none
  termination_by e => 2 * e.skel
  decreasing_by all_goals
    (first | (simp only [Exp.skel]; omega) | omega)


  def check (de : DEnv) (Γ : TEnv) : Exp → Ty → Option Cstr
    | .unreach, _ => some .ff
    | .lam e, .arrow s₁ s₂ =>
        let x := EVar.fresh (TEnv.dom Γ ++ e.fv ++ s₁.fv ++ s₂.fv ++ TEnv.tyFv Γ)
        match check de ((x, s₁) :: Γ) (e.openVar 0 x) (s₂.openVar 0 x) with
        | some c => some (implyBindCstr x s₁ c)
        | none   => none
    | .fix e, .arrow s t =>
        -- Chk-Rec: check the body assuming `f : s → t` (assume–guarantee). The
        -- binding for `f` has arrow or ∀ type, so it contributes no hypothesis.
        -- Polymorphic recursion: if the body instantiates `f` at a type, `f` is
        -- generalized over the annotation's type variables that `Γ` does not mention.
        let f := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s.fv ++ t.fv)
        let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ e.fv ++ s.fv ++ t.fv ++ [f])
        let as := if (e.openVar 1 f).tappsVar f then TEnv.genVars Γ (.arrow s t) else []
        match check de ((x, s) :: (f, Ty.gen as (.arrow s t)) :: Γ)
                ((e.openVar 1 f).openVar 0 x) (t.openVar 0 x) with
        | some c => some (implyBindCstr x s c)
        | none   => none
    | .tabs k e, .forall k' t =>
        if k = k' then
          let a := TVar.fresh (TEnv.ftv Γ ++ e.ftv ++ t.ftv) k
          check de Γ (e.openTv 0 a) (t.openTv 0 a)
        else none
    | .pair (.fvar x) e₂, .prod s t =>
        if x ∈ t.fv then none
        else
          match check de Γ (.fvar x) s, check de Γ e₂ (t.openVar 0 x) with
          | some c₁, some c₂ => some (Cstr.conj c₁ c₂)
          | _, _ => none
    | .split e body, t' =>
        match synth de Γ e with
        | some (c, .prod s t) =>
            let x := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t.fv ++ t'.fv)
            let y := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ body.fv ++ s.fv ++ t.fv ++ t'.fv ++ [x])
            match check de ((y, t.openVar 0 x) :: (x, s) :: Γ)
                    ((body.openVar 1 x).openVar 0 y) t' with
            | some c' => some (Cstr.conj c (implyBindCstr x s (implyBindCstr y (t.openVar 0 x) c')))
            | none    => none
        | _ => none
    | .case e m alts, t =>
        match synth de Γ e with
        | some (c, .data C _ args _) =>
            if de.nCtors C = some m ∧ de.instOK C (List.ofFn args) = true then
              match Cstr.conjAll (fun (j : Fin m) =>
                  match de.payload? C j.val with
                  | some P =>
                      let tz := de.altTy C j.val e.var? (Ty.instTys (List.ofFn args) P)
                      let z := EVar.fresh (TEnv.dom Γ ++ TEnv.tyFv Γ ++ (alts j).fv ++ t.fv ++ tz.fv)
                      match check de ((z, tz) :: Γ) ((alts j).openVar 0 z) t with
                      | some cj => some (implyBindCstr z tz cj)
                      | none    => none
                  | none => none) (List.finRange m) with
              | some cs => some (Cstr.conj c cs)
              | none    => none
            else none
        | _ => none
    | .letin e₁ e₂, t =>
        match synth de Γ e₁ with
        | some (c₁, s) =>
            let x := EVar.fresh (TEnv.dom Γ ++ e₂.fv ++ s.fv ++ t.fv ++ TEnv.tyFv Γ)
            match check de ((x, s) :: Γ) (e₂.openVar 0 x) t with
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
                  match check de ((y, r_true) :: Γ) e₁ t,
                        check de ((y, r_false) :: Γ) e₂ t with
                  | some c₁, some c₂ =>
                      some (Cstr.conj (implyBindCstr y r_true  c₁)
                                      (implyBindCstr y r_false c₂))
                  | _, _ => none
              | _ => none
        | _ => none
    | e, t =>
        -- Catch-all (Chk-Syn): synthesize, then subtype.
        match synth de Γ e with
        | some (c, s) =>
            match sub de Γ s t with
            | some c' => some (Cstr.conj c c')
            | none    => none
        | none => none
  termination_by e _ => 2 * e.skel + 1
  decreasing_by all_goals
    (first
      | (simp only [Exp.skel, Exp.skel_openVar, Exp.skel_openTv]; omega)
      | omega
      | (have := Exp.skel_case_lt e m alts j
         simp only [Exp.skel_openVar]; omega))
end

/-- Top-level: produce a closed Lean `Prop` (parameterized by a κ-assignment)
    to hand to `solve_fixpoint`. The user writes `∃ κ, topVC κ [] e t`. -/
@[simp]
def topVC (κ : KEnv) (Γ : TEnv) (e : Exp) (t : Ty) (de : DEnv := []) : Prop :=
  match check de Γ e t with
  | some c => ∀ γ : REnv, c.interp κ γ
  | none   => False
