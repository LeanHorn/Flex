import Flex.VCG.STLC.Checker.WellFormed

open STLC

/-! # Deciding the bound-variable well-formedness conditions

  `Ty.WFBVars`, `Exp.WFBVars` and `TEnv.WFBVars` — hypotheses of the headline
  theorems and side conditions of the declarative rules — are stated as
  propositions. Here each gets a boolean checker that is *equivalent* to it
  (`…bvOK_iff`), and hence a `Decidable` instance: for any concrete type,
  program or context, the condition holds iff `decide` proves it. (`Ty.wfB` also
  implies `Ty.WFBVars`, but it is stricter — it demands every type variable be
  bound — so it does not decide it.) -/

namespace STLC

/-! ## The checkers

  `ctx` lists the sorts of the enclosing binders, as in `Ty.WFBVarCtx`; `d`
  counts the formula quantifiers passed on the way down, which bind the
  innermost `d` indices. -/

def Term.bvOK (ctx : List (Option Base)) (d : Nat) : {b' : Base} → Term b' → Bool
  | _, .const _ _  => true
  | _, .bvar b j   => decide (j < d) || decide (ctx[j - d]? = some (some b))
  | _, .fvar _ _   => true
  | _, .add t₁ t₂  => t₁.bvOK ctx d && t₂.bvOK ctx d
  | _, .mbvar _ _  => true
  | _, .mfvar _ _  => true
  | _, .ibvar _    => true
  | _, .bbvar _    => true
  | _, .not t      => t.bvOK ctx d
  | _, .and t₁ t₂  => t₁.bvOK ctx d && t₂.bvOK ctx d
  | _, .leqI t₁ t₂ => t₁.bvOK ctx d && t₂.bvOK ctx d
  | _, .ite _ c t e => c.bvOK ctx d && t.bvOK ctx d && e.bvOK ctx d

def Formula.bvOK (ctx : List (Option Base)) : Nat → Formula → Bool
  | _, .tt | _, .ff => true
  | d, .eq _ t₁ t₂ | d, .leq _ t₁ t₂ => t₁.bvOK ctx d && t₂.bvOK ctx d
  | d, .and φ₁ φ₂ | d, .or φ₁ φ₂ | d, .imp φ₁ φ₂ => φ₁.bvOK ctx d && φ₂.bvOK ctx d
  | d, .not φ => φ.bvOK ctx d
  | d, .ex _ φ | d, .all _ φ => φ.bvOK ctx (d + 1)

def Refinement.bvOK (ctx : List (Option Base)) : Refinement → Bool
  | .fmla φ      => φ.bvOK ctx 0
  | .kapp _ args => args.all fun a => a.2.bvOK ctx 0
  | .conj r₁ r₂  => r₁.bvOK ctx && r₂.bvOK ctx

def Ty.bvOK : List (Option Base) → Ty → Bool
  | ctx, .refine br r => r.bvOK (some br :: ctx)
  | ctx, .arrow s t   => s.bvOK ctx && t.bvOK (s.optBase :: ctx)
  | ctx, .forall _ t  => t.bvOK (ctx.map (Option.map Base.shiftT))
  | ctx, .prod s t    => s.bvOK ctx && t.bvOK (s.optBase :: ctx)
  | ctx, .data _ n args r =>
      r.bvOK (none :: ctx) && (List.finRange n).all fun i => (args i).bvOK ctx

def Exp.bvOK : Exp → Bool
  | .bvar _ | .fvar _ | .iconst _ | .bconst _ | .unreach => true
  | .lam e | .not e | .fix e | .tabs _ e | .tapp e _ | .ctor _ _ _ e => e.bvOK
  | .letin e₁ e₂ | .app e₁ e₂ | .and e₁ e₂ | .leq e₁ e₂ | .add e₁ e₂
  | .pair e₁ e₂ | .split e₁ e₂ => e₁.bvOK && e₂.bvOK
  | .ann e t      => Ty.bvOK [] t && e.bvOK
  | .ite e₀ e₁ e₂ => e₀.bvOK && e₁.bvOK && e₂.bvOK
  | .case e n alts => e.bvOK && (List.finRange n).all fun j => (alts j).bvOK

/-! ## They decide the conditions -/

theorem Term.bvOK_iff {ctx : List (Option Base)} {d : Nat} {b' : Base} (t : Term b') :
    t.bvOK ctx d = true ↔ ∀ b k, Term.hasBVar b (k + d) t → ctx[k]? = some (some b) := by
  induction t with
  | bvar b j =>
    simp only [Term.bvOK, Term.hasBVar, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h) b k ⟨rfl, hk⟩
      · omega
      · subst hk; simpa using h
    · intro h
      by_cases hj : j < d
      · exact .inl hj
      · exact .inr (h b (j - d) ⟨rfl, by omega⟩)
  | add _ _ ih₁ ih₂ | and _ _ ih₁ ih₂ | leqI _ _ ih₁ ih₂ =>
    simp only [Term.bvOK, Term.hasBVar, Bool.and_eq_true, ih₁, ih₂]
    exact ⟨fun ⟨h₁, h₂⟩ b k h => h.elim (h₁ b k) (h₂ b k),
      fun h => ⟨fun b k h' => h b k (.inl h'), fun b k h' => h b k (.inr h')⟩⟩
  | ite _ _ _ _ ihc iht ihe =>
    simp only [Term.bvOK, Term.hasBVar, Bool.and_eq_true, ihc, iht, ihe]
    exact ⟨fun ⟨⟨hc, ht⟩, he⟩ b k h => h.elim (hc b k) (·.elim (ht b k) (he b k)),
      fun h => ⟨⟨fun b k h' => h b k (.inl h'), fun b k h' => h b k (.inr (.inl h'))⟩,
        fun b k h' => h b k (.inr (.inr h'))⟩⟩
  | not _ ih => simp only [Term.bvOK, Term.hasBVar, ih]
  | _ => simp [Term.bvOK, Term.hasBVar]

theorem Formula.bvOK_iff {ctx : List (Option Base)} (φ : Formula) : ∀ {d : Nat},
    φ.bvOK ctx d = true ↔ ∀ b k, Formula.hasBVar b (k + d) φ → ctx[k]? = some (some b) := by
  induction φ with
  | tt | ff => simp [Formula.bvOK, Formula.hasBVar]
  | eq _ t₁ t₂ | leq _ t₁ t₂ =>
    intro d
    simp only [Formula.bvOK, Formula.hasBVar, Bool.and_eq_true, Term.bvOK_iff]
    exact ⟨fun ⟨h₁, h₂⟩ b k h => h.elim (h₁ b k) (h₂ b k),
      fun h => ⟨fun b k h' => h b k (.inl h'), fun b k h' => h b k (.inr h')⟩⟩
  | and _ _ ih₁ ih₂ | or _ _ ih₁ ih₂ | imp _ _ ih₁ ih₂ =>
    intro d
    simp only [Formula.bvOK, Formula.hasBVar, Bool.and_eq_true, ih₁, ih₂]
    exact ⟨fun ⟨h₁, h₂⟩ b k h => h.elim (h₁ b k) (h₂ b k),
      fun h => ⟨fun b k h' => h b k (.inl h'), fun b k h' => h b k (.inr h')⟩⟩
  | not _ ih => intro d; simp only [Formula.bvOK, Formula.hasBVar, ih]
  | ex _ _ ih | all _ _ ih =>
    intro d
    simp only [Formula.bvOK, Formula.hasBVar, ih, Nat.add_assoc]

theorem Refinement.bvOK_iff {ctx : List (Option Base)} (r : Refinement) :
    r.bvOK ctx = true ↔ ∀ b k, Refinement.hasBVar b k r → ctx[k]? = some (some b) := by
  induction r with
  | fmla φ => simp only [Refinement.bvOK, Refinement.hasBVar, Formula.bvOK_iff, Nat.add_zero]
  | kapp _ args =>
    simp only [Refinement.bvOK, Refinement.hasBVar, List.all_eq_true, Term.bvOK_iff,
      Nat.add_zero]
    exact ⟨fun h b k ⟨a, ha, h'⟩ => h a ha b k h', fun h a ha b k h' => h b k ⟨a, ha, h'⟩⟩
  | conj _ _ ih₁ ih₂ =>
    simp only [Refinement.bvOK, Refinement.hasBVar, Bool.and_eq_true, ih₁, ih₂]
    exact ⟨fun ⟨h₁, h₂⟩ b k h => h.elim (h₁ b k) (h₂ b k),
      fun h => ⟨fun b k h' => h b k (.inl h'), fun b k h' => h b k (.inr h')⟩⟩

theorem Ty.bvOK_iff (t : Ty) : ∀ {ctx : List (Option Base)},
    t.bvOK ctx = true ↔ Ty.WFBVarCtx ctx t := by
  induction t with
  | refine _ r => intro ctx; simp only [Ty.bvOK, Ty.WFBVarCtx, Refinement.bvOK_iff]
  | arrow _ _ ih₁ ih₂ | prod _ _ ih₁ ih₂ =>
    intro ctx; simp only [Ty.bvOK, Ty.WFBVarCtx, Bool.and_eq_true, ih₁, ih₂]
  | «forall» _ _ ih => intro ctx; simp only [Ty.bvOK, Ty.WFBVarCtx, ih]
  | data _ n args r ih =>
    intro ctx
    simp only [Ty.bvOK, Ty.WFBVarCtx, Bool.and_eq_true, Refinement.bvOK_iff, List.all_eq_true,
      List.mem_finRange, true_implies, ih]

theorem Exp.bvOK_iff (e : Exp) : e.bvOK = true ↔ Exp.WFBVars e := by
  induction e with
  | ann _ t ih => simp only [Exp.bvOK, Exp.WFBVars, Bool.and_eq_true, Ty.bvOK_iff, ih]; rfl
  | case _ n alts ih ihs =>
    simp only [Exp.bvOK, Exp.WFBVars, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, ih, ihs]
  | _ => simp_all [Exp.bvOK, Exp.WFBVars, and_assoc]

theorem TEnv.WFBVars_iff (Γ : TEnv) : TEnv.WFBVars Γ ↔ (Γ.all fun p => Ty.bvOK [] p.2) = true := by
  simp only [TEnv.WFBVars, List.all_eq_true, Ty.bvOK_iff]
  exact ⟨fun h p hp => h p.1 p.2 hp, fun h x t hxt => h (x, t) hxt⟩

/-! ## Decidability

  With these instances, `decide` discharges the well-formedness hypotheses of a
  concrete program: `vcgen_safety (by decide) (by decide) (by decide) h`. -/

instance Ty.decWFBVarCtx (ctx : List (Option Base)) (t : Ty) : Decidable (Ty.WFBVarCtx ctx t) :=
  decidable_of_iff _ (Ty.bvOK_iff t)

instance Ty.decWFBVars (t : Ty) : Decidable (Ty.WFBVars t) :=
  Ty.decWFBVarCtx [] t

instance Exp.decWFBVars (e : Exp) : Decidable (Exp.WFBVars e) :=
  decidable_of_iff _ (Exp.bvOK_iff e)

instance TEnv.decWFBVars (Γ : TEnv) : Decidable (TEnv.WFBVars Γ) :=
  decidable_of_iff _ (TEnv.WFBVars_iff Γ).symm

end STLC
