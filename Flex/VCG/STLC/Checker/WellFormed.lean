import Flex.VCG.STLC.Checker.Operations

open STLC

/-! # Well-formedness checks

  Bound variables used at their binders' sorts (`WFBVars`, `Ty.wfB`), datatype
  instantiation (`instOK`), declared variances (`varOK`), and well-formed
  declarations and measures (`DEnv.wfB`). -/

namespace STLC

/-- Every field a body reads is one of the `n` fields. -/
def MBody.idxOK (n : Nat) : MBody → Bool
  | .const _  => true
  | .field i  => decide (i < n)
  | .meas _ i => decide (i < n)
  | .add a b  => a.idxOK n && b.idxOK n
  | .iteLe a b t e => a.idxOK n && b.idxOK n && t.idxOK n && e.idxOK n
  | .iteB i t e => decide (i < n) && t.idxOK n && e.idxOK n

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
  | _, .ibvar i   => decide (i < ctx.length)
  | _, .bbvar i   => decide (i < ctx.length)
  | _, .not t     => Term.wfB kctx ctx t
  | _, .and t₁ t₂ => Term.wfB kctx ctx t₁ && Term.wfB kctx ctx t₂
  | _, .leqI t₁ t₂ => Term.wfB kctx ctx t₁ && Term.wfB kctx ctx t₂
  | _, .ite _ c t e => Term.wfB kctx ctx c && Term.wfB kctx ctx t && Term.wfB kctx ctx e

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

/-- A body reads an `Int` field only where one is declared `Int{…}`, and
    branches on a field only where it is declared `Bool{…}`. (Soundness does not
    depend on this — a mismatched field reads as `0`/`false` — but such a
    measure is surely a mistake.) -/
def MBody.fieldsOK (ts : List Ty) : MBody → Bool
  | .const _  => true
  | .field i  => match ts[i]? with
    | some (.refine .int _) => true
    | _ => false
  | .meas _ _ => true
  | .add a b  => a.fieldsOK ts && b.fieldsOK ts
  | .iteLe a b t e => a.fieldsOK ts && b.fieldsOK ts && t.fieldsOK ts && e.fieldsOK ts
  | .iteB i t e => (match ts[i]? with
    | some (.refine .bool _) => true
    | _ => false) && t.fieldsOK ts && e.fieldsOK ts

/-- Well-formed measures: distinct names, and every body reads only fields of
    its constructor, each at its declared base. -/
def DataDecl.measOK (d : DataDecl) : Bool :=
  decide (d.measures.map Prod.fst).Nodup &&
  d.measures.all fun mb => (mb.2.zip d.ctorFields).all fun bc =>
    bc.1.idxOK bc.2.2.length && bc.1.fieldsOK bc.2.2

/-- Well-formed declarations: payloads have no free term or type variables, and
    respect the declared variances; measures are well-formed. -/
def DEnv.wfB (de : DEnv) : Bool :=
  (de.all fun d => d.2.ctors.all fun c =>
    c.2.fv.isEmpty && c.2.ftv.isEmpty && Ty.varOK de d.2.variances 0 .pos c.2) &&
  de.all fun d => d.2.measOK

end STLC
