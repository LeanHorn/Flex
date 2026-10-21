import Flex.VCG.STLC.Syntax

/-! # Surface Syntax for STLC Programs

  Provides `<| ... |>` notation for writing locally-nameless `STLC.Exp`/`Ty`
  terms with ordinary named binders. Bound names are resolved to de Bruijn
  indices at macro-expansion time against an explicit name stack; there is no
  name stack threaded through the *elaborated* term, matching `Exp`/`Ty` being
  locally nameless.

  Two independent name stacks are tracked while expanding:
  * the `Exp`-level stack, pushed by `λ x, ...` and `let x = ... in ...`;
  * the refinement-level stack, pushed by `{ν : ...}` and `(x : s) -> t`,
    since ν, `Formula` quantifiers, and `Ty.arrow` binders share one index
    space (see `Syntax.lean`).

  A refinement type names its base explicitly, `int { v : ... }` or
  `bool { v : ... }`, since `Term` is `Base`-indexed (and `Ty.refine` records
  the base) — it cannot otherwise be inferred from the surface syntax. `Term.add` is
  int-only and `Term.not`/`Term.and` are bool-only; `Formula.leqI` is always
  over `Term .int` regardless of the enclosing refinement's base, matching
  `Syntax.lean`.

  Grammar (informal):
  ```
  term  ::= ident | numeral | true | false | (term)
           | term + term | ¬term | term ∧ term
  fmla  ::= ⊤ | ⊥ | term = term | term ≤ term
           | fmla ∧ fmla | fmla ∨ fmla | ¬fmla | fmla → fmla
           | ∃x:Int, fmla | ∃x:Bool, fmla | ∀x:Int, fmla | ∀x:Bool, fmla | (fmla)
  refine ::= fmla | ident term*          -- κ-application
  ty    ::= Int { ident : refine } | Bool { ident : refine }
           | ty -> ty | (ident : ty) -> ty | (ty)
  exp   ::= ident | numeral | (exp) | unreachable
           | λ ident, exp | let ident = exp in exp
           | exp exp | (exp : ty)
           | exp + exp | exp ≤ exp | exp ∧ exp | ¬exp
           | if exp then exp else exp
  ```

  Examples:
  ```lean
  <| let z = 99 in ((λ x, x) : (Int{v : κ v} -> Int{v : κ v})) z |>
  <ty| Int { v : 0 ≤ v } |>
  <ty| (x : Int { v : 0 ≤ v }) -> Bool { v : v = true } |>
  ```
-/

namespace STLC

declare_syntax_cat stlcTerm
declare_syntax_cat stlcFormula
declare_syntax_cat stlcRefine
declare_syntax_cat stlcTy
declare_syntax_cat stlcExp

-- Refinement-level terms (`Term .int` or `Term .bool`, base fixed by context)
syntax:max "(" stlcTerm ")"               : stlcTerm
syntax:max ident                          : stlcTerm
syntax:max num                            : stlcTerm
syntax:max "⌜" term "⌝"                   : stlcTerm  -- lift a Lean value as Term.const
syntax:65  stlcTerm:65 " + " stlcTerm:66  : stlcTerm
syntax:max "¬" stlcTerm:max               : stlcTerm
syntax:35  stlcTerm:36 " ∧ " stlcTerm:35  : stlcTerm

-- Formulas
syntax:max "⊤"                                              : stlcFormula
syntax:max "⊥"                                              : stlcFormula
syntax:max "(" stlcFormula ")"                              : stlcFormula
syntax stlcTerm " = " stlcTerm                               : stlcFormula
syntax stlcTerm " ≤ " stlcTerm                               : stlcFormula
syntax:35 stlcFormula:36 " ∧ " stlcFormula:35                : stlcFormula
syntax:30 stlcFormula:31 " ∨ " stlcFormula:30                : stlcFormula
syntax:max "¬" stlcFormula:max                               : stlcFormula
syntax:25 stlcFormula:26 " → " stlcFormula:25                : stlcFormula
syntax:max "∃" ident " : " ident ", " stlcFormula:max         : stlcFormula
syntax:max "∀" ident " : " ident ", " stlcFormula:max         : stlcFormula

-- Refinements: a kvar-free formula, or a κ-application `κ t₁ … tₙ`
syntax:max stlcFormula                     : stlcRefine
syntax:max ident (colGt stlcTerm:max)*      : stlcRefine

-- Types
syntax:max ident "{" ident " : " stlcRefine "}"        : stlcTy
syntax:max "(" stlcTy ")"                             : stlcTy
syntax:25  "(" ident " : " stlcTy ")" " -> " stlcTy:25 : stlcTy
syntax:25  stlcTy:26 " -> " stlcTy:25                  : stlcTy

-- Expressions
syntax:max "(" stlcExp ")"                            : stlcExp
syntax:max ident                                      : stlcExp
syntax:max num                                        : stlcExp
syntax:max "unreachable"                              : stlcExp
syntax:max "(" stlcExp " : " stlcTy ")"               : stlcExp
syntax:max "¬" stlcExp:max                            : stlcExp
syntax:70 stlcExp:70 stlcExp:71                       : stlcExp  -- application
syntax:60 stlcExp:60 " + " stlcExp:61                 : stlcExp
syntax:50 stlcExp:50 " ≤ " stlcExp:51                 : stlcExp
syntax:45 stlcExp:45 " ∧ " stlcExp:46                 : stlcExp
-- Binders/conditionals are below application precedence so they can only
-- appear as a whole expression (or inside parens), never as an application
-- operand; their bodies parse at the lowest precedence so they extend as far
-- right as possible (e.g. swallowing trailing applications).
syntax:10 "λ " ident ", " stlcExp                     : stlcExp
syntax:10 "let " ident " = " stlcExp " in " stlcExp   : stlcExp
syntax:10 "if " stlcExp " then " stlcExp " else " stlcExp : stlcExp

-- Top-level brackets
syntax (name := stlcProg)   "<|"  stlcExp "|>" : term
syntax (name := stlcTyProg) "<ty|" stlcTy "|>" : term

/-! ## Elaboration via MacroM helpers

  `ctx`/`rctx` are name stacks, innermost (most recently bound) name first,
  so that `List.findIdx?` directly yields the de Bruijn index.

  `eTerm`/`eFormula`/`eRefine` additionally take `base : TSyntax `term`, a
  spliceable `Base.int`/`Base.bool` term fixed by the enclosing
  `int {...}`/`bool {...}` refinement, since `Term` is `Base`-indexed and the
  surface syntax has no other way to pin the index.
  `Formula.leqI` is always over `Term .int` regardless of `base`. -/

class ToTerm (α : Type) (b : outParam Base) where
  toTerm : α → Term b

instance : ToTerm Int  .int  where toTerm n := .const .int  n
instance : ToTerm Bool .bool where toTerm b := .const .bool b

open Lean

private def resolveBase (b : TSyntax `ident) : MacroM Base :=
  match b.getId.toString with
  | "Int"  => pure .int
  | "Bool" => pure .bool
  | s      => Macro.throwError s!"expected 'Int' or 'Bool', got '{s}'"

/-- Splice a `Base` back into surface syntax. -/
private def baseStx : Base → MacroM (TSyntax `term)
  | .int  => `(Base.int)
  | .bool => `(Base.bool)

/-- The refinement-level name stack pairs each bound name with the `Base` it was
    bound at (its type), so a `BVar` occurrence can be elaborated to a
    fully-baseified `Term.bvar b k` — necessary in κ-application argument
    position, where the arg is packed into `Σ b : Base, Term b` and nothing else
    pins the base. A function-typed arrow binder has no refinement base
    (`none`); referencing it as a `Term` is ill-typed and elaborates to a hole. -/
abbrev RCtx := List (String × Option Base)

private def resolveIdent (rctx : RCtx) (name : String) : MacroM (TSyntax `term) :=
    match rctx.findIdx? (·.1 == name) with
    | some i =>
        match rctx[i]!.2 with
        | some b => do let bStx ← baseStx b; `(Term.bvar $bStx $(Lean.quote i))
        | none   => `(Term.bvar _ $(Lean.quote i))
    | none   =>
        match name with
        | "true"  => `(Term.const Base.bool true)
        | "false" => `(Term.const Base.bool false)
        | _       => `(Term.fvar _ $(Lean.mkIdent (Name.mkSimple name)))

/-- The `Base` an arrow binder of declared type `t` is bound at. A refinement
    type `b {…}` contributes its base; a function-typed binder has none. -/
partial def tyBase (t : TSyntax `stlcTy) : MacroM (Option Base) := do
  match t with
  | `(stlcTy| ($inner:stlcTy))                        => tyBase inner
  | `(stlcTy| $b:ident { $_:ident : $_:stlcRefine })  => some <$> resolveBase b
  | _                                                  => pure none

mutual

partial def eTerm (rctx : RCtx) (t : TSyntax `stlcTerm) :
    MacroM (TSyntax `term) := do
  match t with
  | `(stlcTerm| ($inner:stlcTerm))            => eTerm rctx inner
  | `(stlcTerm| $n:num)                       => `(Term.const .int $n)
  | `(stlcTerm| ⌜ $e:term ⌝)                 => `(ToTerm.toTerm $e)
  | `(stlcTerm| $a:stlcTerm + $b:stlcTerm)    => do
      let ta ← eTerm rctx a; let tb ← eTerm rctx b; `(Term.add $ta $tb)
  | `(stlcTerm| ¬ $a:stlcTerm)                 => do
      let ta ← eTerm rctx a; `(Term.not $ta)
  | `(stlcTerm| $a:stlcTerm ∧ $b:stlcTerm)     => do
      let ta ← eTerm rctx a; let tb ← eTerm rctx b; `(Term.and $ta $tb)
  | `(stlcTerm| $x:ident)                     =>
      resolveIdent rctx x.getId.toString
  | _ => Macro.throwUnsupported

partial def eFormula (rctx : RCtx) (f : TSyntax `stlcFormula) :
    MacroM (TSyntax `term) := do
  match f with
  | `(stlcFormula| ⊤)                                 => `(Formula.tt)
  | `(stlcFormula| ⊥)                                 => `(Formula.ff)
  | `(stlcFormula| ($inner:stlcFormula))              => eFormula rctx inner
  | `(stlcFormula| $a:stlcTerm = $b:stlcTerm)         => do
      let ta ← eTerm rctx a; let tb ← eTerm rctx b; `(Formula.eq _ $ta $tb)
  | `(stlcFormula| $a:stlcTerm ≤ $b:stlcTerm)         => do
      let ta ← eTerm rctx a
      let tb ← eTerm rctx b
      `(Formula.leqI $ta $tb)
  | `(stlcFormula| $a:stlcFormula ∧ $b:stlcFormula)   => do
      let ta ← eFormula rctx a; let tb ← eFormula rctx b; `(Formula.and $ta $tb)
  | `(stlcFormula| $a:stlcFormula ∨ $b:stlcFormula)   => do
      let ta ← eFormula rctx a; let tb ← eFormula rctx b; `(Formula.or $ta $tb)
  | `(stlcFormula| ¬ $a:stlcFormula)                  => do
      let ta ← eFormula rctx a; `(Formula.not $ta)
  | `(stlcFormula| $a:stlcFormula → $b:stlcFormula)   => do
      let ta ← eFormula rctx a; let tb ← eFormula rctx b; `(Formula.imp $ta $tb)
  | `(stlcFormula| ∃ $x:ident : $b:ident, $body:stlcFormula) => do
      let base ← resolveBase b
      let tb ← eFormula ((x.getId.toString, some base) :: rctx) body
      let bExpr ← baseStx base; `(Formula.ex $bExpr $tb)
  | `(stlcFormula| ∀ $x:ident : $b:ident, $body:stlcFormula) => do
      let base ← resolveBase b
      let tb ← eFormula ((x.getId.toString, some base) :: rctx) body
      let bExpr ← baseStx base; `(Formula.all $bExpr $tb)
  | _ => Macro.throwUnsupported

partial def eRefine (rctx : RCtx)  (r : TSyntax `stlcRefine) :
    MacroM (TSyntax `term) := do
  match r with
  | `(stlcRefine| $k:ident $args:stlcTerm*) => do
      let targs ← args.toList.mapM (fun a => do
        let ta ← eTerm rctx a
        `(term| (⟨_, $ta⟩ : Σ b : Base, Term b)))
      let targs := targs.toArray
      let lst ← `(term| [$[$targs],*])
      `(Refinement.kapp $(Lean.quote k.getId.toString) $lst)
  | `(stlcRefine| $f:stlcFormula) => do
      let tf ← eFormula rctx f; `(Refinement.fmla $tf)
  | _ => Macro.throwUnsupported

partial def eTy (rctx : RCtx) (t : TSyntax `stlcTy) : MacroM (TSyntax `term) := do
  match t with
  | `(stlcTy| ($inner:stlcTy))                       => eTy rctx inner
  | `(stlcTy| $b:ident { $v:ident : $r:stlcRefine })  => do
      let base ← resolveBase b
      let tr ← eRefine ((v.getId.toString, some base) :: rctx) r
      let bExpr ← baseStx base; `(Ty.refine $bExpr $tr)
  | `(stlcTy| ($x:ident : $s:stlcTy) -> $t:stlcTy)   => do
      let ts ← eTy rctx s
      let sBase ← tyBase s
      let tt ← eTy ((x.getId.toString, sBase) :: rctx) t
      `(Ty.arrow $ts $tt)
  | `(stlcTy| $s:stlcTy -> $t:stlcTy)                => do
      let ts ← eTy rctx s
      let sBase ← tyBase s
      let tt ← eTy (("", sBase) :: rctx) t
      `(Ty.arrow $ts $tt)
  | _ => Macro.throwUnsupported

partial def eExp (ctx : List String) (e : TSyntax `stlcExp) : MacroM (TSyntax `term) := do
  match e with
  | `(stlcExp| ($inner:stlcExp))               => eExp ctx inner
  | `(stlcExp| $n:num)                         => `(Exp.iconst $n)
  | `(stlcExp| unreachable)                    => `(Exp.unreach)
  | `(stlcExp| $x:ident)                       =>
      let name := x.getId.toString
      match ctx.findIdx? (· == name) with
      | some i => `(Exp.bvar $(Lean.quote i))
      | none   => `(Exp.fvar $(Lean.quote name))
  | `(stlcExp| λ $x:ident, $body:stlcExp)      => do
      let b ← eExp (x.getId.toString :: ctx) body
      `(Exp.lam $b)
  | `(stlcExp| let $x:ident = $e1:stlcExp in $e2:stlcExp) => do
      let t1 ← eExp ctx e1
      let t2 ← eExp (x.getId.toString :: ctx) e2
      `(Exp.letin $t1 $t2)
  | `(stlcExp| ($e1:stlcExp : $ty:stlcTy))     => do
      let te ← eExp ctx e1
      let tt ← eTy [] ty
      `(Exp.ann $te $tt)
  | `(stlcExp| if $c:stlcExp then $t:stlcExp else $f:stlcExp) => do
      let tc ← eExp ctx c; let tt ← eExp ctx t; let tf ← eExp ctx f
      `(Exp.ite $tc $tt $tf)
  | `(stlcExp| ¬ $a:stlcExp)                   => do
      let ta ← eExp ctx a; `(Exp.not $ta)
  | `(stlcExp| $a:stlcExp + $b:stlcExp)        => do
      let ta ← eExp ctx a; let tb ← eExp ctx b; `(Exp.add $ta $tb)
  | `(stlcExp| $a:stlcExp ≤ $b:stlcExp)        => do
      let ta ← eExp ctx a; let tb ← eExp ctx b; `(Exp.leq $ta $tb)
  | `(stlcExp| $a:stlcExp ∧ $b:stlcExp)        => do
      let ta ← eExp ctx a; let tb ← eExp ctx b; `(Exp.and $ta $tb)
  | `(stlcExp| $f:stlcExp $a:stlcExp)          => do
      let tf ← eExp ctx f; let ta ← eExp ctx a; `(Exp.app $tf $ta)
  | _ => Macro.throwUnsupported

end

macro_rules
  | `(<| $e |>) => eExp [] e

macro_rules
  | `(<ty| $t |>) => eTy [] t

end STLC
