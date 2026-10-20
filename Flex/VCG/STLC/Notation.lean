import Flex.VCG.STLC.Spec.Syntax
import Lean.Elab.Command
import Std.Data.HashMap

/-! # Surface Syntax for STLC Programs

  `<| … |>` writes an `Exp`, `<ty| … |>` a `Ty`, and `stlc_data` declares a
  datatype (a `DataDecl`), all with ordinary named binders. Names are resolved
  to de Bruijn indices when the notation is elaborated, so the result is the
  same locally-nameless term one would write by hand.

  ## Scopes

  Three name stacks are tracked while elaborating:
  * **variables**: pushed by the expression binders (`λ`, `fix`, `let`, tuple
    patterns, `match` alternatives) and by the binders of types (`(x : s) -> t`,
    `(x : s) × t`, the ν of `b{ν : r}`) and formulas (`∃`, `∀`). They share one
    index space (see `Spec/Syntax.lean`), so a type inside an expression (an
    annotation, a type argument) may mention the program variables in scope;
  * **type variables**: pushed by `Λ` and `∀`, read as `Base.tbvar`;
  * **constructors**: global, registered by `stlc_data`. `C`, or `D.C` to
    pick the datatype `D`, names constructor `C`; a bound variable of the same
    name shadows it.

  Some binders are compiled away (the payload of a constructor, the
  intermediate pairs of a tuple pattern); they take indices like any other
  binder but have no name.

  ## Sorts

  `Term` is indexed by its sort, which the notation infers: literals, `+` and
  measures are `Int`, `¬`/`∧` are `Bool`, a variable has the sort it was bound
  at (`b{ν : …}`, an arrow binder of refined type, a `let` of a literal or a
  comparison). Comparisons and equalities take the sort of whichever side has
  one, so `x ≤ ν` in `α{ν : x ≤ ν}` compares at `α`. A variable whose sort is
  unknown (a `λ`-bound one, say) takes the sort its context expects, and `Int`
  if there is none; `(t : Bool)` forces it.

  ## Grammar (informal)
  ```
  term    ::= x | n | -n | true | false | ⌜lean⌝ | (term) | (term : sort)
            | m x                                  -- measure m of variable x
            | term + term | ¬term | term ∧ term
            | if term then term else term | if term ≤ term then term else term
  fmla    ::= ⊤ | ⊥ | (fmla) | term = term | term ≠ term
            | term ≤ term | term < term | term ≥ term | term > term
            | fmla ∧ fmla | fmla ∨ fmla | ¬fmla | fmla → fmla | fmla ↔ fmla
            | ∃ x : sort, fmla | ∀ x : sort, fmla
  refine  ::= fmla | κ term*                       -- κ-application (args atomic)
  sort    ::= Int | Bool | α
  kind    ::= ⋆ | B
  ty      ::= sort | sort{x : refine}              -- refined base or type variable
            | D | D[ty,*] | D{x : refine} | D[ty,*]{x : refine}   -- datatype
            | ty -> ty | (x : ty) -> ty | ty × ty | (x : ty) × ty
            | ∀ α, ty | ∀ α : kind, ty | (ty) | ⌜lean⌝
  pat     ::= x | _ | (pat, pat, …)                -- tuples nest to the right
  exp     ::= x | n | -n | true | false | () | ⌜lean⌝ | unreachable
            | (exp) | (exp : ty) | (exp, exp, …)
            | exp exp | exp[ty,*] | C[ty,*] exp*   -- application, instantiation, constructor
            | exp + exp | exp ≤ exp | exp ∧ exp | ¬exp
            | λ x y …, exp | Λ α, exp | Λ α : kind, exp | fix f x, exp
            | let pat = exp in exp | let x : ty = exp in exp
            | if exp then exp else exp
            | match exp with | C x₁ … xₙ => exp | …
  ```
  `fix f x, e` is `Exp.fix`: `f` is the function itself, `x` its parameter. A
  constructor is applied to its type arguments and then to one argument per
  field; its payload is built as the nested pairs `(f₀, (f₁, … ()))`. A `match`
  alternative binds the fields, and the alternatives may come in any order. A
  `match` inside an alternative extends as far as possible, so parenthesize
  it unless it is the last one. `Λ` and `∀` are keywords, so follow them with a
  space.

  `⌜…⌝` splices a Lean term: an `Exp`, a `Ty`, or (in a refinement) a value
  converted by `ToTerm`. A spliced `Exp` or `Ty` is inserted as is, without
  shifting its indices, so it should be closed.

  ## Datatypes
  ```lean
  stlc_data lenListDecl : list (+α : ⋆) where
    | Nil
    | Cons (h : α) (t : list[α])
    measure len
    | Nil => 0
    | Cons _ t => 1 + len t
  ```
  defines `lenListDecl : DataDecl` for the datatype `list` and registers its
  constructors. A parameter is `(α)`, `(α : kind)`, prefixed with `+` or `-`
  for a covariant or contravariant one (unannotated: invariant). Inside the
  fields, parameter `i` is `Base.tbvar i` and a field's type may mention the
  earlier fields. A measure body is built from literals, the `Int` fields,
  `m f` (measure `m` of field `f`), `+`, `max a b`, `if a ≤ b then t else e`
  and `if f then t else e` (on a `Bool` field) — the forms of `MBody`.

  ## Examples
  ```lean
  <| let z = 99 in ((λ x, x) : Int{v : κ v} -> Int{v : κ v}) z |>
  <ty| (x : Int{v : 0 ≤ v}) -> Bool{v : v = true} |>
  <ty| ∀ α : ⋆, (xs : list[α]) -> Int{v : v = len xs} |>
  <| Λ α : ⋆, fix go xs, match xs with
       | Nil => 0
       | Cons _ t => let r = go t in let one = 1 in one + r |>
  ```
-/

namespace STLC

/-- `case e of alts`, with the alternatives as a list: what `match` builds. -/
abbrev caseL (e : Exp) (alts : List Exp) : Exp := .case e alts.length alts.get

/-! ## The constructor registry -/

/-- What the notation needs to know about a constructor. -/
structure CtorInfo where
  dtype   : String
  idx     : Nat
  nfields : Nat
  nctors  : Nat
  deriving Inhabited, Repr

abbrev CtorTable := Std.HashMap String CtorInfo

open Lean in
initialize ctorExt : SimplePersistentEnvExtension (String × CtorInfo) CtorTable ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, v) => m.insert k v
    addImportedFn := fun as => as.foldl (fun m a => a.foldl (fun m (k, v) => m.insert k v) m) {}
  }

/-! ## Syntax -/

declare_syntax_cat stlcTerm
declare_syntax_cat stlcFormula
declare_syntax_cat stlcRefine
declare_syntax_cat stlcKind
declare_syntax_cat stlcTy
declare_syntax_cat stlcBinder
declare_syntax_cat stlcPat
declare_syntax_cat stlcAlt
declare_syntax_cat stlcExp

-- Refinement-level terms
syntax:max "(" stlcTerm ")"                     : stlcTerm
syntax:max "(" stlcTerm " : " ident ")"         : stlcTerm
syntax:max ident                                : stlcTerm
syntax:max num                                  : stlcTerm
syntax:max "-" num                              : stlcTerm
syntax:max "⌜" term "⌝"                         : stlcTerm  -- lift a Lean value as Term.const
syntax:70  ident ident                          : stlcTerm  -- measure application
syntax:65  stlcTerm:65 " + " stlcTerm:66        : stlcTerm
syntax:max "¬" stlcTerm:max                     : stlcTerm
syntax:35  stlcTerm:36 " ∧ " stlcTerm:35        : stlcTerm
syntax:10  "if " stlcTerm " ≤ " stlcTerm " then " stlcTerm " else " stlcTerm : stlcTerm
syntax:10  "if " stlcTerm " then " stlcTerm " else " stlcTerm : stlcTerm

-- Formulas
syntax:max "⊤"                                  : stlcFormula
syntax:max "⊥"                                  : stlcFormula
syntax:max "(" stlcFormula ")"                  : stlcFormula
syntax:50 stlcTerm:51 " = " stlcTerm:51                  : stlcFormula
syntax:50 stlcTerm:51 " ≠ " stlcTerm:51                  : stlcFormula
syntax:50 stlcTerm:51 " ≤ " stlcTerm:51                  : stlcFormula
syntax:50 stlcTerm:51 " < " stlcTerm:51                  : stlcFormula
syntax:50 stlcTerm:51 " ≥ " stlcTerm:51                  : stlcFormula
syntax:50 stlcTerm:51 " > " stlcTerm:51                  : stlcFormula
syntax:35 stlcFormula:36 " ∧ " stlcFormula:35   : stlcFormula
syntax:30 stlcFormula:31 " ∨ " stlcFormula:30   : stlcFormula
syntax:max "¬" stlcFormula:max                  : stlcFormula
syntax:25 stlcFormula:26 " → " stlcFormula:25   : stlcFormula
syntax:20 stlcFormula:21 " ↔ " stlcFormula:21   : stlcFormula
syntax:max "∃ " ident " : " ident ", " stlcFormula : stlcFormula
syntax:max "∀ " ident " : " ident ", " stlcFormula : stlcFormula

-- Refinements: a kvar-free formula, or a κ-application `κ t₁ … tₙ`
syntax:max stlcFormula                          : stlcRefine
syntax:max ident (colGt stlcTerm:max)*          : stlcRefine

-- Kinds
syntax "⋆"                                      : stlcKind
syntax ident                                    : stlcKind  -- `B`

-- Types
syntax:max ident                                : stlcTy
syntax:max ident "[" stlcTy,* "]"               : stlcTy
syntax:max ident "{" ident " : " stlcRefine "}" : stlcTy
syntax:max ident "[" stlcTy,* "]" "{" ident " : " stlcRefine "}" : stlcTy
syntax:max "(" stlcTy ")"                       : stlcTy
syntax:max "⌜" term "⌝"                         : stlcTy
syntax:25  "∀ " ident (" : " stlcKind)? ", " stlcTy  : stlcTy
syntax:25  "(" ident " : " stlcTy ")" " -> " stlcTy:25 : stlcTy
syntax:25  stlcTy:26 " -> " stlcTy:25           : stlcTy
syntax:35  "(" ident " : " stlcTy ")" " × " stlcTy:35  : stlcTy
syntax:35  stlcTy:36 " × " stlcTy:35            : stlcTy

-- Binders and patterns
syntax ident                                    : stlcBinder
syntax "_"                                      : stlcBinder
syntax stlcBinder                               : stlcPat
syntax "(" stlcPat ")"                          : stlcPat
syntax "(" stlcPat ", " stlcPat,+ ")"           : stlcPat
syntax ident (ppSpace stlcBinder)* " => " stlcExp : stlcAlt

-- Expressions
syntax:max "(" stlcExp ")"                      : stlcExp
syntax:max "(" ")"                              : stlcExp
syntax:max "(" stlcExp ", " stlcExp,+ ")"       : stlcExp
syntax:max "(" stlcExp " : " stlcTy ")"         : stlcExp
syntax:max ident                                : stlcExp
syntax:max num                                  : stlcExp
syntax:max "-" num                              : stlcExp
syntax:max "⌜" term "⌝"                         : stlcExp
syntax:max "unreachable"                        : stlcExp
syntax:max "¬" stlcExp:max                      : stlcExp
syntax:max stlcExp:max "[" stlcTy,* "]"         : stlcExp  -- type application
syntax:70 stlcExp:70 stlcExp:71                 : stlcExp  -- application
syntax:60 stlcExp:60 " + " stlcExp:61           : stlcExp
syntax:50 stlcExp:50 " ≤ " stlcExp:51           : stlcExp
syntax:45 stlcExp:45 " ∧ " stlcExp:46           : stlcExp
-- Binders/conditionals are below application precedence so they can only
-- appear as a whole expression (or inside parens), never as an application
-- operand; their bodies parse at the lowest precedence so they extend as far
-- right as possible (e.g. swallowing trailing applications).
syntax:10 "λ " (ppSpace stlcBinder)+ ", " stlcExp         : stlcExp
syntax:10 "Λ " ident (" : " stlcKind)? ", " stlcExp       : stlcExp
syntax:10 "fix " ident ppSpace stlcBinder ", " stlcExp     : stlcExp
syntax:10 "let " stlcPat (" : " stlcTy)? " = " stlcExp " in " stlcExp : stlcExp
syntax:10 "if " stlcExp " then " stlcExp " else " stlcExp : stlcExp
syntax:10 "match " stlcExp " with" (ppDedent(ppLine) " | " stlcAlt)+ : stlcExp

-- Top-level brackets
syntax (name := stlcProg)   "<|"  stlcExp "|>" : term
syntax (name := stlcTyProg) "<ty|" stlcTy "|>" : term

/-! ## Elaboration

  The helpers run in `MacroM` and produce the term to elaborate; the
  constructor registry is read once, up front, and passed in the context. -/

class ToTerm (α : Type) (b : outParam Base) where
  toTerm : α → Term b

instance : ToTerm Int  .int  where toTerm n := .const .int  n
instance : ToTerm Bool .bool where toTerm b := .const .bool b

open Lean

/-- A sort, as the notation tracks it. A type variable is recorded by its de
    Bruijn *level* (its position counted from the outermost type binder), which
    does not change as more type variables are bound; it becomes a
    `Base.tbvar` index where it is used. -/
inductive SBase where
  | int  : SBase
  | bool : SBase
  | tv   : Nat → SBase
  deriving BEq, Inhabited

/-- The scopes. Stacks are innermost first, so a name's position in its stack
    is its de Bruijn index. A variable records its sort, if known. -/
structure Ctx where
  vars  : List (String × Option SBase) := []
  tvars : List String := []
  ctors : CtorTable := {}

namespace Ctx

def push (c : Ctx) (x : String) (b : Option SBase := none) : Ctx :=
  { c with vars := (x, b) :: c.vars }

def pushTv (c : Ctx) (a : String) : Ctx := { c with tvars := a :: c.tvars }

def bound (c : Ctx) (x : String) : Bool := c.vars.any (·.1 == x)

def lookup (c : Ctx) (x : String) : Option (Nat × Option SBase) := do
  let i ← c.vars.findIdx? (·.1 == x)
  return (i, c.vars[i]!.2)

/-- A name for a compiled-away binder at the current depth: unique, and not
    a name the user can write. -/
def hidden (c : Ctx) (offset : Nat := 0) : String := s!"%{c.vars.length + offset}"

end Ctx

private def nameOf (x : TSyntax `ident) : String := x.getId.toString

private def binderName : TSyntax `stlcBinder → String
  | `(stlcBinder| $x:ident) => nameOf x
  | _ => ""

/-- The sort named `b`: `Int`, `Bool` or a type variable in scope. -/
private def sortOf? (c : Ctx) (b : String) : Option SBase :=
  match b with
  | "Int"  => some .int
  | "Bool" => some .bool
  | _      => (c.tvars.findIdx? (· == b)).map fun i => .tv (c.tvars.length - 1 - i)

private def resolveSort (c : Ctx) (b : TSyntax `ident) : MacroM SBase :=
  match sortOf? c (nameOf b) with
  | some s => pure s
  | none   => Macro.throwErrorAt b s!"expected 'Int', 'Bool' or a type variable, got '{nameOf b}'"

private def baseStx (c : Ctx) : SBase → MacroM (TSyntax `term)
  | .int  => `(Base.int)
  | .bool => `(Base.bool)
  | .tv l =>
      if l < c.tvars.length then `(Base.tbvar $(quote (c.tvars.length - 1 - l)))
      else Macro.throwError "type variable used out of scope"

private def kindStx : TSyntax `stlcKind → MacroM (TSyntax `term)
  | `(stlcKind| ⋆) => `(Kind.star)
  | `(stlcKind| $k:ident) =>
      if nameOf k == "B" then `(Kind.B) else Macro.throwErrorAt k "expected a kind, '⋆' or 'B'"
  | _ => Macro.throwUnsupported

private def optKindStx : Option (TSyntax `stlcKind) → MacroM (TSyntax `term)
  | some k => kindStx k
  | none   => `(Kind.star)

/-! ### Refinements -/

/-- The sort of a term, when it is determined by the term itself. -/
private partial def termSort? (c : Ctx) (t : TSyntax `stlcTerm) : Option SBase :=
  match t with
  | `(stlcTerm| ($inner:stlcTerm))         => termSort? c inner
  | `(stlcTerm| ($_:stlcTerm : $b:ident))  => sortOf? c (nameOf b)
  | `(stlcTerm| $_:num)                    => some .int
  | `(stlcTerm| - $_:num)                  => some .int
  | `(stlcTerm| $_:ident $_:ident)         => some .int
  | `(stlcTerm| $_:stlcTerm + $_:stlcTerm) => some .int
  | `(stlcTerm| ¬ $_:stlcTerm)             => some .bool
  | `(stlcTerm| $_:stlcTerm ∧ $_:stlcTerm) => some .bool
  | `(stlcTerm| if $_:stlcTerm ≤ $_:stlcTerm then $a:stlcTerm else $b:stlcTerm) =>
      termSort? c a <|> termSort? c b
  | `(stlcTerm| if $_:stlcTerm then $a:stlcTerm else $b:stlcTerm) =>
      termSort? c a <|> termSort? c b
  | `(stlcTerm| $x:ident) =>
      match c.lookup (nameOf x) with
      | some (_, b) => b
      | none => if nameOf x == "true" || nameOf x == "false" then some .bool else none
  | _ => none

mutual

/-- Elaborate a term; `exp` is the sort its context expects, if any. -/
private partial def eTerm (c : Ctx) (exp : Option SBase) (t : TSyntax `stlcTerm) :
    MacroM (TSyntax `term) := do
  match t with
  | `(stlcTerm| ($inner:stlcTerm))            => eTerm c exp inner
  | `(stlcTerm| ($inner:stlcTerm : $b:ident)) => do eTerm c (some (← resolveSort c b)) inner
  | `(stlcTerm| $n:num)                       => `(Term.const Base.int $n)
  | `(stlcTerm| - $n:num)                     => `(Term.const Base.int (-$n))
  | `(stlcTerm| ⌜ $e:term ⌝)                  => `(ToTerm.toTerm $e)
  | `(stlcTerm| $m:ident $x:ident)            => do
      let ms := quote (nameOf m)
      match c.lookup (nameOf x) with
      | some (i, _) => `(Term.mbvar $ms $(quote i))
      | none        => `(Term.mfvar $ms $(quote (nameOf x)))
  | `(stlcTerm| $a:stlcTerm + $b:stlcTerm)    => do
      `(Term.add $(← eTerm c (some .int) a) $(← eTerm c (some .int) b))
  | `(stlcTerm| ¬ $a:stlcTerm)                => do `(Term.not $(← eTerm c (some .bool) a))
  | `(stlcTerm| $a:stlcTerm ∧ $b:stlcTerm)    => do
      `(Term.and $(← eTerm c (some .bool) a) $(← eTerm c (some .bool) b))
  | `(stlcTerm| if $a:stlcTerm ≤ $b:stlcTerm then $t:stlcTerm else $e:stlcTerm) => do
      let s := exp <|> termSort? c t <|> termSort? c e |>.getD .int
      `(Term.ite $(← baseStx c s) (Term.leqI $(← eTerm c (some .int) a) $(← eTerm c (some .int) b))
          $(← eTerm c (some s) t) $(← eTerm c (some s) e))
  | `(stlcTerm| if $a:stlcTerm then $t:stlcTerm else $e:stlcTerm) => do
      let s := exp <|> termSort? c t <|> termSort? c e |>.getD .int
      `(Term.ite $(← baseStx c s) $(← eTerm c (some .bool) a)
          $(← eTerm c (some s) t) $(← eTerm c (some s) e))
  | `(stlcTerm| $x:ident)                     => do
      let sortStx (s : Option SBase) : MacroM (TSyntax `term) :=
        match s with
        | some s => baseStx c s
        | none   => `(_)
      match c.lookup (nameOf x) with
      | some (i, s) => `(Term.bvar $(← sortStx (s <|> exp)) $(quote i))
      | none =>
          match nameOf x with
          | "true"  => `(Term.const Base.bool true)
          | "false" => `(Term.const Base.bool false)
          | n       => `(Term.fvar $(← sortStx exp) $(quote n))
  | _ => Macro.throwUnsupported

/-- The comparison `a ≤ b`, at the sort of either side (`Int` if neither has one). -/
private partial def eLeq (c : Ctx) (a b : TSyntax `stlcTerm) : MacroM (TSyntax `term) := do
  let s := termSort? c a <|> termSort? c b |>.getD .int
  let ta ← eTerm c (some s) a
  let tb ← eTerm c (some s) b
  if s == .int then `(Formula.leqI $ta $tb) else `(Formula.leq $(← baseStx c s) $ta $tb)

private partial def eEq (c : Ctx) (a b : TSyntax `stlcTerm) : MacroM (TSyntax `term) := do
  let s? := termSort? c a <|> termSort? c b
  let bs ← match s? with
    | some s => baseStx c s
    | none   => `(_)
  `(Formula.eq $bs $(← eTerm c s? a) $(← eTerm c s? b))

private partial def eFormula (c : Ctx) (f : TSyntax `stlcFormula) : MacroM (TSyntax `term) := do
  match f with
  | `(stlcFormula| ⊤)                                => `(Formula.tt)
  | `(stlcFormula| ⊥)                                => `(Formula.ff)
  | `(stlcFormula| ($inner:stlcFormula))             => eFormula c inner
  | `(stlcFormula| $a:stlcTerm = $b:stlcTerm)        => eEq c a b
  | `(stlcFormula| $a:stlcTerm ≠ $b:stlcTerm)        => do `(Formula.not $(← eEq c a b))
  | `(stlcFormula| $a:stlcTerm ≤ $b:stlcTerm)        => eLeq c a b
  | `(stlcFormula| $a:stlcTerm < $b:stlcTerm)        => do `(Formula.not $(← eLeq c b a))
  | `(stlcFormula| $a:stlcTerm ≥ $b:stlcTerm)        => eLeq c b a
  | `(stlcFormula| $a:stlcTerm > $b:stlcTerm)        => do `(Formula.not $(← eLeq c a b))
  | `(stlcFormula| $a:stlcFormula ∧ $b:stlcFormula)  => do
      `(Formula.and $(← eFormula c a) $(← eFormula c b))
  | `(stlcFormula| $a:stlcFormula ∨ $b:stlcFormula)  => do
      `(Formula.or $(← eFormula c a) $(← eFormula c b))
  | `(stlcFormula| ¬ $a:stlcFormula)                 => do `(Formula.not $(← eFormula c a))
  | `(stlcFormula| $a:stlcFormula → $b:stlcFormula)  => do
      `(Formula.imp $(← eFormula c a) $(← eFormula c b))
  | `(stlcFormula| $a:stlcFormula ↔ $b:stlcFormula)  => do
      let ta ← eFormula c a; let tb ← eFormula c b
      `(Formula.and (Formula.imp $ta $tb) (Formula.imp $tb $ta))
  | `(stlcFormula| ∃ $x:ident : $b:ident, $body:stlcFormula) => do
      let s ← resolveSort c b
      `(Formula.ex $(← baseStx c s) $(← eFormula (c.push (nameOf x) s) body))
  | `(stlcFormula| ∀ $x:ident : $b:ident, $body:stlcFormula) => do
      let s ← resolveSort c b
      `(Formula.all $(← baseStx c s) $(← eFormula (c.push (nameOf x) s) body))
  | _ => Macro.throwUnsupported

private partial def eRefine (c : Ctx) (r : TSyntax `stlcRefine) : MacroM (TSyntax `term) := do
  match r with
  | `(stlcRefine| $k:ident $args:stlcTerm*) => do
      let targs ← args.mapM fun a => do
        let s := termSort? c a |>.getD .int
        `(term| (⟨$(← baseStx c s), $(← eTerm c (some s) a)⟩ : Σ b : Base, Term b))
      `(Refinement.kapp $(quote (nameOf k)) [$targs,*])
  | `(stlcRefine| $f:stlcFormula) => do `(Refinement.fmla $(← eFormula c f))
  | _ => Macro.throwUnsupported

end

/-! ### Types -/

/-- The sort a binder of type `t` is bound at: a refined base or type variable
    contributes its sort; other types have none. -/
private partial def tySort? (c : Ctx) (t : TSyntax `stlcTy) : Option SBase :=
  match t with
  | `(stlcTy| ($inner:stlcTy))                          => tySort? c inner
  | `(stlcTy| $b:ident)                                 => sortOf? c (nameOf b)
  | `(stlcTy| $b:ident { $_:ident : $_:stlcRefine })    => sortOf? c (nameOf b)
  | _                                                   => none

mutual

/-- `name[args]{v : r}`: a refined base or type variable, or a datatype. -/
private partial def eNamedTy (c : Ctx) (name : TSyntax `ident) (args : Array (TSyntax `stlcTy))
    (ref : Option (TSyntax `ident × TSyntax `stlcRefine)) : MacroM (TSyntax `term) := do
  match sortOf? c (nameOf name) with
  | some s =>
      unless args.isEmpty do
        Macro.throwErrorAt name s!"'{nameOf name}' takes no type arguments"
      let r ← match ref with
        | some (v, r) => eRefine (c.push (nameOf v) s) r
        | none        => `(Refinement.fmla Formula.tt)
      `(Ty.refine $(← baseStx c s) $r)
  | none =>
      let targs ← args.mapM (eTy c)
      let dn := quote (nameOf name)
      match ref with
      | some (v, r) => `(Ty.dataL $dn [$targs,*] $(← eRefine (c.push (nameOf v)) r))
      | none        => `(Ty.dataL $dn [$targs,*])

private partial def eTy (c : Ctx) (t : TSyntax `stlcTy) : MacroM (TSyntax `term) := do
  match t with
  | `(stlcTy| ($inner:stlcTy))                              => eTy c inner
  | `(stlcTy| ⌜ $e:term ⌝)                                  => pure e
  | `(stlcTy| $b:ident)                                     => eNamedTy c b #[] none
  | `(stlcTy| $b:ident [ $ts,* ])                           => eNamedTy c b ts.getElems none
  | `(stlcTy| $b:ident { $v:ident : $r:stlcRefine })        => eNamedTy c b #[] (some (v, r))
  | `(stlcTy| $b:ident [ $ts,* ] { $v:ident : $r:stlcRefine }) =>
      eNamedTy c b ts.getElems (some (v, r))
  | `(stlcTy| ∀ $a:ident $[: $k]?, $body:stlcTy)            => do
      `(Ty.forall $(← optKindStx k) $(← eTy (c.pushTv (nameOf a)) body))
  | `(stlcTy| ($x:ident : $s:stlcTy) -> $t:stlcTy)          => do
      `(Ty.arrow $(← eTy c s) $(← eTy (c.push (nameOf x) (tySort? c s)) t))
  | `(stlcTy| $s:stlcTy -> $t:stlcTy)                       => do
      `(Ty.arrow $(← eTy c s) $(← eTy (c.push "" (tySort? c s)) t))
  | `(stlcTy| ($x:ident : $s:stlcTy) × $t:stlcTy)           => do
      `(Ty.prod $(← eTy c s) $(← eTy (c.push (nameOf x) (tySort? c s)) t))
  | `(stlcTy| $s:stlcTy × $t:stlcTy)                        => do
      `(Ty.prod $(← eTy c s) $(← eTy (c.push "" (tySort? c s)) t))
  | _ => Macro.throwUnsupported

end

/-! ### Expressions -/

/-- The sort of a `let`-bound expression, when evident. -/
private partial def expSort? (c : Ctx) (e : TSyntax `stlcExp) : Option SBase :=
  match e with
  | `(stlcExp| ($inner:stlcExp))           => expSort? c inner
  | `(stlcExp| ($_:stlcExp : $t:stlcTy))   => tySort? c t
  | `(stlcExp| $_:num)                     => some .int
  | `(stlcExp| - $_:num)                   => some .int
  | `(stlcExp| $_:stlcExp + $_:stlcExp)    => some .int
  | `(stlcExp| $_:stlcExp ≤ $_:stlcExp)    => some .bool
  | `(stlcExp| $_:stlcExp ∧ $_:stlcExp)    => some .bool
  | `(stlcExp| ¬ $_:stlcExp)               => some .bool
  | `(stlcExp| $x:ident)                   =>
      match c.lookup (nameOf x) with
      | some (_, s) => s
      | none => if nameOf x == "true" || nameOf x == "false" then some .bool else none
  | _ => none

private partial def patName? : TSyntax `stlcPat → Option String
  | `(stlcPat| $b:stlcBinder) => some (binderName b)
  | `(stlcPat| ($p:stlcPat)) => patName? p
  | _ => none

private partial def patComps? : TSyntax `stlcPat → Option (List (TSyntax `stlcPat))
  | `(stlcPat| ($p:stlcPat)) => patComps? p
  | `(stlcPat| ($p:stlcPat, $ps:stlcPat,*)) => some (p :: ps.getElems.toList)
  | _ => none

private def varRef (c : Ctx) (x : String) : MacroM (TSyntax `term) :=
  match c.lookup x with
  | some (i, _) => `(Exp.bvar $(quote i))
  | none        => Macro.throwError s!"internal: unbound '{x}'"

/-- A step of an application spine: type arguments, or an argument. -/
private inductive SArg where
  | tys : Array (TSyntax `stlcTy) → SArg
  | exp : TSyntax `stlcExp → SArg

private partial def spine (e : TSyntax `stlcExp) : TSyntax `stlcExp × Array SArg :=
  match e with
  | `(stlcExp| $f:stlcExp $a:stlcExp) => let (h, as) := spine f; (h, as.push (.exp a))
  | `(stlcExp| $f:stlcExp [ $ts,* ])  => let (h, as) := spine f; (h, as.push (.tys ts.getElems))
  | _ => (e, #[])

/-- The constructor named `x`, unless a variable shadows it. -/
private def ctor? (c : Ctx) (x : TSyntax `ident) : Option CtorInfo :=
  if c.bound (nameOf x) then none else c.ctors[nameOf x]?

mutual

/-- Destructure `src` (elaborated in `c`) by the tuple pattern `p :: ps`. The
    components that are binders name the pair's binders directly; the others
    are bound to a hidden name and destructured in turn. -/
private partial def eSplit (c : Ctx) (src : TSyntax `term) (p : TSyntax `stlcPat)
    (ps : List (TSyntax `stlcPat)) (k : Ctx → MacroM (TSyntax `term)) : MacroM (TSyntax `term) := do
  let x := (patName? p).getD (c.hidden 0)
  let y := match ps with
    | [q] => (patName? q).getD (c.hidden 1)
    | _   => c.hidden 1
  let c' := (c.push x).push y
  let body ← destructVar c' p x fun c'' =>
    match ps with
    | [q]     => destructVar c'' q y k
    | q :: qs => do eSplit c'' (← varRef c'' y) q qs k
    | []      => Macro.throwError "internal: empty tuple pattern"
  `(Exp.split $src $body)

/-- Destructure the variable named `x` by `p` (nothing to do for a binder,
    which already named it). -/
private partial def destructVar (c : Ctx) (p : TSyntax `stlcPat) (x : String)
    (k : Ctx → MacroM (TSyntax `term)) : MacroM (TSyntax `term) := do
  match patComps? p with
  | some (q :: qs) => eSplit c (← varRef c x) q qs k
  | _              => k c

end

/-- Bind the fields `xs` of the payload held by the variable `src`: the
    payload is `(x₀, (x₁, … (xₙ₋₁, ())))`. -/
private partial def eFields (c : Ctx) (src : String) (xs : List String)
    (k : Ctx → MacroM (TSyntax `term)) : MacroM (TSyntax `term) := do
  match xs with
  | [] => k c
  | x :: rest =>
      let y := if rest.isEmpty then "" else c.hidden 1
      let body ← eFields ((c.push x).push y) y rest k
      `(Exp.split $(← varRef c src) $body)

mutual

/-- A constructor application `C[τs] e₁ … eₙ`, if `e` is one. -/
private partial def eCtorApp? (c : Ctx) (e : TSyntax `stlcExp) :
    MacroM (Option (TSyntax `term)) := do
  let (h, args) := spine e
  let `(stlcExp| $x:ident) := h | return none
  let some info := ctor? c x | return none
  let (tys, rest) := match args.toList with
    | .tys ts :: r => (ts, r)
    | r            => (#[], r)
  let es ← rest.mapM fun
    | .exp a  => pure a
    | .tys _  => Macro.throwErrorAt e "type arguments of a constructor go right after its name"
  unless es.length == info.nfields do
    Macro.throwErrorAt e
      s!"constructor '{nameOf x}' has {info.nfields} field(s), applied to {es.length}"
  let targs ← tys.mapM (eTy c)
  let payload ← es.foldrM (fun a acc => do `(Exp.pair $(← eExp c a) $acc)) (← `(Exp.iconst 0))
  return some (← `(Exp.ctor $(quote info.dtype) $(quote info.idx) [$targs,*] $payload))

private partial def eExp (c : Ctx) (e : TSyntax `stlcExp) : MacroM (TSyntax `term) := do
  if let some t ← eCtorApp? c e then return t
  match e with
  | `(stlcExp| ($inner:stlcExp))               => eExp c inner
  | `(stlcExp| ())                             => `(Exp.iconst 0)
  | `(stlcExp| ($a:stlcExp, $bs:stlcExp,*))    => do
      let es := #[a] ++ bs.getElems
      let last ← eExp c es.back!
      es.pop.foldrM (fun a acc => do `(Exp.pair $(← eExp c a) $acc)) last
  | `(stlcExp| ($inner:stlcExp : $ty:stlcTy))  => do `(Exp.ann $(← eExp c inner) $(← eTy c ty))
  | `(stlcExp| $n:num)                         => `(Exp.iconst $n)
  | `(stlcExp| - $n:num)                       => `(Exp.iconst (-$n))
  | `(stlcExp| ⌜ $t:term ⌝)                    => pure t
  | `(stlcExp| unreachable)                    => `(Exp.unreach)
  | `(stlcExp| $x:ident)                       =>
      match c.lookup (nameOf x) with
      | some (i, _) => `(Exp.bvar $(quote i))
      | none =>
          match nameOf x with
          | "true"  => `(Exp.bconst true)
          | "false" => `(Exp.bconst false)
          | n       => `(Exp.fvar $(quote n))
  | `(stlcExp| λ $xs:stlcBinder*, $body:stlcExp) => do
      let c' := xs.foldl (fun c x => c.push (binderName x)) c
      xs.foldrM (fun _ acc => `(Exp.lam $acc)) (← eExp c' body)
  | `(stlcExp| Λ $a:ident $[: $k]?, $body:stlcExp) => do
      `(Exp.tabs $(← optKindStx k) $(← eExp (c.pushTv (nameOf a)) body))
  | `(stlcExp| fix $f:ident $x:stlcBinder, $body:stlcExp) => do
      `(Exp.fix $(← eExp ((c.push (nameOf f)).push (binderName x)) body))
  | `(stlcExp| let $p:stlcPat $[: $ty?]? = $e1:stlcExp in $e2:stlcExp) => do
      let t1 ← eExp c e1
      let (t1, s) ← match ty? with
        | some ty => pure (← `(Exp.ann $t1 $(← eTy c ty)), tySort? c ty)
        | none    => pure (t1, expSort? c e1)
      match patName? p, patComps? p with
      | some x, _ => `(Exp.letin $t1 $(← eExp (c.push x s) e2))
      | _, some (q :: qs) => eSplit c t1 q qs (eExp · e2)
      | _, _ => Macro.throwUnsupported
  | `(stlcExp| if $a:stlcExp then $t:stlcExp else $f:stlcExp) => do
      `(Exp.ite $(← eExp c a) $(← eExp c t) $(← eExp c f))
  | `(stlcExp| match $s:stlcExp with $[| $alts:stlcAlt]*) => do
      let ts ← eExp c s
      let mut arms : Array (Nat × TSyntax `term) := #[]
      let mut dt : Option CtorInfo := none
      for alt in alts do
        let `(stlcAlt| $k:ident $xs:stlcBinder* => $body:stlcExp) := alt | Macro.throwUnsupported
        let some info := c.ctors[nameOf k]? | Macro.throwErrorAt k s!"unknown constructor '{nameOf k}'"
        if let some d := dt then
          unless d.dtype == info.dtype do
            Macro.throwErrorAt k s!"'{nameOf k}' is a constructor of '{info.dtype}', not '{d.dtype}'"
        dt := some info
        unless xs.size == info.nfields do
          Macro.throwErrorAt alt s!"constructor '{nameOf k}' has {info.nfields} field(s)"
        if arms.any (·.1 == info.idx) then
          Macro.throwErrorAt k s!"duplicate alternative for '{nameOf k}'"
        let p := c.hidden 0
        let arm ← eFields (c.push p) p (xs.toList.map binderName) (eExp · body)
        arms := arms.push (info.idx, arm)
      let some d := dt | Macro.throwUnsupported
      unless arms.size == d.nctors do
        Macro.throwErrorAt e s!"'match' on '{d.dtype}' needs one alternative per constructor"
      let sorted := (arms.qsort (·.1 < ·.1)).map (·.2)
      `(caseL $ts [$sorted,*])
  | `(stlcExp| ¬ $a:stlcExp)                   => do `(Exp.not $(← eExp c a))
  | `(stlcExp| $a:stlcExp + $b:stlcExp)        => do `(Exp.add $(← eExp c a) $(← eExp c b))
  | `(stlcExp| $a:stlcExp ≤ $b:stlcExp)        => do `(Exp.leq $(← eExp c a) $(← eExp c b))
  | `(stlcExp| $a:stlcExp ∧ $b:stlcExp)        => do `(Exp.and $(← eExp c a) $(← eExp c b))
  | `(stlcExp| $f:stlcExp [ $ts,* ])           => do
      ts.getElems.foldlM (fun acc τ => do `(Exp.tapp $acc $(← eTy c τ))) (← eExp c f)
  | `(stlcExp| $f:stlcExp $a:stlcExp)          => do `(Exp.app $(← eExp c f) $(← eExp c a))
  | _ => Macro.throwUnsupported

end

/-! ### Entry points -/

open Elab Term in
@[term_elab stlcProg] def elabStlcProg : TermElab := fun stx expected? => do
  let `(<| $e |>) := stx | throwUnsupportedSyntax
  let c : Ctx := { ctors := ctorExt.getState (← getEnv) }
  elabTerm (← liftMacroM (eExp c e)) expected?

open Elab Term in
@[term_elab stlcTyProg] def elabStlcTy : TermElab := fun stx expected? => do
  let `(<ty| $t |>) := stx | throwUnsupportedSyntax
  let c : Ctx := { ctors := ctorExt.getState (← getEnv) }
  elabTerm (← liftMacroM (eTy c t)) expected?

/-! ## Datatype declarations -/

declare_syntax_cat stlcParam
declare_syntax_cat stlcField
declare_syntax_cat stlcCtor
declare_syntax_cat stlcMBody
declare_syntax_cat stlcMAlt

syntax "(" ident (" : " stlcKind)? ")"          : stlcParam
syntax "(" "+" ident (" : " stlcKind)? ")"      : stlcParam
syntax "(" "-" ident (" : " stlcKind)? ")"      : stlcParam
syntax "(" stlcBinder " : " stlcTy ")"          : stlcField
syntax "| " ident (ppSpace stlcField)*          : stlcCtor

syntax:max num                                  : stlcMBody
syntax:max "-" num                              : stlcMBody
syntax:max "(" stlcMBody ")"                    : stlcMBody
syntax:max ident                                : stlcMBody  -- an `Int` field
syntax:70  ident (colGt stlcMBody:max)+         : stlcMBody  -- `m f`, `max a b`
syntax:65  stlcMBody:65 " + " stlcMBody:66      : stlcMBody
syntax:10  "if " stlcMBody " ≤ " stlcMBody " then " stlcMBody " else " stlcMBody : stlcMBody
syntax:10  "if " ident " then " stlcMBody " else " stlcMBody : stlcMBody
syntax "| " ident (ppSpace stlcBinder)* " => " stlcMBody : stlcMAlt
syntax stlcMeasure := &"measure " ident (ppLine stlcMAlt)+

/-- `stlc_data declName : D params where | C₁ fields | … measure m | C₁ xs => body | …`
    defines `declName : DataDecl` for the datatype `D` and registers its
    constructors with the notation. -/
syntax (name := stlcData) (docComment)? "stlc_data " ident " : " ident (ppSpace stlcParam)*
  " where" (ppLine stlcCtor)+ (ppLine stlcMeasure)* : command

private partial def eMBody (fields : List String) (b : TSyntax `stlcMBody) :
    MacroM (TSyntax `term) := do
  let field (x : TSyntax `ident) : MacroM Nat :=
    match fields.findIdx? (· == nameOf x) with
    | some i => pure i
    | none   => Macro.throwErrorAt x s!"'{nameOf x}' is not a field of this constructor"
  match b with
  | `(stlcMBody| $n:num)                       => `(MBody.const $n)
  | `(stlcMBody| - $n:num)                     => `(MBody.const (-$n))
  | `(stlcMBody| ($inner:stlcMBody))           => eMBody fields inner
  | `(stlcMBody| $x:ident)                     => do `(MBody.field $(quote (← field x)))
  | `(stlcMBody| $f:ident $args:stlcMBody*)    => do
      match nameOf f, args with
      | "max", #[a, b] => `(MBody.max $(← eMBody fields a) $(← eMBody fields b))
      | m, #[a] =>
          let `(stlcMBody| $x:ident) := a
            | Macro.throwErrorAt a "a measure is applied to a field"
          `(MBody.meas $(quote m) $(quote (← field x)))
      | _, _ => Macro.throwErrorAt b "expected 'm f' or 'max a b'"
  | `(stlcMBody| $a:stlcMBody + $b:stlcMBody)  => do
      `(MBody.add $(← eMBody fields a) $(← eMBody fields b))
  | `(stlcMBody| if $a:stlcMBody ≤ $b:stlcMBody then $t:stlcMBody else $e:stlcMBody) => do
      `(MBody.iteLe $(← eMBody fields a) $(← eMBody fields b) $(← eMBody fields t)
          $(← eMBody fields e))
  | `(stlcMBody| if $x:ident then $t:stlcMBody else $e:stlcMBody) => do
      `(MBody.iteB $(quote (← field x)) $(← eMBody fields t) $(← eMBody fields e))
  | _ => Macro.throwUnsupported

/-- A parameter: its name, kind and variance (if declared). -/
private def eParam : TSyntax `stlcParam → MacroM (String × TSyntax `term × Option (TSyntax `term))
  | `(stlcParam| ($a:ident $[: $k]?))   => do pure (nameOf a, ← optKindStx k, none)
  | `(stlcParam| (+ $a:ident $[: $k]?)) => do pure (nameOf a, ← optKindStx k, some (← `(Variance.co)))
  | `(stlcParam| (- $a:ident $[: $k]?)) => do pure (nameOf a, ← optKindStx k, some (← `(Variance.contra)))
  | _ => Macro.throwUnsupported

/-- The fields of a constructor, as types: parameter `i` is `tbvar i`, and each
    field's type may mention the earlier fields. -/
private def eFieldTys (c : Ctx) (fs : Array (TSyntax `stlcField)) :
    MacroM (Array (TSyntax `term)) := do
  let mut c := c
  let mut out := #[]
  for f in fs do
    let `(stlcField| ($x:stlcBinder : $t:stlcTy)) := f | Macro.throwUnsupported
    out := out.push (← eTy c t)
    c := c.push (binderName x) (tySort? c t)
  return out

open Elab Command in
@[command_elab stlcData] def elabStlcData : CommandElab := fun stx => do
  let `($[$doc?:docComment]? stlc_data $declName:ident : $dname:ident $params:stlcParam* where $ctors:stlcCtor* $meas:stlcMeasure*) := stx
    | throwUnsupportedSyntax
  let dn := nameOf dname
  let ps ← liftMacroM (params.mapM eParam)
  let c : Ctx := { tvars := (ps.map (·.1)).toList }
  -- constructors
  let mut ctorNames : Array String := #[]
  let mut arity : Array Nat := #[]
  let mut ctorTerms : Array (TSyntax `term) := #[]
  for ct in ctors do
    let `(stlcCtor| | $k:ident $fs:stlcField*) := ct | throwUnsupportedSyntax
    if ctorNames.contains (nameOf k) then throwErrorAt k s!"duplicate constructor '{nameOf k}'"
    let tys ← liftMacroM (eFieldTys c fs)
    ctorNames := ctorNames.push (nameOf k)
    arity := arity.push fs.size
    ctorTerms := ctorTerms.push (← `(($(quote (nameOf k)), [$tys,*])))
  -- measures
  let mut measTerms : Array (TSyntax `term) := #[]
  for m in meas do
    -- `measure` is not a keyword (it is a common identifier), so the node is
    -- taken apart by position
    let mn : TSyntax `ident := ⟨m.raw[1]⟩
    let alts : Array (TSyntax `stlcMAlt) := m.raw[2].getArgs.map (⟨·⟩)
    let mut bodies : Array (Option (TSyntax `term)) := Array.replicate ctorNames.size none
    for alt in alts do
      let `(stlcMAlt| | $k:ident $xs:stlcBinder* => $body) := alt | throwUnsupportedSyntax
      let some j := ctorNames.idxOf? (nameOf k)
        | throwErrorAt k s!"'{nameOf k}' is not a constructor of '{dn}'"
      unless xs.size == arity[j]! do
        throwErrorAt alt s!"constructor '{nameOf k}' has {arity[j]!} field(s)"
      if bodies[j]!.isSome then throwErrorAt k s!"duplicate equation for '{nameOf k}'"
      let t ← liftMacroM (eMBody (xs.toList.map binderName) body)
      bodies := bodies.set! j (some t)
    let some bs := bodies.mapM id
      | throwErrorAt mn s!"measure '{nameOf mn}' needs one equation per constructor"
    measTerms := measTerms.push (← `(($(quote (nameOf mn)), [$bs,*])))
  -- the declaration
  let kinds := ps.map (·.2.1)
  let fields : Array (TSyntax ``Lean.Parser.Term.structInstField) := #[
    ← `(Lean.Parser.Term.structInstField| params := [$kinds,*]),
    ← `(Lean.Parser.Term.structInstField| ctorFields := [$ctorTerms,*])]
  let fields ← if ps.any (·.2.2.isSome) then do
      let vs ← ps.mapM fun p => match p.2.2 with
        | some v => pure v
        | none   => `(Variance.inv)
      pure (fields.push (← `(Lean.Parser.Term.structInstField| variances := [$vs,*])))
    else pure fields
  let fields ← if measTerms.isEmpty then pure fields else
      pure (fields.push (← `(Lean.Parser.Term.structInstField| measures := [$measTerms,*])))
  elabCommand (← `($[$doc?:docComment]? def $declName : DataDecl := { $fields:structInstField,* }))
  -- register the constructors, as `C` and as `D.C`
  for h : j in [0:ctorNames.size] do
    let info : CtorInfo := { dtype := dn, idx := j, nfields := arity[j]!, nctors := ctorNames.size }
    modifyEnv (ctorExt.addEntry · (ctorNames[j], info))
    modifyEnv (ctorExt.addEntry · (s!"{dn}.{ctorNames[j]}", info))

end STLC
