import Flex.VCG.SystemFRK.Syntax

/-! Functional surface syntax for SystemFRK. These macros emit the existing AST;
they do not change checking, evaluation, or proofs. Named type binders become
de Bruijn indices, and each refinement's witness becomes `$value`.

* `[frk| Λ α => fun (x : α) => x]`
* `[frkTy| ∀ α, (x : α) → α]`
* `[frkTy| (xs : List[Int]) → {v : List[Int] | len(v) = len(xs)}]`

`ctor cons[Int](head, tail)` constructs a value; `f[Int]` instantiates a type;
`measure len xs` observes a measure. `fix (xs : T) : U => ...` and `recur tail`
use the existing structural recursion checker. `⌜term⌝` splices existing core
syntax verbatim, including any free names or type indices it contains.
-/
namespace SystemFRK.Notation

open Lean

-- Contextual keywords remain usable as ordinary Lean identifiers outside a quote.
private def ctorKeyword : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "ctor" true
private def measureKeyword : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "measure" true
private def recurKeyword : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "recur" true
private def fixKeyword : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "fix" true
private def kvarKeyword : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "κ" true
private def typeLambdaKeyword : Lean.Parser.Parser := Lean.Parser.nonReservedSymbol "Λ" true

declare_syntax_cat frkLogic
declare_syntax_cat frkFormula
declare_syntax_cat frkPredicate
declare_syntax_cat frkType
declare_syntax_cat frkBinder
declare_syntax_cat frkExpr
declare_syntax_cat frkBranch

syntax:max ident : frkLogic
syntax:max num : frkLogic
syntax:max "-" num : frkLogic
syntax:max "⌜" term "⌝" : frkLogic
syntax:max "(" frkLogic ")" : frkLogic
syntax:max ident "(" frkLogic ")" : frkLogic
syntax:65 frkLogic:65 " + " frkLogic:66 : frkLogic

syntax:max ident : frkFormula
syntax:max "(" frkFormula ")" : frkFormula
syntax:50 frkLogic " = " frkLogic : frkFormula
syntax:50 frkLogic " ≤ " frkLogic : frkFormula
syntax:40 "¬ " frkFormula:40 : frkFormula
syntax:35 frkFormula:36 " ∧ " frkFormula:35 : frkFormula
syntax:30 frkFormula:31 " ∨ " frkFormula:30 : frkFormula
syntax frkFormula : frkPredicate
syntax (priority := high) kvarKeyword ident "(" frkLogic,* ")" : frkPredicate

syntax:max ident : frkType
syntax:max "⌜" term "⌝" : frkType
syntax:max "(" frkType ")" : frkType
syntax:max ident "[" frkType,* "]" : frkType
syntax:max "{" ident " : " frkType " | " frkPredicate "}" : frkType
syntax:25 "(" ident " : " frkType ")" " → " frkType : frkType
syntax:25 frkType:26 " → " frkType : frkType
syntax:10 "∀ " ident+ ", " frkType : frkType

syntax "(" ident " : " frkType ")" : frkBinder
syntax:max ident : frkExpr
syntax:max num : frkExpr
syntax:max "-" num : frkExpr
syntax:max "⌜" term "⌝" : frkExpr
syntax:max "(" frkExpr ")" : frkExpr
syntax:max "(" frkExpr " : " frkType ")" : frkExpr
syntax:max (priority := high) ctorKeyword ident "[" frkType,* "]" "(" frkExpr,* ")" : frkExpr
syntax:80 frkExpr:80 "[" frkType "]" : frkExpr
syntax:70 frkExpr:70 frkExpr:71 : frkExpr
syntax:71 (priority := high) measureKeyword ident frkExpr:71 : frkExpr
syntax:71 (priority := high) recurKeyword frkExpr:71 : frkExpr
syntax:10 "fun " frkBinder+ " => " frkExpr : frkExpr
syntax:10 (priority := high) typeLambdaKeyword ident+ " => " frkExpr : frkExpr
syntax:10 "let " ident " := " frkExpr "; " frkExpr : frkExpr
syntax:10 (priority := high) fixKeyword frkBinder " : " frkType " => " frkExpr : frkExpr
syntax "| " ident ident* " => " frkExpr : frkBranch
syntax:10 "match " frkExpr " with " frkBranch+ " end" : frkExpr

syntax "[frk| " frkExpr "]" : term
syntax "[frkTy| " frkType "]" : term

private def nameOf (name : TSyntax `ident) : String := name.getId.eraseMacroScopes.toString

private def binderName (name : TSyntax `ident) : MacroM String := do
  let name := nameOf name
  if ["true", "false", "ctor", "measure", "recur", "fix", "Λ"].contains name then
    Macro.throwError s!"'{name}' is reserved inside SystemFRK quotations"
  pure name

private partial def logic (witness : String) : TSyntax `frkLogic → MacroM (TSyntax `term)
  | `(frkLogic| ⌜$t:term⌝) => pure t
  | `(frkLogic| ($t:frkLogic)) => logic witness t
  | `(frkLogic| $n:num) => `(LTerm.int $n)
  | `(frkLogic| -$n:num) => `(LTerm.int (-$n))
  | `(frkLogic| $name:ident) =>
      if nameOf name == "true" then `(LTerm.bool true)
      else if nameOf name == "false" then `(LTerm.bool false)
      else `(LTerm.var $(quote (if nameOf name == witness then valueName else nameOf name)))
  | `(frkLogic| $name:ident ($arg:frkLogic)) => do
      let arg ← logic witness arg
      `(LTerm.measure $(quote (nameOf name)) $arg)
  | `(frkLogic| $a:frkLogic + $b:frkLogic) => do
      let a ← logic witness a; let b ← logic witness b
      `(LTerm.add $a $b)
  | _ => Macro.throwUnsupported

private partial def formula (witness : String) : TSyntax `frkFormula → MacroM (TSyntax `term)
  | `(frkFormula| $name:ident) =>
      if nameOf name == "True" then `(Formula.truth)
      else if nameOf name == "False" then `(Formula.falsity)
      else Macro.throwError "expected a comparison, True, or False"
  | `(frkFormula| ($p:frkFormula)) => formula witness p
  | `(frkFormula| $a:frkLogic = $b:frkLogic) => do
      let a ← logic witness a; let b ← logic witness b
      `(Formula.eq $a $b)
  | `(frkFormula| $a:frkLogic ≤ $b:frkLogic) => do
      let a ← logic witness a; let b ← logic witness b
      `(Formula.le $a $b)
  | `(frkFormula| ¬ $p:frkFormula) => do
      let p ← formula witness p; `(Formula.not $p)
  | `(frkFormula| $a:frkFormula ∧ $b:frkFormula) => do
      let a ← formula witness a; let b ← formula witness b
      `(Formula.and $a $b)
  | `(frkFormula| $a:frkFormula ∨ $b:frkFormula) => do
      let a ← formula witness a; let b ← formula witness b
      `(Formula.or $a $b)
  | _ => Macro.throwUnsupported

private def predicate (witness : String) : TSyntax `frkPredicate → MacroM (TSyntax `term)
  | `(frkPredicate| κ $name:ident ($args:frkLogic,*)) => do
      let args ← args.getElems.mapM (logic witness)
      `(Atom.kvar $(quote (nameOf name)) [$[$args],*])
  | `(frkPredicate| $p:frkFormula) => do
      let p ← formula witness p; `(Atom.theory $p)
  | _ => Macro.throwUnsupported

private partial def type (types : List String) : TSyntax `frkType → MacroM (TSyntax `term)
  | `(frkType| ⌜$t:term⌝) => pure t
  | `(frkType| ($t:frkType)) => type types t
  | `(frkType| $name:ident) => do
      let name := nameOf name
      match types.idxOf? name with
      | some index => `(Ty.var $(quote index))
      | none => match name with
        | "Int" => `(Ty.int)
        | "Bool" => `(Ty.bool)
        | _ => Macro.throwError s!"unbound type '{name}'; use {name}[] for a datatype or ⌜...⌝ for a Lean type expression"
  | `(frkType| $name:ident [$args:frkType,*]) => do
      let args ← args.getElems.mapM (type types)
      `(Ty.data $(quote (nameOf name)) [$[$args],*])
  | `(frkType| {$name:ident : $base:frkType | $p:frkPredicate}) => do
      let name ← binderName name
      let base ← type types base; let p ← predicate name p
      `(Ty.refine $base $p)
  | `(frkType| ($name:ident : $a:frkType) → $b:frkType) => do
      let a ← type types a; let b ← type types b
      `(Ty.arrow $(quote (nameOf name)) $a $b)
  | `(frkType| $a:frkType → $b:frkType) => do
      let a ← type types a; let b ← type types b
      `(Ty.arrow "_" $a $b)
  | `(frkType| ∀ $names:ident*, $body:frkType) => do
      let mut body ← type (names.toList.reverse.map nameOf ++ types) body
      for _ in names do body ← `(Ty.all $body)
      pure body
  | _ => Macro.throwUnsupported

private partial def expression (types : List String) : TSyntax `frkExpr → MacroM (TSyntax `term)
  | `(frkExpr| ⌜$e:term⌝) => pure e
  | `(frkExpr| ($e:frkExpr)) => expression types e
  | `(frkExpr| $name:ident) =>
      if nameOf name == "true" then `(SystemFRK.Expr.bool true)
      else if nameOf name == "false" then `(SystemFRK.Expr.bool false)
      else `(SystemFRK.Expr.var $(quote (nameOf name)))
  | `(frkExpr| $n:num) => `(SystemFRK.Expr.int $n)
  | `(frkExpr| -$n:num) => `(SystemFRK.Expr.int (-$n))
  | `(frkExpr| ($e:frkExpr : $t:frkType)) => do
      let e ← expression types e; let t ← type types t
      `(SystemFRK.Expr.ann $e $t)
  | `(frkExpr| $f:frkExpr [$t:frkType]) => do
      let f ← expression types f; let t ← type types t
      `(SystemFRK.Expr.tyApp $f $t)
  | `(frkExpr| $f:frkExpr $a:frkExpr) => do
      let f ← expression types f; let a ← expression types a
      `(SystemFRK.Expr.app $f $a)
  | `(frkExpr| fun $binders:frkBinder* => $body:frkExpr) => do
      let mut body ← expression types body
      for binder in binders.reverse do
        let `(frkBinder| ($name:ident : $domain:frkType)) := binder | Macro.throwUnsupported
        let name ← binderName name
        let domain ← type types domain
        body ← `(SystemFRK.Expr.lam $(quote name) $domain $body)
      pure body
  | `(frkExpr| Λ $names:ident* => $body:frkExpr) => do
      let mut body ← expression (names.toList.reverse.map nameOf ++ types) body
      for _ in names do body ← `(SystemFRK.Expr.tyLam $body)
      pure body
  | `(frkExpr| let $name:ident := $value:frkExpr; $body:frkExpr) => do
      let name ← binderName name
      let value ← expression types value; let body ← expression types body
      `(SystemFRK.Expr.letE $(quote name) $value $body)
  | `(frkExpr| ctor $name:ident [$args:frkType,*]($fields:frkExpr,*)) => do
      let args ← args.getElems.mapM (type types)
      let fields ← fields.getElems.mapM (expression types)
      `(SystemFRK.Expr.ctor $(quote (nameOf name)) [$[$args],*] [$[$fields],*])
  | `(frkExpr| measure $name:ident $arg:frkExpr) => do
      let arg ← expression types arg
      `(SystemFRK.Expr.measure $(quote (nameOf name)) $arg)
  | `(frkExpr| recur $arg:frkExpr) => do
      let arg ← expression types arg; `(SystemFRK.Expr.recur $arg)
  | `(frkExpr| fix ($name:ident : $domain:frkType) : $result:frkType => $body:frkExpr) => do
      let name ← binderName name
      let domain ← type types domain; let result ← type types result
      let body ← expression types body
      `(SystemFRK.Expr.structRec $(quote name) $domain $result $body)
  | `(frkExpr| match $scrutinee:frkExpr with $branches:frkBranch* end) => do
      let scrutinee ← expression types scrutinee
      let branches ← branches.mapM fun branch => do
        let `(frkBranch| | $name:ident $fields:ident* => $body:frkExpr) := branch | Macro.throwUnsupported
        let names ← fields.mapM (fun name => return quote (← binderName name))
        let body ← expression types body
        `(term| ($(quote (nameOf name)), [$[$names],*], $body))
      `(SystemFRK.Expr.matchE $scrutinee [$[$branches],*])
  | _ => Macro.throwUnsupported

macro_rules
  | `([frk| $e:frkExpr]) => expression [] e
  | `([frkTy| $t:frkType]) => type [] t

end SystemFRK.Notation
