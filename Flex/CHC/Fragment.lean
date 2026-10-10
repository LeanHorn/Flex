import Flex.CHC.Types
import Smt.Translate.Int
import Smt.Translate.Bool
import Smt.Translate.Prop

namespace Flex.CHC.Fragment

open Lean Meta

/-- Only first-order value sorts; no approximation of Nat, arrays, or functions. -/
def valueSort (type : Expr) : MetaM ValueSort := do
  let type ← whnf type
  if type.isConstOf ``Int then return .int
  if type.isConstOf ``Bool || type.isProp then return .bool
  throwError "CHC export: unsupported value type {type}; expected Int, Bool, or Prop"

/-- Scope the upstream handlers to the audited fragment. A user's registered
translator must not silently extend the language of this exporter. -/
def withTranslators (action : MetaM α) : MetaM α := do
  let extension := Smt.Attribute.smtExt
  let previous := (extension.getState (← getEnv)).getD ``Smt.Translator {}
  modifyEnv fun env => extension.modifyState env fun state =>
    state.insert ``Smt.Translator {
      ``Smt.Translate.Int.translateType, ``Smt.Translate.Int.translateInt,
      ``Smt.Translate.Int.translateProp, ``Smt.Translate.Bool.translateType,
      ``Smt.Translate.Bool.translateBool, ``Smt.Translate.Bool.translateProp,
      ``Smt.Translate.Prop.translateType, ``Smt.Translate.Prop.translateProp,
      ``Smt.Translate.Prop.translateIte }
  try action
  finally
    modifyEnv fun env => extension.modifyState env fun state =>
      state.insert ``Smt.Translator previous

private def application (term : Smt.Term) : Smt.Term × Array Smt.Term :=
  go term #[]
where
  go : Smt.Term → Array Smt.Term → Smt.Term × Array Smt.Term
    | .appT f x, args => go f (#[x] ++ args)
    | f, args => (f, args)

private def numeral : Smt.Term → Bool
  | .literalT text => !text.isEmpty && text.toList.all Char.isDigit
  | .appT (.symbolT "-") (.literalT text) => !text.isEmpty && text.toList.all Char.isDigit
  | _ => false

/-- The upstream translator is broader than our solver interface. Check its AST,
including binders and operator arities; native parsing checks sorts afterwards. -/
partial def checkTerm (term : Smt.Term) (symbols : Array String) : MetaM Unit := do
  match term with
  | .literalT _ =>
    unless numeral term do throwError "CHC export: unsupported SMT literal {term}"
  | .symbolT name =>
    unless symbols.contains name || #["true", "false"].contains name do
      throwError "CHC export: undeclared SMT symbol '{name}'"
  | .forallT name sort body =>
    unless (toString sort == "Int" || toString sort == "Bool") && !symbols.contains name do
      throwError "CHC export: invalid or shadowed SMT binder '{name}'"
    checkTerm body (symbols.push name)
  | .appT .. =>
    let (head, args) := application term
    let .symbolT name := head | throwError "CHC export: higher-order SMT application"
    if !symbols.contains name then
      let valid := match name with
        | "not" => args.size == 1
        | "-" => args.size == 1 || args.size == 2
        | "ite" => args.size == 3
        | "and" | "or" | "xor" | "=>" | "=" | "distinct" | "+" | "*" | "<" | "<=" | ">" | ">=" => args.size == 2
        | _ => false
      unless valid do throwError "CHC export: unsupported SMT operator '{name}' or arity"
      if name == "*" && !args.any numeral then
        throwError "CHC export: nonlinear multiplication; one operand must be an integer literal"
    for argument in args do checkTerm argument symbols
  | _ => throwError "CHC export: unsupported SMT term {term}"

end Flex.CHC.Fragment
