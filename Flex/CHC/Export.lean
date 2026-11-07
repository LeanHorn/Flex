import Flex.Fusion.Flatten
import Smt.Translate.Int
import Smt.Translate.Bool
import Smt.Translate.Prop
import Smt.Translate.Query
import Smt2Lean.Chc
import Qq

namespace Flex.CHC

open Lean Meta Qq

/-- Restore Meta/Core state after a speculative operation. -/
def restoreMetaState (saved : Meta.SavedState) : MetaM Unit := do
  set saved.meta
  modifyThe Core.State fun _ => saved.core.toState

/-- Integer and Boolean value sorts. -/
inductive ValueSort where
  | int | bool
  deriving BEq, Repr, Inhabited

/-- Map solver symbols to Lean witness slots, retaining unused arguments and Bool/Prop types. -/
structure Relation where
  symbol : String
  kvar : KVar
  leanType : Lean.Expr
  argumentSorts : Array ValueSort
  deriving Inhabited

/-- Checked assertions ending in `check-sat`, with metadata for model reconstruction. -/
structure ExportedProblem where
  relations : Array Relation
  commands : List Smt.Translate.Command
  clauseCount : Nat
  /-- Alternate SMT presentation; the Lean clauses and relation slots are unchanged. -/
  canonicalClauses : Bool := false
  deriving Inhabited

private partial def flattenBool : Sexp → Sexp
  | .atom text => .atom text
  | .expr items =>
    let items := items.map flattenBool
    match items with
    | .atom op :: args =>
      if op == "and" || op == "or" then
        .expr (.atom op :: args.flatMap fun arg => match arg with
          | .expr (.atom nested :: children) => if nested == op then children else [arg]
          | _ => [arg])
      else .expr items
    | _ => .expr items

/-- `p → q → r` becomes `(p ∧ q) → r`; only Boolean associations change. -/
private def canonicalClause (body : Sexp) : Sexp := go body []
where
  go : Sexp → List Sexp → Sexp
    | .expr [.atom "=>", guard, rest], guards => go rest (guard :: guards)
    | head, guards =>
      let body := match guards.reverse with
        | [] => .atom "true"
        | [guard] => guard
        | guards => .expr (.atom "and" :: guards)
      .expr [.atom "=>", flattenBool body, flattenBool head]

/-- Group universal binders: Spacer rejects some nested Bool/Int prefixes. -/
private def clauseSexp (canonical : Bool) (term : Smt.Term) : Sexp :=
  go term []
where
  bodySexp (body : Smt.Term) : Sexp :=
    let body := ToSexp.toSexp body
    if canonical then canonicalClause body else body
  go : Smt.Term → List Sexp → Sexp
    | .forallT name sort body, binders =>
      go body (.expr [.atom (Smt.Term.quoteSymbol name), ToSexp.toSexp sort] :: binders)
    | body, [] => bodySexp body
    | body, binders => .expr [.atom "forall", .expr binders.reverse, bodySexp body]

private def commandSexp (canonical : Bool) : Smt.Translate.Command → Sexp
  | .assert term => .expr [.atom "assert", clauseSexp canonical term]
  | command => ToSexp.toSexp command

/-- Serialize the script with grouped universal binders. -/
def ExportedProblem.toSMTLib (problem : ExportedProblem) : String :=
  Sexp.serializeMany (problem.commands.map (commandSexp problem.canonicalClauses)) ++ "\n"

namespace Fragment

/-- Accept Int, Bool, and Prop values. -/
def valueSort (type : Expr) : MetaM ValueSort := do
  let type ← whnf type
  if type.isConstOf ``Int then return .int
  if type.isConstOf ``Bool || type.isProp then return .bool
  throwError "CHC export: unsupported value type {type}; expected Int, Bool, or Prop"

/-- Use only the supported lean-smt translators; restore the environment afterwards. -/
def withTranslators (action : MetaM α) (allowQuantifiers : Bool := false) : MetaM α := withoutModifyingEnv do
  let extension := Smt.Attribute.smtExt
  modifyEnv fun env => extension.modifyState env fun state =>
    let translators : Std.HashSet Name := {
      ``Smt.Translate.Int.translateType, ``Smt.Translate.Int.translateInt,
      ``Smt.Translate.Int.translateProp, ``Smt.Translate.Bool.translateType,
      ``Smt.Translate.Bool.translateBool, ``Smt.Translate.Bool.translateProp,
      ``Smt.Translate.Prop.translateType, ``Smt.Translate.Prop.translateProp,
      ``Smt.Translate.Prop.translateIte }
    state.insert ``Smt.Translator (if allowQuantifiers then
      translators.insert ``Smt.Translate.Prop.translateExists else translators)
  action

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

private def positiveNumeral : Smt.Term → Bool
  | .literalT text => text.toNat?.any (· > 0)
  | _ => false

/-- Check supported operators and arities; the native parser subsequently checks sorts. -/
partial def checkTerm (term : Smt.Term) (symbols : Array String)
    (allowQuantifiers : Bool := false) (sorts : Array String := #[]) : MetaM Unit := do
  match term with
  | .literalT _ =>
    unless numeral term do throwError "CHC export: unsupported SMT literal {term}"
  | .symbolT name =>
    unless symbols.contains name || #["true", "false"].contains name do
      throwError "CHC export: undeclared SMT symbol '{name}'"
  | .forallT name sort body | .existsT name sort body =>
    if !allowQuantifiers then
      if let .existsT .. := term then throwError "CHC export: existential SMT terms are unsupported"
    unless (toString sort == "Int" || toString sort == "Bool" || sorts.contains (toString sort))
        && !symbols.contains name do
      throwError "CHC export: invalid or shadowed SMT binder '{name}'"
    checkTerm body (symbols.push name) allowQuantifiers sorts
  | .letT name value body =>
    unless allowQuantifiers do throwError "CHC export: SMT let bindings are unsupported"
    if symbols.contains name then throwError "CHC export: shadowed SMT let binder '{name}'"
    checkTerm value symbols allowQuantifiers sorts
    checkTerm body (symbols.push name) allowQuantifiers sorts
  | .appT .. =>
    let (head, args) := application term
    let .symbolT name := head | throwError "CHC export: higher-order SMT application"
    if !symbols.contains name then
      let valid := match name with
        | "not" => args.size == 1
        | "-" => args.size == 1 || args.size == 2
        | "ite" => args.size == 3
        | "and" | "or" | "xor" | "=>" | "=" | "distinct" | "+" | "*" | "div" | "mod"
        | "<" | "<=" | ">" | ">=" => args.size == 2
        | _ => false
      unless valid do throwError "CHC export: unsupported SMT operator '{name}' or arity"
      if (name == "div" || name == "mod") && !positiveNumeral args[1]! then
        throwError "CHC export: {name} requires a positive integer literal divisor"
    for argument in args do checkTerm argument symbols allowQuantifiers sorts
  | _ => throwError "CHC export: unsupported SMT term {term}"

end Fragment

namespace Prepare

/-- Existential symbol roles are determined by their Lean types. -/
private inductive WitnessKind where
  | predicate | carrier | constant | function | theoryParameter

private def witnessKind (type : Expr) : MetaM WitnessKind := do
  let type ← whnf type
  if type.isProp then return .predicate
  if type.isSort then return .carrier
  for id in (collectFVars {} type).fvarIds do
    let dependency ← whnf (← inferType (mkFVar id))
    if dependency.isSort && !dependency.isProp then return .theoryParameter
  forallTelescopeReducing type fun parameters result => do
    if result.isProp then return .predicate
    return if parameters.isEmpty then .constant else .function

private def checkPredicateType (name : Name) (type : Expr) : MetaM Unit := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelMVar then
    throwError "CHC preparation: predicate '{name}' has an open or unresolved signature"
  forallTelescopeReducing type fun parameters _ =>
    for parameter in parameters, i in [:parameters.size] do
      let domain ← inferType parameter
      if domain.hasFVar then
        throwError "CHC preparation: predicate '{name}' has a dependent argument {i + 1}"
      try discard <| Fragment.valueSort domain
      catch error =>
        if error.isInterrupt then throw error
        throwError "CHC preparation: predicate '{name}' argument {i + 1} has unsupported type {domain}; expected Int, Bool, or Prop"

/-- Validate the existential prefix before creating predicate witness slots. -/
partial def checkPredicatePrefix (input : Expr) : MetaM Unit := do
  let input ← whnf input
  unless input.isAppOfArity ``Exists 2 do return
  let type := input.getArg! 0
  let predicate ← whnf (input.getArg! 1)
  let .lam name _ body bi := predicate
    | throwError "CHC preparation: expected a lambda in an existential binder"
  match ← witnessKind type with
  | .predicate => checkPredicateType name type
  | .carrier =>
    throwError "CHC preparation: unsupported theory wrapper: existential carrier '{name}' : {type}; array and other abstract theory models require an interpretation before predicate synthesis"
  | .theoryParameter =>
    throwError "CHC preparation: unsupported theory-model parameter '{name}' : {type}; its type depends on an abstract carrier"
  | .constant =>
    throwError "CHC preparation: unsupported existential background constant '{name}' : {type}; only Prop-valued predicates can be synthesized"
  | .function =>
    throwError "CHC preparation: unsupported existential background function '{name}' : {type}; only Prop-valued predicates can be synthesized"
  withLocalDecl name bi type fun parameter =>
    checkPredicatePrefix (body.instantiate1 parameter)

/-- Expose named propositions and beta/let wrappers, preserving arithmetic operators. -/
partial def expose (expression : Expr) : MetaM Expr := do
  let expression := expression.consumeMData.headBeta
  match expression with
  | .letE _ _ value body _ => expose (body.instantiate1 value)
  | .const .. =>
    let type ← whnf (← inferType expression)
    if (← isProp expression) || type.isConstOf ``Int || type.isConstOf ``Bool then
      if let some value ← unfoldDefinition? expression then return ← expose value
    return expression
  | _ => return expression

private def canonical (original expected : Expr) : MetaM Unit := do
  unless ← isDefEq original expected do
    throwError "CHC export: nonstandard operator instance in {original}"

/-- Check standard instances before lean-smt erases their typeclass arguments. -/
private def checkIntegerInstance (e : Expr) : MetaM Unit := do
  let int := mkConst ``Int
  if let some n := e.natLitOf? int then
    canonical e (mkIntLit n)
  else if let some a := e.negOf? int then
    let a : Q(Int) := a
    canonical e q(-$a)
  else
    let operators := #[e.hAddOf? int int, e.hSubOf? int int, e.hMulOf? int int,
      e.hDivOf? int int, e.hModOf? int int,
      e.leOf? int, e.ltOf? int, e.geOf? int, e.gtOf? int]
    for arguments in operators, i in [:operators.size] do
      if let some (a, b) := arguments then
        let a : Q(Int) := a
        let b : Q(Int) := b
        let expected := #[q($a + $b), q($a - $b), q($a * $b), q($a / $b), q($a % $b),
          q($a ≤ $b), q($a < $b), q($a ≥ $b), q($a > $b)][i]!
        canonical e expected

/-- Smt2Lean keeps n-ary distinct as a transparent, namespaced operator helper.
Unfold its actual definition rather than assigning semantics from the name. -/
private def unfoldDistinct? (e : Expr) : MetaM (Option Expr) := do
  let .const (.str (.str _ "SMT") suffix) _ := e.getAppFn | return none
  unless suffix.startsWith "distinct" do return none
  let some arity := (suffix.drop 8).toString.toNat? | return none
  unless arity >= 2 && e.getAppNumArgs == arity + 1 && (← isProp e) do return none
  unfoldDefinition? e

private def recordEquality? (e : Expr) : MetaM (Option Expr) := do
  let some (type, left, right) := e.eq? | return none
  let type ← whnf type
  let .const name _ := type.getAppFn | return none
  let some ctor := getNonRecStructureCtor? (← getEnv) name | return none
  let arity := ctor.numParams + ctor.numFields
  unless left.isAppOfArity ctor.name arity && right.isAppOfArity ctor.name arity do
    return none
  let mut result := mkConst ``True
  for a in left.getAppArgs[ctor.numParams:], b in right.getAppArgs[ctor.numParams:] do
    unless ← isDefEq (← inferType a) (← inferType b) do return none
    let eq ← mkEq a b
    result := if result.isConstOf ``True then eq else mkApp2 (mkConst ``And) result eq
  return some result

/-- Evaluate closed Nat comparisons without identifying Nat subtraction with Int subtraction. -/
private def closedNatComparison? (e : Expr) : MetaM (Option Expr) := do
  let nat := mkConst ``Nat
  let eq := match e.eq? with | some (type, a, b) => if type == nat then some (a, b) else none | _ => none
  let ne := match e.ne? with | some (type, a, b) => if type == nat then some (a, b) else none | _ => none
  let operators := #[e.leOf? nat, e.ltOf? nat, e.geOf? nat, e.gtOf? nat, eq, ne]
  for arguments in operators, i in [:operators.size] do
    if let some (a, b) := arguments then
      let a : Q(Nat) := a
      let b : Q(Nat) := b
      canonical e (#[q($a ≤ $b), q($a < $b), q($a ≥ $b), q($a > $b), q($a = $b), q($a ≠ $b)][i]!)
      let some n ← evalNat a | return none
      let some m ← evalNat b | return none
      let truth := #[decide (n ≤ m), decide (n < m), decide (n ≥ m), decide (n > m), n == m, n != m][i]!
      return some (mkConst (if truth then ``True else ``False))
  return none

/-- Expose scalar computations over records before the SMT translator visits their fields. -/
private def unfoldRecordCall? (e : Expr) : MetaM (Option Expr) := do
  let .const name _ := e.getAppFn | return none
  let env ← getEnv
  unless env.find? name matches some (.defnInfo _) do return none
  let type ← whnf (← inferType e)
  unless type.isProp || type.isConstOf ``Int || type.isConstOf ``Bool do return none
  for arg in e.getAppArgs do
    let type ← whnf (← inferType arg)
    if let .const recordName _ := type.getAppFn then
      if !isClass env recordName && (getNonRecStructureCtor? env recordName).isSome then
        if ← isRecursiveDefinition name then return none
        return ← unfoldDefinition? e
  return none

/-- Unfold a matcher application to its `casesOn` implementation. (`unfoldDefinition?`
declines matchers.) -/
def unfoldMatcher? (e : Expr) : MetaM (Option Expr) := do
  let .const name levels := e.getAppFn | return none
  let some info ← getMatcherInfo? name | return none
  if e.getAppNumArgs < info.arity then return none
  let some constant@(.defnInfo _) := (← getEnv).find? name | return none
  return some ((← instantiateValueLevelParams constant levels).beta e.getAppArgs)

/-- PA datatype encoding: matchers unfold to `casesOn`, whose alternatives are normalized
under their field binders. The motive and parameters are left untouched. -/
private partial def casesOnAtom? (e : Expr) (atom : Expr → MetaM Expr) : MetaM (Option Expr) := do
  let .const name _ := e.getAppFn | return none
  let env ← getEnv
  if (← getMatcherInfo? name).isSome then
    let some unfolded ← unfoldMatcher? e | return none
    return some (← atom unfolded)
  unless isCasesOnRecursor env name do return none
  let some (.inductInfo info) := env.find? name.getPrefix | return none
  let major := info.numParams + 1 + info.numIndices
  let minors := major + 1 + info.ctors.length
  let args := e.getAppArgs
  if args.size < minors then return none
  let args ← args.mapIdxM fun i arg => do
    if i < major then return arg
    if i == major || i ≥ minors then return ← atom arg
    lambdaTelescope arg fun fields body => do mkLambdaFVars fields (← atom body)
  return some (mkAppN e.getAppFn args)

/-- Normalize checked theory terms. PA can also enable first-order Int/Bool/Prop
quantifiers; CHC export keeps them restricted to clause prefixes. -/
partial def atom (input : Expr) (allowQuantifiers : Bool := false) : MetaM Expr := do
  let e ← expose input
  if e.isAppOfArity ``Iff 2 then
    return ← mkEq (← atom (e.getArg! 0) allowQuantifiers)
      (← atom (e.getArg! 1) allowQuantifiers)
  if e.isAppOfArity ``Decidable.decide 2 then
    return ← atom (← mkAppOptM ``ite #[some (mkConst ``Bool), some (e.getArg! 0),
      some (e.getArg! 1), some (mkConst ``Bool.true), some (mkConst ``Bool.false)])
      allowQuantifiers
  if let some body ← unfoldDistinct? e then return ← atom body allowQuantifiers
  if let some body ← recordEquality? e then return ← atom body allowQuantifiers
  if let some body ← closedNatComparison? e then return body
  -- lean-smt recognizes the notation's typeclass applications, not these direct functions.
  let e ← if e.isAppOfArity ``Int.ediv 2 || e.isAppOfArity ``Int.emod 2 then do
      let a : Q(Int) := e.getArg! 0
      let b : Q(Int) := e.getArg! 1
      pure (if e.isAppOfArity ``Int.ediv 2 then q($a / $b) else q($a % $b))
    else pure e
  checkIntegerInstance e
  if e.beq?.isSome || e.bne?.isSome then
    throwError "CHC export: BEq comparisons are unsupported; use propositional equality"
  match e with
  | .forallE name domain body bi =>
    if !(← isProp domain) && allowQuantifiers then
      -- PA binder sorts (Int, Bool, or batch datatypes) are checked after translation.
      let name ← mkFreshUserName `_pa_quant
      return ← withLocalDecl name bi domain fun input => do
        -- lean-smt treats unused forall binders as function arrows. These sorts
        -- are inhabited, so dropping an unused value binder is equivalent.
        mkForallFVars #[input] (← atom (body.instantiate1 input) true) (usedOnly := true)
    unless (← isProp domain) && !body.hasLooseBVar 0 do
      throwError "CHC export: quantifiers must be clause binders; proof-dependent guards are unsupported"
    let domain' ← atom domain allowQuantifiers
    withLocalDecl name bi domain fun proof => do
      mkArrow domain' (← atom (body.instantiate1 proof) allowQuantifiers)
  | .lam .. =>
    throwError "CHC export: quantifiers must be clause binders; higher-order terms are unsupported"
  | .app .. =>
    if allowQuantifiers && e.isAppOfArity ``Exists 2 then
      let domain := e.getArg! 0
      let predicate ← whnf (e.getArg! 1)
      let name ← mkFreshUserName `_pa_quant
      return ← withLocalDeclD name domain fun input => do
        let body ← atom (mkApp predicate input).headBeta true
        return mkApp2 e.getAppFn domain (← mkLambdaFVars #[input] body)
    let head := e.getAppFn
    if allowQuantifiers then
      if let some body ← casesOnAtom? e (atom · true) then return body
    let args ← e.getAppArgs.mapM fun arg => atom arg allowQuantifiers
    let applied := mkAppN head args
    let env ← getEnv
    if let some projected ← reduceProjOf? applied (fun name => !isClass env name) then
      unless projected == applied do return ← atom projected allowQuantifiers
    if let .const name _ := head then
      if let some info := env.getProjectionFnInfo? name then
        if !info.fromClass && args.size == info.numParams + 1 then
          if let some projected ← unfoldDefinition? applied then
            return ← atom projected allowQuantifiers
    if let some body ← unfoldRecordCall? applied then return ← atom body allowQuantifiers
    return applied
  | .proj name index value =>
    if let some projected ← reduceProj? e then return ← atom projected allowQuantifiers
    if value.isAppOfArity ``ite 5 then
      let yes := Expr.proj name index (value.getArg! 3)
      let no := Expr.proj name index (value.getArg! 4)
      let type ← inferType e
      if (← isDefEq type (← inferType yes)) && (← isDefEq type (← inferType no)) then
        return ← atom (← mkAppOptM ``ite #[some type, some (value.getArg! 1),
          some (value.getArg! 2), some yes, some no]) allowQuantifiers
    return e
  | .mvar .. => throwError "CHC export: unresolved metavariable {e}"
  | _ => return e

/-- Quantifying a nonrecursive record is equivalent to quantifying its constructor fields. -/
private def recordBinder? (domain body : Expr) : MetaM (Option Expr) := do
  let domain ← whnf domain
  let .const name levels := domain.getAppFn | return none
  let some ctor := getNonRecStructureCtor? (← getEnv) name | return none
  let constructor := mkAppN (mkConst ctor.name levels) domain.getAppArgs
  forallTelescopeReducing (← inferType constructor) fun fields result => do
    unless ← isDefEq result domain do return none
    return some (← mkForallFVars fields (body.instantiate1 (mkAppN constructor fields)))

/-- Move value binders before guards and expose nonrecursive record binders. -/
partial def clause (input : Expr) : MetaM Expr :=
  go input #[] #[]
where
  go (input : Expr) (variables guards : Array Expr) : MetaM Expr := do
    let e ← expose input
    if let .forallE _ domain body _ := e then
      if ← isProp domain then
        if body.hasLooseBVar 0 then
          throwError "CHC export: constraints depending on proof terms are unsupported"
        let guard ← atom domain
        withLocalDeclD `guard domain fun proof =>
          go (body.instantiate1 proof) variables (guards.push guard)
      else
        if let some expanded ← recordBinder? domain body then
          return ← go expanded variables guards
        discard <| Fragment.valueSort domain
        withLocalDeclD (Name.mkSimple s!"v_{variables.size}") domain fun binder =>
          go (body.instantiate1 binder) (variables.push binder) guards
    else
      let mut result ← atom e
      for guard in guards.reverse do result ← mkArrow guard result
      mkForallFVars variables result (usedOnly := true)

end Prepare

private def relation (kvar : KVar) (index : Nat) : MetaM Relation := do
  if ← kvar.mvarId.isAssigned then
    throwError "CHC export: predicate '{kvar.name}' is already assigned"
  let type ← instantiateMVars (← kvar.mvarId.getType)
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelMVar then
    throwError "CHC export: predicate '{kvar.name}' has an open or unresolved signature"
  let sorts ← forallTelescopeReducing type fun parameters result => do
    unless result.isProp do
      throwError "CHC export: predicate '{kvar.name}' must return Prop"
    unless parameters.size == kvar.paramTypes.length && parameters.size == kvar.params.length do
      throwError "CHC export: parameter metadata disagrees with predicate '{kvar.name}'"
    parameters.mapIdxM fun i parameter => do
      let parameterType ← inferType parameter
      if parameterType.hasFVar then
        throwError "CHC export: dependent predicate parameters are unsupported"
      unless ← isDefEq parameterType kvar.paramTypes[i]! do
        throwError "CHC export: parameter {i + 1} has inconsistent metadata for '{kvar.name}'"
      Fragment.valueSort parameterType
  return { symbol := s!"k_{index}", kvar, leanType := type, argumentSorts := sorts }

private def validate (problem : ExportedProblem) : MetaM Unit := do
  (Smt2Lean.Chc.parseAndInspectProblem problem.toSMTLib (name := "flex-chc") fun parsed => do
    unless parsed.constants.isEmpty && parsed.functions.isEmpty &&
        parsed.relations.size == problem.relations.size && parsed.clauses.size == problem.clauseCount do
      throw (.error "CHC export: unexpected declarations or clause count after validation")
    for expected in problem.relations do
      let some actual := parsed.relations.find? (·.name == expected.symbol)
        | throw (.error s!"CHC export: missing relation '{expected.symbol}'")
      unless actual.argumentSorts.size == expected.argumentSorts.size do
        throw (.error s!"CHC export: wrong arity for '{expected.symbol}'")
      for actualSort in actual.argumentSorts, expectedSort in expected.argumentSorts do
        unless (match expectedSort with | .int => actualSort.isInteger | .bool => actualSort.isBoolean) do
          throw (.error s!"CHC export: wrong argument sort for '{expected.symbol}'")
  ).runIO

/-- Check an equivalent Horn presentation before a solver retry. -/
def ExportedProblem.withCanonicalClauses (problem : ExportedProblem) : MetaM ExportedProblem := do
  let problem := { problem with canonicalClauses := true }
  validate problem
  return problem

/-- Expand unsupported nonrecursive definitions, keeping recognized SMT operators intact. -/
private partial def translateClause (input : Expr) (names : Std.HashMap FVarId String)
    (symbols : Array String) : MetaM Smt.Term := do
  let clause ← Prepare.clause input
  let ((term, constants, freeVariables), _) ← (Smt.Translator.translateExpr clause).run {
    uniqueFVarNames := names }
  unless constants.isEmpty do
    let changed ← IO.mkRef false
    let expanded ← Meta.transform (m := MetaM) clause (pre := fun e => do
      let .const name _ := e.getAppFn | return .continue
      unless constants.contains name do return .continue
      unless (← getEnv).find? name matches some (.defnInfo _) do return .continue
      if ← isRecursiveDefinition name then return .continue
      if let some body ← unfoldDefinition? e then
        unless body == e do
          changed.set true
          return .visit body
      return .continue)
    unless ← changed.get do
      throwError "unsupported constant dependencies: {constants.toArray}"
    return ← translateClause expanded names symbols
  unless freeVariables.toArray.all names.contains do
    throwError "unexpected free variable in translation"
  Fragment.checkTerm term symbols
  return term

/-- Export Bool/Int arithmetic, positive-literal div/mod, and local lets.
The body must be closed except for its unassigned κs. No witnesses are assigned. -/
def exportConstraints (kvars : List KVar) (body : Expr) : MetaM ExportedProblem := do
  let saved ← Meta.saveState
  try
    Fragment.withTranslators do
      let mut seen : Std.HashSet MVarId := {}
      for kvar in kvars do
        if seen.contains kvar.mvarId then throwError "CHC export: duplicate κ identity '{kvar.name}'"
        seen := seen.insert kvar.mvarId
      let relations ← kvars.toArray.mapIdxM fun i kvar => relation kvar i
      let body ← instantiateMVars body
      if body.hasFVar then
        throwError "CHC export: free local variables in the body; bind parameters and guards explicitly"
      if body.hasLooseBVars then throwError "CHC export: loose bound variable in the body"
      unless ← isProp body do throwError "CHC export: expected a proposition"
      let context : KContext := { kvars := kvars.foldl (fun ctx k => ctx.insert k.mvarId k) {} }
      let clauses ← (exprFlat body Prepare.expose).run context
      withLocalDeclsDND (relations.map fun r => (.mkSimple r.symbol, r.leanType)) fun symbols => do
        let replacements := (relations.zip symbols).foldl
          (fun map (r, symbol) => map.insert r.kvar.mvarId symbol) ({} : Std.HashMap MVarId Expr)
        let names := (relations.zip symbols).foldl
          (fun map (r, symbol) => map.insert symbol.fvarId! r.symbol) ({} : Std.HashMap FVarId String)
        -- Translate each clause once; retain the checked terms for the final script.
        let assertions ← clauses.toArray.mapIdxM fun i original => do
          try
            let input := original.replace fun e => if e.isMVar then replacements[e.mvarId!]? else none
            if input.hasMVar then throwError "unregistered or unresolved metavariable"
            let term ← translateClause input names (relations.map (·.symbol))
            return Smt.Translate.Command.assert term
          catch error => throwError "CHC export: clause {i + 1}: {error.toMessageData}"
        let declarations ← Smt.Translate.Query.generateQuery symbols.toList names
        let problem : ExportedProblem := {
          relations
          commands := [.setLogic "HORN"] ++ declarations ++ assertions.toList ++ [.checkSat]
          clauseCount := assertions.size }
        validate problem
        return problem
  finally restoreMetaState saved

end Flex.CHC
