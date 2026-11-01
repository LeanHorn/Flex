import Lean
import Smt.Recognizers

namespace Flex.PA.Observation

open Lean Meta

structure Config where
  maxTermsPerClause : Nat := 512
  maxCongruencePairs : Nat := 4096

private def scalar (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return type.isConstOf ``Int || type.isConstOf ``Bool || type.isProp

private def conj (xs : Array Expr) : Expr :=
  xs.foldr (fun p q => if q.isConstOf ``True then p else mkApp2 (mkConst ``And) p q)
    (mkConst ``True)

private def implication (p q : Expr) : Expr := .forallE .anonymous p q .default

private def builtin (e : Expr) : Bool := Id.run do
  let name := e.getAppFn.constName?.getD .anonymous
  if #[``HDiv.hDiv, ``HMod.hMod, ``Int.ediv, ``Int.emod].contains name then
    return e.getAppArgs.back?.any fun divisor =>
      (divisor.natLitOf? (mkConst ``Int)).any (· > 0)
  return #[``And, ``Or, ``Not, ``Iff, ``Eq, ``ite, ``dite,
    ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt,
    ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod,
    ``Neg.neg, ``OfNat.ofNat, ``Int.add, ``Int.sub, ``Int.mul, ``Int.neg,
    ``Int.ediv, ``Int.emod, ``Int.le, ``Int.lt,
    ``Bool.and, ``Bool.or, ``Bool.not, ``Bool.xor].contains
      (e.getAppFn.constName?.getD .anonymous)

private def literal (e : Expr) : Bool :=
  e.isConstOf ``True || e.isConstOf ``False || e.isConstOf ``Bool.true ||
  e.isConstOf ``Bool.false || (e.natLitOf? (mkConst ``Int)).isSome

private def expose (raw : Expr) : MetaM Expr := do
  let e := raw.consumeMData.headBeta
  if let .letE _ _ value body _ := e then return body.instantiate1 value
  -- Typeclass projections such as LE.le must retain their arithmetic syntax.
  if builtin e || #[``HDiv.hDiv, ``HMod.hMod, ``Int.ediv, ``Int.emod].contains
      (e.getAppFn.constName?.getD .anonymous) then return e
  let e ← if e.isProj then whnf e else
    if let .const name _ := e.getAppFn then
      if (← getEnv).getProjectionFnInfo? name |>.isSome then whnf e else pure e
    else pure e
  if e.isAppOfArity ``Int.ofNat 1 then
    if let .lit (.natVal n) := e.getArg! 0 then return ← mkNumeral (mkConst ``Int) n
  if e.isAppOfArity ``Int.negSucc 1 then
    if let .lit (.natVal n) := e.getArg! 0 then
      return ← mkAppM ``Neg.neg #[← mkNumeral (mkConst ``Int) (n + 1)]
  return e

private structure Variable where
  value : Expr
  type : Expr

private structure ClauseState where
  variables : Array Variable := #[]
  names : Std.HashMap Expr Expr := {}
  cache : Std.HashMap Expr Expr := {}
  applications : Array Expr := #[]

private abbrev ClauseM := StateT ClauseState MetaM

private def fresh (original type : Expr) (cfg : Config) : ClauseM Expr := do
  if let some value := (← get).names[original]? then return value
  if (← get).variables.size >= cfg.maxTermsPerClause then
    throwError "PA observation: variable limit ({cfg.maxTermsPerClause}) exceeded in a clause"
  let value := mkFVar (← mkFreshFVarId)
  modify fun s => { s with
    variables := s.variables.push { value, type }
    names := s.names.insert original value }
  return value

/-- Integer labels represent equality classes of the finitely observed opaque values.
Only validity of the resulting query is used by predicate abstraction. -/
private def opaqueEquality (a b : Expr) (cfg : Config) : ClauseM Expr := do
  if a == b then return mkConst ``True
  return mkApp3 (mkConst ``Eq [.succ .zero]) (mkConst ``Int)
    (← fresh a (mkConst ``Int) cfg) (← fresh b (mkConst ``Int) cfg)

private def addApplication (e : Expr) : ClauseM Unit := do
  if e.isApp && !(← get).applications.contains e then
    modify fun s => { s with applications := s.applications.push e }

private def structureEquality? (type a b : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  let .const name _ := type.getAppFn | return none
  let some info := getStructureInfo? (← getEnv) name | return none
  let mut fields := #[]
  for field in info.fieldInfo do
    let left ← mkAppM field.projFn #[a]
    let right ← mkAppM field.projFn #[b]
    unless ← isDefEq (← inferType left) (← inferType right) do return none
    fields := fields.push (← mkEq (← expose left) (← expose right))
  return some (conj fields)

private def constructorEquality? (a b : Expr) : MetaM (Option Expr) := do
  let .const name _ := a.getAppFn | return none
  unless b.getAppFn == a.getAppFn do return none
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  let aa := a.getAppArgs
  let bb := b.getAppArgs
  unless aa.size == bb.size && aa.size == info.numParams + info.numFields do return none
  let mut fields := #[]
  for i in [info.numParams:aa.size] do
    unless ← isDefEq (← inferType aa[i]!) (← inferType bb[i]!) do return none
    fields := fields.push (← mkEq aa[i]! bb[i]!)
  return some (conj fields)

private partial def abstractTerm (raw : Expr) (cfg : Config)
    : ClauseM Expr := do
  let e ← expose raw
  if let some value := (← get).cache[e]? then return value
  let result ← do
    if literal e then return e
    if e.getAppFn.isMVar then throwError "PA observation: unresolved metavariable"
    if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
      let type := e.getArg! 0
      unless ← scalar type do
        throwError "PA observation: unsupported conditional result type {type}"
      let condition ← abstractTerm (e.getArg! 1) cfg
      let branch (value : Expr) : ClauseM Expr := do
        if e.isAppOfArity ``dite 5 then
          let .lam _ _ body _ := value.headBeta
            | throwError "PA observation: expected a conditional branch lambda"
          if body.hasLooseBVar 0 then
            throwError "PA observation: proof-dependent conditional branches are unsupported"
          abstractTerm (body.instantiate1 (mkConst ``True.intro)) cfg
        else abstractTerm value cfg
      let yes ← branch (e.getArg! 3)
      let no ← branch (e.getArg! 4)
      return mkApp5 (mkConst ``ite e.getAppFn.constLevels!) type condition
        (mkApp (mkConst ``Classical.propDecidable) condition) yes no
    if e.isAppOfArity ``Iff 2 then
      return mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero)
        (← abstractTerm (e.getArg! 0) cfg)
        (← abstractTerm (e.getArg! 1) cfg)
    if let some (type, a, b) := e.eq? then
      if let some fields ← structureEquality? type a b then
        return ← abstractTerm fields cfg
      if let some fields ← constructorEquality? a b then
        return ← abstractTerm fields cfg
      if ← scalar type then
        return mkApp3 e.getAppFn type (← abstractTerm a cfg) (← abstractTerm b cfg)
      return ← opaqueEquality a b cfg
    if let .forallE _ domain body _ := e then
      if (← isProp domain) && !body.hasLooseBVar 0 then
        return implication (← abstractTerm domain cfg)
          (← abstractTerm (body.instantiate1 (mkConst ``True.intro)) cfg)
      -- Quantified semantic properties are single observations; no binder escapes.
      unless ← isProp e do throwError "PA observation: unsupported function-valued observation"
      return ← fresh e (mkSort .zero) cfg
    if builtin e then
      let mut args := #[]
      for arg in e.getAppArgs do
        let type ← inferType arg
        let arg ← if ← scalar type then abstractTerm arg cfg else pure arg
        args := args.push arg
      return mkAppN e.getAppFn args
    let type ← inferType e
    unless ← scalar type do throwError "PA observation: unsupported observation result {type}"
    addApplication e
    fresh e type cfg
  modify fun s => { s with cache := s.cache.insert e result }
  return result

private def observedEquality (a b : Expr) (cfg : Config)
    : ClauseM Expr := do
  if a == b then return mkConst ``True
  let ta ← inferType a
  unless ← isDefEq ta (← inferType b) do
    throwError "PA observation: equality between observations of different types"
  if ← scalar ta then
    let lhs ← abstractTerm a cfg
    let rhs ← abstractTerm b cfg
    return mkApp3 (mkConst ``Eq [← getLevel ta]) ta lhs rhs
  opaqueEquality a b cfg

/-- Finite congruence keeps frame equalities conditional on learned observations. -/
private def congruence (cfg : Config) : ClauseM (Array Expr) := do
  let mut facts := #[]
  let mut visited : Std.HashSet (Expr × Expr) := {}
  let mut cursor := 0
  while cursor < (← get).applications.size do
    let left := (← get).applications[cursor]!
    cursor := cursor + 1
    let applications := (← get).applications
    for right in applications do
      if left == right then continue
      let lf := left.getAppFn
      let rf := right.getAppFn
      if lf != rf && !(lf.isFVar && rf.isFVar) then continue
      if lf != rf then
        unless ← isDefEq (← inferType lf) (← inferType rf) do continue
      if visited.contains (left, right) || visited.contains (right, left) then continue
      if visited.size >= cfg.maxCongruencePairs then
        throwError "PA observation: congruence limit ({cfg.maxCongruencePairs}) exceeded"
      visited := visited.insert (left, right)
      let aa := left.getAppArgs
      let bb := right.getAppArgs
      unless aa.size == bb.size do continue
      let mut premises := #[]
      if lf != rf then premises := premises.push (← observedEquality lf rf cfg)
      let mut compatible := true
      for a in aa, b in bb do
        if a == b then continue
        let type ← inferType a
        -- Type/instance arguments must agree; they are not runtime values.
        if (type.isSort && !type.isProp) || (← isProp type) then
          unless ← isDefEq a b do
            compatible := false
            break
        else premises := premises.push (← observedEquality a b cfg)
      unless compatible do continue
      let conclusion ← observedEquality left right cfg
      facts := facts.push (implication (conj premises) conclusion)
  return facts

/-- Share observations and congruence across related validity queries.
Validity of the abstraction is sufficient; satisfiability need not transfer back. -/
def projectQueries (assumptions conclusions : Array Expr) (cfg : Config := {})
    : MetaM (Array Expr) := do
  let (queries, state) ← (do
    let assumptions ← assumptions.mapM (abstractTerm · cfg)
    let conclusions ← conclusions.mapM (abstractTerm · cfg)
    let facts ← congruence cfg
    return conclusions.map (implication (conj (facts ++ assumptions)) ·)).run {}
  queries.mapM fun query => do
    let mut result := query
    for entry in state.variables.reverse do
      result := .forallE `observation entry.type (result.abstract #[entry.value]) .default
    if result.hasFVar || result.hasMVar || result.hasLooseBVars then
      throwError "PA observation: unresolved observation in validity query"
    check result
    return result

end Flex.PA.Observation
