import Flex.CHC.Export

namespace Flex.CHC.Projection

open Lean Meta

initialize registerTraceClass `flex.chc.projection

structure Config where
  maxFeatures : Nat := 96
  maxTermsPerClause : Nat := 512
  maxCongruencePairs : Nat := 4096
  maxClauses : Nat := 1024

/-- Closed observations over the complete original predicate argument list. -/
structure Mapping where
  original : KVar
  projected : KVar
  arguments : Array Expr

structure ProjectedGoal where
  kvars : List KVar
  body : Expr
  mappings : Array Mapping

private def scalar (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return type.isConstOf ``Int || type.isConstOf ``Bool || type.isProp

private def conj (xs : Array Expr) : Expr :=
  xs.foldr (fun p q => if q.isConstOf ``True then p else mkApp2 (mkConst ``And) p q)
    (mkConst ``True)

private def implication (p q : Expr) : Expr := .forallE .anonymous p q .default

private def builtin (e : Expr) : Bool :=
  #[``And, ``Or, ``Not, ``Iff, ``Eq, ``ite, ``dite,
    ``LE.le, ``LT.lt, ``GE.ge, ``GT.gt,
    ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod,
    ``Neg.neg, ``OfNat.ofNat, ``Int.add, ``Int.sub, ``Int.mul, ``Int.neg,
    ``Int.ediv, ``Int.emod, ``Int.le, ``Int.lt,
    ``Bool.and, ``Bool.or, ``Bool.not, ``Bool.xor].contains
      (e.getAppFn.constName?.getD .anonymous)

private def literal (e : Expr) : Bool :=
  e.isConstOf ``True || e.isConstOf ``False || e.isConstOf ``Bool.true ||
  e.isConstOf ``Bool.false || (e.natLitOf? (mkConst ``Int)).isSome

private def hasKappa (ids : Array MVarId) (e : Expr) : Bool :=
  (e.find? fun e => e.isMVar && ids.contains e.mvarId!).isSome

private def expose (raw : Expr) : MetaM Expr := do
  let e := raw.consumeMData.headBeta
  if let .letE _ _ value body _ := e then return body.instantiate1 value
  -- Typeclass projections such as LE.le must retain their arithmetic syntax.
  if builtin e then return e
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

/-- Observation templates preserve the actual source argument assignment. -/
private def anchor (property occurrence : Expr) (kvar : KVar) : MetaM (Option Expr) := do
  let args := occurrence.getAppArgs
  if !property.hasFVar || property.hasMVar || property.hasLooseBVars || literal property then return none
  forallTelescope (← kvar.mvarId.getType) fun parameters _ => do
    unless parameters.size == args.size do return none
    let body := property.replace fun e => do
      let i ← args.findIdx? (fun arg => arg.hasFVar && arg == e)
      return parameters[i]!
    let feature ← mkLambdaFVars parameters body (usedOnly := false)
    if feature.hasFVar || feature.hasMVar || feature.hasLooseBVars then return none
    unless ← scalar (← inferType body) do return none
    check feature
    return some feature

private partial def collectTerms (ids : Array MVarId) (raw : Expr)
    (relations observations : Array Expr) : MetaM (Array Expr × Array Expr) := do
  let e ← expose raw
  if hasKappa ids e && e.getAppFn.isMVar then
    return (if relations.contains e then relations else relations.push e, observations)
  let mut observations := observations
  if !e.hasMVar && !e.hasLooseBVars && !literal e && !builtin e &&
      (← scalar (← inferType e)) && e.isApp then
    if !observations.contains e then observations := observations.push e
  if let .forallE name domain body bi := e then
    if ← isProp domain then
      let (rs, os) ← collectTerms ids domain relations observations
      return ← withLocalDecl name bi domain fun p =>
        collectTerms ids (body.instantiate1 p) rs os
    return (relations, observations)
  let mut relations := relations
  for arg in e.getAppArgs do
    if !(← inferType arg).isSort then
      let (rs, os) ← collectTerms ids arg relations observations
      relations := rs
      observations := os
  return (relations, observations)

private def initialFeatures (kvar : KVar) : MetaM (Array Expr) := do
  forallTelescope (← kvar.mvarId.getType) fun parameters _ => do
    let mut result := #[]
    for parameter in parameters do
      if ← scalar (← inferType parameter) then
        result := result.push (← mkLambdaFVars parameters parameter (usedOnly := false))
    for i in [:parameters.size] do
      let type ← inferType parameters[i]!
      if ← scalar type then continue
      for j in [i + 1:parameters.size] do
        if ← isDefEq type (← inferType parameters[j]!) then
          result := result.push (← mkLambdaFVars parameters
            (← mkEq parameters[i]! parameters[j]!) (usedOnly := false))
    return result

private def discover (kvars : List KVar) (clauses : Array Expr) (cfg : Config)
    : MetaM (Array (Array Expr)) := do
  let ks := kvars.toArray
  let ids := ks.map (·.mvarId)
  let mut features ← ks.mapM initialFeatures
  for fs in features, k in ks do
    if fs.size > cfg.maxFeatures then
      throwError "CHC projection: initial feature limit ({cfg.maxFeatures}) exceeded for {k.name}"
  for clause in clauses do
    features ← forallTelescope clause fun parameters body => do
      let mut relations := #[]
      let mut observations := #[]
      for parameter in parameters do
        let type ← inferType parameter
        if ← isProp type then
          let (rs, os) ← collectTerms ids type relations observations
          relations := rs
          observations := os
      let (rs, os) ← collectTerms ids body relations observations
      relations := rs
      observations := os
      let mut features := features
      for occurrence in relations do
        let some i := ids.findIdx? (· == occurrence.getAppFn.mvarId!) | continue
        for property in observations do
          if let some feature ← anchor property occurrence ks[i]! then
            if !features[i]!.contains feature then
              if features[i]!.size >= cfg.maxFeatures then
                throwError "CHC projection: feature limit ({cfg.maxFeatures}) exceeded for {ks[i]!.name}"
              features := features.set! i (features[i]!.push feature)
      return features
  return features

private structure Variable where
  original : Expr
  value : Expr
  type : Expr

private structure Equality where
  left : Expr
  right : Expr
  value : Expr

private structure ClauseState where
  variables : Array Variable := #[]
  equalities : Array Equality := #[]
  values : Array Expr := #[]
  applications : Array Expr := #[]

private abbrev ClauseM := StateT ClauseState MetaM

private def fresh (original type : Expr) (cfg : Config) : ClauseM Expr := do
  if let some old := (← get).variables.find? (·.original == original) then return old.value
  if (← get).variables.size >= cfg.maxTermsPerClause then
    throwError "CHC projection: variable limit ({cfg.maxTermsPerClause}) exceeded in a clause"
  let value := mkFVar (← mkFreshFVarId)
  modify fun s => { s with variables := s.variables.push { original, value, type } }
  return value

private def addValue (e : Expr) (cfg : Config) : ClauseM Unit := do
  unless (← get).values.contains e do
    if (← get).values.size >= cfg.maxTermsPerClause then
      throwError "CHC projection: unsupported-value limit exceeded in a clause"
    modify fun s => { s with values := s.values.push e }

private def opaqueEquality (a b : Expr) (cfg : Config) : ClauseM Expr := do
  if a == b then return mkConst ``True
  if let some old := (← get).equalities.find? fun old =>
      (old.left == a && old.right == b) || (old.left == b && old.right == a) then
    return old.value
  addValue a cfg
  addValue b cfg
  let original ← mkEq a b
  let value ← fresh original (mkSort .zero) cfg
  modify fun s => { s with equalities := s.equalities.push { left := a, right := b, value } }
  return value

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

private partial def abstractTerm (raw : Expr) (mappings : Array Mapping) (cfg : Config)
    : ClauseM Expr := do
  let e ← expose raw
  if literal e then return e
  if let some mapping := mappings.find? (fun m => e.getAppFn == mkMVar m.original.mvarId) then
    let args ← mapping.arguments.mapM fun feature =>
      abstractTerm (feature.beta e.getAppArgs) mappings cfg
    return mkAppN (mkMVar mapping.projected.mvarId) args
  if e.getAppFn.isMVar then throwError "CHC projection: unregistered predicate or unresolved metavariable"
  if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
    let type := e.getArg! 0
    unless ← scalar type do
      throwError "CHC projection: unsupported conditional result type {type}"
    let condition ← abstractTerm (e.getArg! 1) mappings cfg
    let branch (value : Expr) : ClauseM Expr := do
      if e.isAppOfArity ``dite 5 then
        let .lam _ _ body _ := value.headBeta
          | throwError "CHC projection: expected a conditional branch lambda"
        if body.hasLooseBVar 0 then
          throwError "CHC projection: proof-dependent conditional branches are unsupported"
        abstractTerm (body.instantiate1 (mkConst ``True.intro)) mappings cfg
      else abstractTerm value mappings cfg
    let yes ← branch (e.getArg! 3)
    let no ← branch (e.getArg! 4)
    return mkApp5 (mkConst ``ite e.getAppFn.constLevels!) type condition
      (mkApp (mkConst ``Classical.propDecidable) condition) yes no
  if e.isAppOfArity ``Iff 2 then
    return mkApp3 (mkConst ``Eq [.succ .zero]) (mkSort .zero)
      (← abstractTerm (e.getArg! 0) mappings cfg)
      (← abstractTerm (e.getArg! 1) mappings cfg)
  if let some (type, a, b) := e.eq? then
    if let some fields ← structureEquality? type a b then
      return ← abstractTerm fields mappings cfg
    if let some fields ← constructorEquality? a b then
      return ← abstractTerm fields mappings cfg
    if ← scalar type then
      return mkApp3 e.getAppFn type (← abstractTerm a mappings cfg) (← abstractTerm b mappings cfg)
    return ← opaqueEquality a b cfg
  if let .forallE _ domain body _ := e then
    if (← isProp domain) && !body.hasLooseBVar 0 then
      return implication (← abstractTerm domain mappings cfg)
        (← abstractTerm (body.instantiate1 (mkConst ``True.intro)) mappings cfg)
    -- Quantified semantic properties are single observations; no binder escapes.
    unless ← isProp e do throwError "CHC projection: unsupported function-valued observation"
    return ← fresh e (mkSort .zero) cfg
  if builtin e then
    let mut args := #[]
    for arg in e.getAppArgs do
      let type ← inferType arg
      let arg ← if ← scalar type then abstractTerm arg mappings cfg else pure arg
      args := args.push arg
    return mkAppN e.getAppFn args
  let type ← inferType e
  unless ← scalar type do throwError "CHC projection: unsupported observation result {type}"
  addApplication e
  fresh e type cfg

private def observedEquality (a b : Expr) (mappings : Array Mapping) (cfg : Config)
    : ClauseM Expr := do
  if a == b then return mkConst ``True
  let ta ← inferType a
  unless ← isDefEq ta (← inferType b) do
    throwError "CHC projection: equality between observations of different types"
  if ← scalar ta then
    let lhs ← abstractTerm a mappings cfg
    let rhs ← abstractTerm b mappings cfg
    return mkApp3 (mkConst ``Eq [← getLevel ta]) ta lhs rhs
  opaqueEquality a b cfg

/-- Finite congruence keeps frame equalities conditional on learned observations. -/
private def congruence (mappings : Array Mapping) (cfg : Config) : ClauseM (Array Expr) := do
  let mut facts := #[]
  let mut visited : Array (Expr × Expr) := #[]
  let mut cursor := 0
  while cursor < (← get).applications.size do
    let left := (← get).applications[cursor]!
    cursor := cursor + 1
    let applications := (← get).applications
    for right in applications do
      if left == right || left.getAppFn != right.getAppFn then continue
      if visited.contains (left, right) || visited.contains (right, left) then continue
      if visited.size >= cfg.maxCongruencePairs then
        throwError "CHC projection: congruence limit ({cfg.maxCongruencePairs}) exceeded"
      visited := visited.push (left, right)
      let aa := left.getAppArgs
      let bb := right.getAppArgs
      unless aa.size == bb.size do continue
      let mut premises := #[]
      let mut compatible := true
      for a in aa, b in bb do
        if a == b then continue
        let type ← inferType a
        -- Type/instance arguments must agree; they are not runtime values.
        if (type.isSort && !type.isProp) || (← isProp type) then
          unless ← isDefEq a b do
            compatible := false
            break
        else premises := premises.push (← observedEquality a b mappings cfg)
      unless compatible do continue
      let conclusion ← observedEquality left right mappings cfg
      facts := facts.push (implication (conj premises) conclusion)
  let values := (← get).values
  for i in [:values.size] do
    for j in [i + 1:values.size] do
      unless ← isDefEq (← inferType values[i]!) (← inferType values[j]!) do continue
      for k in [j + 1:values.size] do
        unless ← isDefEq (← inferType values[i]!) (← inferType values[k]!) do continue
        if facts.size + 3 > cfg.maxCongruencePairs then
          throwError "CHC projection: equality-congruence limit exceeded"
        let ij ← opaqueEquality values[i]! values[j]! cfg
        let jk ← opaqueEquality values[j]! values[k]! cfg
        let ik ← opaqueEquality values[i]! values[k]! cfg
        facts := facts.push (implication (conj #[ij, jk]) ik)
          |>.push (implication (conj #[ij, ik]) jk)
          |>.push (implication (conj #[ik, jk]) ij)
  return facts

private def projectClause (clause : Expr) (mappings : Array Mapping) (cfg : Config)
    : MetaM Expr :=
  forallTelescope clause fun parameters body => do
    let mut input := body
    for parameter in parameters.reverse do
      let type ← inferType parameter
      if ← isProp type then input := implication type input
    let (result, state) ← (do
      let result ← abstractTerm input mappings cfg
      let facts ← congruence mappings cfg
      return if facts.isEmpty then result else implication (conj facts) result).run {}
    let mut result := result
    for entry in state.variables.reverse do
      result := .forallE `observation entry.type (result.abstract #[entry.value]) .default
    if result.hasFVar || result.hasLooseBVars then
      throwError "CHC projection: an observation escaped its clause scope"
    check result
    return result

/-- Infer over scalar observations, retaining the original predicates for certification. -/
def project (kvars : List KVar) (body : Expr) (cfg : Config := {}) : MetaM ProjectedGoal := do
  let ids := kvars.toArray.map (·.mvarId)
  let context : KContext := { kvars := kvars.foldl (fun map k => map.insert k.mvarId k) {} }
  let clauses := (← (exprFlat body Prepare.expose).run context).toArray.filter (hasKappa ids)
  if clauses.size > cfg.maxClauses then
    throwError "CHC projection: clause limit ({cfg.maxClauses}) exceeded"
  let features ← discover kvars clauses cfg
  trace[flex.chc.projection] "clauses {clauses.size}; feature counts {features.map (·.size)}"
  let mut mappings := #[]
  for original in kvars.toArray, arguments in features do
    let mut domains := #[]
    for argument in arguments do
      let domain ← forallTelescope (← original.mvarId.getType) fun parameters _ =>
        inferType (argument.beta parameters)
      if domain.hasFVar then throwError "CHC projection: dependent observation type"
      domains := domains.push domain
    let type := domains.foldr (fun domain body => .forallE .anonymous domain body .default) (mkSort .zero)
    let symbol ← mkFreshExprMVar (some type) (kind := .syntheticOpaque)
      (userName := original.name)
    let projected : KVar := {
      name := original.name
      mvarId := symbol.mvarId!
      params := (List.range domains.size).map (fun i => Name.mkSimple s!"p{i}")
      paramTypes := domains.toList }
    mappings := mappings.push { original, projected, arguments }
  let clauses ← clauses.mapM (projectClause · mappings cfg)
  return { kvars := (mappings.map (·.projected)).toList, body := conj clauses, mappings }

end Flex.CHC.Projection
