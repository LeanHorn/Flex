import Flex.PA.Scrape.Indices

/-! Predicate-slot substitutions, scalar measures, and homogeneous-list observations. -/

open Lean Meta

namespace PAScrape.Structured

open PAScrape.Internal (support containsArgument dependsOnArguments isResolved isCandidate
  appendCandidate indexedPredicates)

private def numeric (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return type.isConstOf ``Int || type.isConstOf ``Nat

private partial def endpointVariants (e : Expr) (arguments : Array Expr)
    (cap : Nat) : StateT Nat MetaM (Array Expr) := do
  if cap == 0 || (← get) == 0 then return #[]
  modify (· - 1)
  if e.isFVar && !arguments.contains e then
    let type ← whnf (← inferType e)
    if type.isConstOf ``Int || type.isConstOf ``Nat then
      let mut out := #[]
      for arg in arguments do
        if arg == e || arg.hasMVar || arg.hasLooseBVars then continue
        if (← whnf (← inferType arg)) == type then out := out.push arg
        if out.size >= cap then break
      return out
  match e with
  | .app f a =>
    let right ← endpointVariants a arguments cap
    let left ← endpointVariants f arguments (cap - right.size)
    return right.map (mkApp f) ++ left.map (mkApp · a)
  | .mdata data body =>
    return (← endpointVariants body arguments cap).map (.mdata data)
  | .proj name index body =>
    return (← endpointVariants body arguments cap).map (.proj name index)
  -- Bound variables and dependent binder types are never rewritten.
  | _ => return #[]

/-- Replace one numeric endpoint occurrence by a predicate slot; PA validates it. -/
def endpointCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 24)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let mut families := #[]
  for property in properties.extract 0 32 do
    unless isResolved property do continue
    unless ← isProp property do continue
    let fresh := arguments.filter fun arg => (property.find? (· == arg)).isNone
    let slots := fresh ++ arguments.filter (!fresh.contains ·)
    let (variants, _) ← (endpointVariants property slots maxCandidates).run 256
    let mut candidates := #[]
    for candidate in variants do
      if candidate != property then candidates ← appendCandidate candidates candidate
    unless candidates.isEmpty do families := families.push candidates
  let mut result := #[]
  for i in [:maxCandidates] do
    for family in families do
      if let some candidate := family[i]? then
        unless result.contains candidate do result := result.push candidate
        if result.size >= maxCandidates then return result
  return result

/-- A terminal equality supplies a bounded affine endpoint substitution. -/
def affineCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  for equation in properties.extract 0 32 do
    if equation.hasMVar || equation.hasLooseBVars then continue
    let some (_, lhs, rhs) := equation.eq? | continue
    for (slot, endpoint) in #[(lhs, rhs), (rhs, lhs)] do
      unless arguments.contains slot do continue
      let type ← whnf (← inferType slot)
      unless ← numeric type do continue
      let name := endpoint.getAppFn.constName?.getD .anonymous
      let isAdd := #[``HAdd.hAdd, ``Nat.add, ``Int.add].contains name
      let isSub := #[``HSub.hSub, ``Nat.sub, ``Int.sub].contains name
      unless isAdd || isSub do continue
      let args := endpoint.getAppArgs
      if args.size < 2 then continue
      let input := args[args.size - 2]!
      let offset := args[args.size - 1]!
      unless input.isFVar && !arguments.contains input do continue
      let natValue ← getNatValue? offset
      let intValue ← getIntValue? offset
      let small := if type.isConstOf ``Nat then natValue.any (fun n => decide (n ≤ 16))
        else intValue.any (fun n => decide (n.natAbs ≤ 16))
      unless small do continue
      let replacement ← mkAppM (if isAdd then ``HSub.hSub else ``HAdd.hAdd) #[slot, offset]
      for property in properties.extract 0 32 do
        if fuel == 0 then return out
        fuel := fuel - 1
        if property == equation || property.hasMVar || property.hasLooseBVars then continue
        unless property.containsFVar input.fvarId! do continue
        let candidate := property.replaceFVar input replacement
        out ← appendCandidate out candidate
        if out.size >= maxCandidates then return out
      for (left, right) in #[(slot, endpoint), (endpoint, slot)] do
        let candidate ← mkAppM ``LE.le #[left, right]
        out ← appendCandidate out candidate
        if out.size >= maxCandidates then return out
  return out

/-- Sparse affine forms keep source applications opaque. -/
private structure AffineForm where
  terms : Array (Expr × Rat) := #[]
  constant : Rat := 0
  deriving Inhabited

private def AffineForm.coeff (form : AffineForm) (atom : Expr) : Rat :=
  (form.terms.find? (·.1 == atom)).map (·.2) |>.getD 0

private def AffineForm.add (a b : AffineForm) (scale : Rat := 1) : AffineForm := Id.run do
  let mut terms := a.terms
  for (atom, value) in b.terms do
    if let some i := terms.findIdx? (·.1 == atom) then
      terms := terms.set! i (atom, terms[i]!.2 + scale * value)
    else terms := terms.push (atom, scale * value)
  return ⟨terms.filter (·.2 != 0), a.constant + scale * b.constant⟩

private def AffineForm.scale (a : AffineForm) (value : Rat) : AffineForm :=
  ({} : AffineForm).add a value

private def affineOp (e : Expr) (names : Array Name) : Bool :=
  names.contains (e.getAppFn.constName?.getD .anonymous)

private partial def affineForm (raw : Expr) (fuel : Nat := 64) : MetaM AffineForm := do
  let e := raw.consumeMData.headBeta
  if fuel == 0 then return ⟨#[(e, 1)], 0⟩
  if let some value ← getIntValue? e then return ⟨#[], value⟩
  let args := e.getAppArgs
  if args.size >= 2 then
    let a := args[args.size - 2]!
    let b := args.back!
    if affineOp e #[``HAdd.hAdd, ``Int.add, ``HSub.hSub, ``Int.sub] then
      let sign := if affineOp e #[``HSub.hSub, ``Int.sub] then -1 else 1
      return (← affineForm a (fuel - 1)).add (← affineForm b (fuel - 1)) sign
    if affineOp e #[``HMul.hMul, ``Int.mul] then
      if let some n ← getIntValue? a then return (← affineForm b (fuel - 1)).scale n
      if let some n ← getIntValue? b then return (← affineForm a (fuel - 1)).scale n
  if !args.isEmpty && affineOp e #[``Neg.neg, ``Int.neg] then
    return (← affineForm args.back! (fuel - 1)).scale (-1)
  -- Keep arithmetic in a selected field intact; whnf would also unfold that arithmetic.
  if e.isProj then
    if let some reduced ← reduceProj? e then return ← affineForm reduced (fuel - 1)
  else if (← getProjectionFnInfo? (e.getAppFn.constName?.getD .anonymous)).isSome then
    if let some reduced ← unfoldDefinition? e then return ← affineForm reduced (fuel - 1)
  return ⟨#[(e, 1)], 0⟩

private def reduceAffine (form : AffineForm) (basis : Array (Expr × AffineForm)) : AffineForm :=
  basis.foldl (fun current (atom, row) => current.add row (-current.coeff atom)) form

private def affineEquations (properties : Array Expr) : Array Expr := Id.run do
  let mut pending := properties.toList
  let mut equations := #[]
  for _ in [:512] do
    let e :: rest := pending | break
    pending := rest
    if !isResolved e then continue
    if e.eq?.isSome && !equations.contains e then equations := equations.push e
    pending := e.getAppArgs.toList ++ pending
  return equations

private def cyclicAffineAlias (input value : Expr) (aliases : Array (Expr × Expr)) : Bool := Id.run do
  let mut pending := support value
  let mut visited : FVarIdSet := {}
  while let some id := pending.back? do
    pending := pending.pop
    if visited.contains id then continue
    if id == input.fvarId! then return true
    visited := visited.insert id
    for (lhs, rhs) in aliases do
      if lhs.fvarId! == id then pending := pending ++ support rhs
  return false

private def sourceAffineBasis (equations : Array Expr)
    : MetaM (Array (Expr × AffineForm) × Array (Expr × Expr)) := do
  let mut aliases := #[]
  for equation in equations do
    let some (type, lhs, rhs) := equation.eq? | continue
    if (← whnf type).isConstOf ``Int then continue
    for (a, b) in #[(lhs, rhs), (rhs, lhs)] do
      if a.isFVar && !cyclicAffineAlias a b aliases then aliases := aliases.push (a, b)
  let mut basis := #[]
  for equation in equations do
    let some (type, lhs, rhs) := equation.eq? | continue
    unless (← whnf type).isConstOf ``Int do continue
    let row := reduceAffine ((← affineForm lhs).add (← affineForm rhs) (-1)) basis
    let some (atom, value) := row.terms[0]? | continue
    basis := basis.push (atom, row.scale (1 / value))
  return (basis, aliases)

private def rewriteAffineAliases (e : Expr) (aliases : Array (Expr × Expr)) : Expr :=
  (List.range 3).foldl (fun e _ => aliases.foldl (fun e (a, b) => e.replaceFVar a b) e) e

private structure AffineSystem where
  types : Array Expr
  features : Array Expr := #[]
  entryPairs : Array (Nat × Nat) := #[]
  rows : Array (Nat × Array Rat) := #[]
  entries : Nat := 0
  transitions : Nat := 0
  deriving Inhabited

private def affineRow (rows : Array (Nat × Array Rat)) (input : Array Rat)
    : Array (Nat × Array Rat) := Id.run do
  let subtract (a b : Array Rat) (c : Rat) := a.zipWith (fun x y => x - c * y) b
  let row := rows.foldl (fun row (i, old) => subtract row old row[i]!) input
  let some pivot := row.findIdx? (· != 0) | return rows
  let row := row.map (· / row[pivot]!)
  return (rows.map fun (i, old) => (i, subtract old row old[pivot]!)).push (pivot, row)

private partial def affineCalls (e : Expr) (fuel : Nat := 64) : Array Expr :=
  if fuel == 0 then #[] else if e.getAppFn.isMVar then #[e]
  else e.getAppArgs.foldl (fun found arg => found ++ affineCalls arg (fuel - 1)) #[]

private partial def affineClauses (raw : Expr) (fuel : IO.Ref Nat)
    (visit : Array Expr → Expr → MetaM Unit) (premises : Array Expr := #[]) : MetaM Unit := do
  if (← fuel.get) == 0 then return
  fuel.modify (· - 1)
  let e := raw.consumeMData.headBeta
  if let .letE _ _ value body _ := e then
    affineClauses (body.instantiate1 value) fuel visit premises
  else if let .forallE name type body bi := e then
    let premises ← if ← isProp type then pure (premises.push type) else pure premises
    withLocalDecl name bi type fun x => affineClauses (body.instantiate1 x) fuel visit premises
  else if let some (left, right) := e.and? then
    affineClauses left fuel visit premises
    affineClauses right fuel visit premises
  else if e.getAppFn.isMVar then visit premises e

private def affineFeatures (fixed : FVarIdSet) (system : AffineSystem)
    (properties : Array Expr) (relation : Expr) : MetaM AffineSystem := do
  withLocalDeclsDND (system.types.map (`slot, ·)) fun slots => do
    let mut features := system.features
    if features.isEmpty then
      for slot in slots do
        if (← inferType slot).isConstOf ``Int then
          features := features.push (← mkLambdaFVars slots slot)
    let arguments := relation.getAppArgs
    let mut pending := (properties ++ arguments).toList
    for _ in [:512] do
      let e :: rest := pending | break
      pending := rest
      if features.size >= 24 then break
      pending := e.getAppArgs.toList ++ pending
      unless (e.isApp || e.isFVar || e.isProj) && isResolved e do continue
      unless (← whnf (← inferType e)).isConstOf ``Int do continue
      if affineOp e #[``HAdd.hAdd, ``Int.add, ``HSub.hSub, ``Int.sub,
          ``HMul.hMul, ``Int.mul, ``Neg.neg, ``Int.neg, ``OfNat.ofNat] then continue
      let fixedValue := (support e).all fixed.contains
      let value := if fixedValue then e else e.replace fun part =>
        arguments.findIdx? (fun arg => arg.hasFVar && arg == part) |>.map (slots[·]!)
      unless fixedValue || containsArgument value slots do continue
      let feature ← mkLambdaFVars slots value
      unless (support feature).all fixed.contains do continue
      unless features.contains feature do features := features.push feature
    return { system with features }

/-- An entry's equal arguments transfer observed measures between those slots. -/
private def closeAffineFeatures (system : AffineSystem) : MetaM AffineSystem := do
  withLocalDeclsDND (system.types.map (`slot, ·)) fun slots => do
    let mut features := system.features
    let mut cursor := 0
    let mut attempts := 0
    while cursor < features.size && features.size < 24 && attempts < 256 do
      let value := (mkAppN features[cursor]! slots).headBeta
      cursor := cursor + 1
      unless value.isApp || value.isProj do continue
      for (a, b) in system.entryPairs do
        for (source, target) in #[(a, b), (b, a)] do
          if features.size >= 24 || attempts >= 256 then break
          unless value.containsFVar slots[source]!.fvarId! do continue
          attempts := attempts + 1
          let feature ← mkLambdaFVars slots (value.replaceFVar slots[source]! slots[target]!)
          unless features.contains feature do features := features.push feature
    return { system with features }

private def addAffineClause (system : AffineSystem) (premises : Array Expr) (head : Expr)
    : MetaM AffineSystem := do
  let previous := premises.flatMap affineCalls |>.find? (·.getAppFn == head.getAppFn)
  let (basis, aliases) ← sourceAffineBasis (affineEquations premises)
  let evaluate (feature relation : Expr) := do
    let value := (mkAppN feature relation.getAppArgs).headBeta
    return reduceAffine (← affineForm (rewriteAffineAliases value aliases)) basis
  let mut forms := #[]
  for feature in system.features do
    let after ← evaluate feature head
    let before ← match previous with
      | some relation => evaluate feature relation
      | none => pure {}
    forms := forms.push (after.add before (-1))
  forms := forms.push ⟨#[], if previous.isSome then 0 else 1⟩
  let atoms := forms.foldl (fun atoms form =>
    form.terms.foldl (fun atoms (atom, _) => if atoms.contains atom then atoms else atoms.push atom) atoms) #[]
  let mut rows := system.rows
  for atom in atoms do rows := affineRow rows (forms.map (·.coeff atom))
  rows := affineRow rows (forms.map (·.constant))
  return { system with
    rows
    entries := system.entries + (if previous.isNone then 1 else 0)
    transitions := system.transitions + (if previous.isSome then 1 else 0) }

private def affineKernel (system : AffineSystem) : Array (Array Int) := Id.run do
  let mut out := #[]
  for free in [:system.features.size + 1] do
    if system.rows.any (·.1 == free) then continue
    let mut vector := (Array.replicate (system.features.size + 1) (0 : Rat)).set! free 1
    for (pivot, row) in system.rows do vector := vector.set! pivot (-row[free]!)
    let denominator := vector.foldl (fun n q => Nat.lcm n q.den) 1
    let integers := vector.map fun q => q.num * ((denominator / q.den : Nat) : Int)
    let divisor := integers.foldl (fun n c => Nat.gcd n c.natAbs) 0
    let sign := if (integers.find? (· != 0)).getD 0 < 0 then -1 else 1
    out := out.push (integers.map fun c => sign * (c / (divisor : Int)))
  return out

/-- Infer a bounded affine space from entry calls and source transition equations.
`maxNodes` bounds clause traversal; features and nested observations have separate caps.
Conditional equations only suggest relations; PA still checks every candidate. -/
def affineConservationCandidates (body : Expr) (fixed : FVarIdSet)
    (maxCandidates : Nat := 16) (maxNodes : Nat := 5000) : MetaM (Array PAAnchoredQualifier) :=
    withNewMCtxDepth do
  if maxCandidates == 0 || maxNodes == 0 then return #[]
  let systems ← IO.mkRef ({} : Std.HashMap MVarId AffineSystem)
  let fuel ← IO.mkRef maxNodes
  affineClauses body fuel fun premises head => do
    let id := head.getAppFn.mvarId!
    let mut system ← match (← systems.get)[id]? with
      | some system => pure system
      | none => do
        let types ← head.getAppArgs.mapM (fun arg => do whnf (← inferType arg))
        if types.size > 24 || types.any (fun ty =>
            !isResolved ty || !(support ty).all fixed.contains) then return
        pure { types }
    let previous := premises.flatMap affineCalls
    for relation in #[head] ++ previous do
      if relation.getAppFn == head.getAppFn then
        system ← affineFeatures fixed system premises relation
    unless previous.any (·.getAppFn == head.getAppFn) do
      let arguments := head.getAppArgs
      for i in [:arguments.size] do
        for j in [:i] do
          if arguments[i]! == arguments[j]! && !system.entryPairs.contains (i, j) then
            system := { system with entryPairs := system.entryPairs.push (i, j) }
    systems.modify (·.insert id system)
  for (id, system) in (← systems.get).toArray do
    let system ← closeAffineFeatures system
    systems.modify (·.insert id system)
  fuel.set maxNodes
  affineClauses body fuel fun premises head => do
    let id := head.getAppFn.mvarId!
    if let some system := (← systems.get)[id]? then
      let system ← addAffineClause system premises head
      systems.modify (·.insert id system)
  let mut out := #[]
  for (id, system) in (← systems.get).toArray do
    if system.entries == 0 || system.transitions == 0 then continue
    let candidates ← withLocalDeclsDND (system.types.map (`slot, ·)) fun slots => do
      let mut candidates := #[]
      let mut count := 0
      for vector in affineKernel system do
        if count >= maxCandidates then break
        let values := system.features.map (fun f => (mkAppN f slots).headBeta)
        let mut left : Option Expr := none
        let mut right : Option Expr := none
        for coefficient in vector, i in [:vector.size] do
          if coefficient == 0 then continue
          let value ← if i == values.size then pure (mkIntLit coefficient.natAbs)
            else if coefficient.natAbs == 1 then pure values[i]!
            else pure (mkApp2 (mkConst ``Int.mul) (mkIntLit coefficient.natAbs) values[i]!)
          if coefficient > 0 then
            left := some (left.map (mkApp2 (mkConst ``Int.add) · value) |>.getD value)
          else right := some (right.map (mkApp2 (mkConst ``Int.add) · value) |>.getD value)
        let property ← mkEq (left.getD (mkIntLit 0)) (right.getD (mkIntLit 0))
        let used := slots.filter fun slot => property.containsFVar slot.fvarId!
        if used.isEmpty then continue
        let qualifier ← mkLambdaFVars used property
        check qualifier
        let indices := slots.toList.zipIdx |>.filterMap fun (slot, i) =>
          if used.contains slot then some i else none
        candidates := candidates.push (⟨id, qualifier, indices, "affine relations"⟩ : PAAnchoredQualifier)
        count := count + 1
      return candidates
    out := out ++ candidates
  return out

/-- Compare a source observation at fixed inputs and at up to two predicate slots. -/
def measureCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let mut out := #[]
  let mut fuel := 64 * maxCandidates
  for property in properties.extract 0 32 do
    if property.hasMVar || property.hasLooseBVars then continue
    let some (_, lhs, rhs) := property.eq? | continue
    for target in #[lhs, rhs] do
      unless target.isApp do continue
      if dependsOnArguments target arguments then continue
      let inputsSupport := support target
      let type ← whnf (← inferType target)
      -- Collection-valued observations use completion rather than whole-value preservation.
      unless type.isConstOf ``Nat || type.isConstOf ``Int || type.isConstOf ``Bool do continue
      let mut inputs := #[]
      let mut choices : Array (Array Expr) := #[]
      for id in inputsSupport.extract 0 8 do
        let input := mkFVar id
        let inputType ← inferType input
        if inputType.hasMVar || inputType.hasFVar then continue
        if ← isProp input then continue
        let normalized ← whnf inputType
        if normalized.isForall || normalized.isSort then continue
        let mut compatible := #[]
        for argument in arguments.extract 0 16 do
          if fuel == 0 then return out
          fuel := fuel - 1
          if argument.hasMVar || argument.hasLooseBVars then continue
          let argumentType ← inferType argument
          if argumentType.hasMVar then continue
          if ← isDefEq inputType argumentType then compatible := compatible.push argument
        unless compatible.isEmpty do
          inputs := inputs.push input
          choices := choices.push (compatible.extract 0 4)
        if inputs.size == 2 then break
      if inputs.isEmpty then continue
      let mut variants := #[target]
      for input in inputs, alternatives in choices do
        let mut next := #[]
        for variant in variants do
          for alternative in alternatives do
            if fuel == 0 then return out
            fuel := fuel - 1
            next := next.push (variant.replaceFVar input alternative)
        variants := next
      for variant in variants do
        if variant == target then continue
        let candidate ← mkEq variant target
        out ← appendCandidate out candidate
        if out.size >= maxCandidates then return out
  return out

private def hasSlotType (slot type : Expr) : MetaM Bool := do
  if slot.hasMVar then return false
  let slotType ← inferType slot
  if slotType.hasMVar then return false
  return ← isDefEq type slotType

/-- Change argument positions independently, keeping compound bounds intact. -/
def slotCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 24)
    : MetaM (Array Expr) := do
  if maxCandidates == 0 then return #[]
  let mut result := #[]
  for property in properties do
    if property.hasMVar then continue
    unless ← isProp property do continue
    let fn := property.getAppFn
    let .const name _ := fn | continue
    let .defnInfo _ ← getConstInfo name | continue
    let args := property.getAppArgs
    let mut bases := #[property]
    -- A changing collection and a changing bound often occupy separate positions.
    for i in [:args.size] do
      let arg := args[i]!
      unless arguments.contains arg do continue
      let type ← inferType arg
      if type.hasMVar then continue
      if (← isProp type) || (← whnf type).isSort || (← numeric type) then continue
      for replacement in arguments do
        if replacement == arg then continue
        unless ← hasSlotType replacement type do continue
        let candidate := mkAppN fn (args.set! i replacement)
        if ← isCandidate candidate then
          unless bases.contains candidate do bases := bases.push candidate
          unless result.contains candidate do result := result.push candidate
          if result.size >= maxCandidates then return result
    for base in bases do
      let args := base.getAppArgs
      for i in [:args.size] do
        let arg := args[i]!
        unless arguments.contains arg do continue
        let type ← inferType arg
        if type.hasMVar then continue
        unless ← numeric type do continue
        for replacement in arguments do
          if replacement == arg then continue
          unless ← hasSlotType replacement type do continue
          let candidate := mkAppN fn (args.set! i replacement)
          if ← isCandidate candidate then
            unless result.contains candidate do result := result.push candidate
            if result.size >= maxCandidates then return result
  return result

private def listType? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnf type
  return if type.isAppOfArity ``List 1 then some type.appArg! else none

/-- Find homogeneous-list constructors through a bounded number of abbreviations. -/
private partial def repeatedElements (properties : Array Expr) : MetaM (Array (Expr × Expr)) := do
  let mut pending := properties.map (·, 0)
  let mut seen : ExprSet := {}
  let mut result := #[]
  let mut visits := 0
  while !pending.isEmpty && visits < 256 do
    let (raw, depth) := pending.back!
    pending := pending.pop
    let e := raw.consumeMData.headBeta
    if seen.contains e then continue
    seen := seen.insert e
    visits := visits + 1
    if e.hasLooseBVars || e.hasMVar then continue
    if e.isAppOfArity ``List.replicate 3 then
      let args := e.getAppArgs
      let item := args[2]!
      unless result.any (fun pair => pair.1 == args[0]! && pair.2 == item) do
        result := result.push (args[0]!, item)
      continue
    if let .letE _ _ value body _ := e then
      pending := pending.push (body.instantiate1 value, depth)
      continue
    for arg in e.getAppArgs do pending := pending.push (arg, depth)
    if depth < 3 && e.isApp then
      if (← listType? (← inferType e)).isSome then
        if let some unfolded ← unfoldDefinition? e then
          pending := pending.push (unfolded, depth + 1)
  return result

/-- Derive element and length candidates from a homogeneous-list specification. -/
def listCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 24)
    : MetaM (Array Expr) := do
  if maxCandidates == 0 then return #[]
  let repeated ← repeatedElements properties
  if repeated.isEmpty then return #[]
  let integers ← arguments.filterM fun arg => do
    return (← whnf (← inferType arg)).isConstOf ``Int
  let mut result := #[]
  for list in arguments do
    let some elementType ← listType? (← inferType list) | continue
    if elementType.hasMVar then continue
    let mut matched := false
    for (type, item) in repeated do
      if type.hasMVar then continue
      unless ← isDefEq type elementType do continue
      matched := true
      let candidate ← withLocalDeclD `element elementType fun element => do
        let member ← mkAppM ``Membership.mem #[list, element]
        mkForallFVars #[element] (← mkArrow member (← mkEq element item))
      if ← isCandidate candidate then
        unless result.contains candidate do result := result.push candidate
        if result.size >= maxCandidates then return result
    unless matched do continue
    let length ← mkAppM ``List.length #[list]
    let length ← mkAppM ``Int.ofNat #[length]
    for initial in integers do
      for remaining in integers do
        if initial == remaining then continue
        let difference ← mkAppM ``Int.sub #[initial, remaining]
        let candidate ← mkEq length difference
        if ← isCandidate candidate then
          unless result.contains candidate do result := result.push candidate
          if result.size >= maxCandidates then return result
  return result

/-- Propose processed prefixes and preserved lengths from homogeneous-list specifications. -/
def listPrefixCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := do
  if maxCandidates == 0 then return #[]
  let repeated ← repeatedElements properties
  if repeated.isEmpty then return #[]
  let bounds ← arguments.filterM fun arg => do
    if arg.hasMVar || arg.hasLooseBVars then return false
    let type ← inferType arg
    if type.hasMVar then return false
    numeric type
  let mut lists := #[]
  for list in arguments do
    if list.hasMVar || list.hasLooseBVars then continue
    let some elementType ← listType? (← inferType list) | continue
    if elementType.hasMVar then continue
    unless ← repeated.anyM (fun (type, _) => do
        if type.hasMVar then return false
        isDefEq type elementType) do continue
    unless lists.any (fun (other, _) => other == list) do
      lists := lists.push (list, elementType)
  let mut result := #[]
  let lengthLimit := max 1 (maxCandidates / 4)
  for i in [:lists.size] do
    for j in [:i] do
      if result.size >= lengthLimit then break
      let (list, elementType) := lists[i]!
      let (other, otherType) := lists[j]!
      unless ← isDefEq elementType otherType do continue
      let lhs ← mkAppM ``Int.ofNat #[← mkAppM ``List.length #[list]]
      let rhs ← mkAppM ``Int.ofNat #[← mkAppM ``List.length #[other]]
      let candidate ← mkEq lhs rhs
      if ← isCandidate candidate then result := result.push candidate
      if result.size >= maxCandidates then return result
  for (list, elementType) in lists do
    for (type, item) in repeated do
      if type.hasMVar || item.hasMVar then continue
      unless ← isDefEq type elementType do continue
      for bound in bounds do
        let candidates ← indexedPredicates (mkConst ``Nat) none (some bound) fun index => do
          let value ← mkAppM ``GetElem?.getElem? #[list, index]
          return #[← mkEq value (← mkAppM ``Option.some #[item])]
        for candidate in candidates do
          if ← isCandidate candidate then
            unless result.contains candidate do result := result.push candidate
            if result.size >= maxCandidates then return result
  return result

end PAScrape.Structured
