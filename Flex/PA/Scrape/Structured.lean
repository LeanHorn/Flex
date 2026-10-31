import Flex.PA.Scrape.Indices

/-! Predicate-slot substitutions, scalar measures, and homogeneous-list observations. -/

open Lean Meta

namespace PAScrape.Structured

open PAScrape.Internal (support dependsOnArguments isResolved isCandidate appendCandidate indexedPredicates)

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

private def matchingSlots (value : Expr) (arguments : Array Expr) : MetaM (Array Expr) := do
  let type ← inferType value
  if type.hasMVar then return #[]
  if (← isProp type) || (← whnf type).isSort then return #[]
  arguments.filterM (hasSlotType · type)

private def compoundVariants (property : Expr) (arguments : Array Expr) (limit : Nat)
    : MetaM (Array Expr) := do
  unless isResolved property do return #[]
  unless ← isProp property do return #[]
  let fn := property.getAppFn
  let .const name _ := fn | return #[]
  let .defnInfo _ ← getConstInfo name | return #[]
  let args := property.getAppArgs
  let mut bases := #[]
  let mut positions := #[]
  let mut fuel := 32 * limit
  for i in [:args.size] do
    let arg := args[i]!
    if arguments.contains arg || !arg.hasFVar then continue
    if ← numeric (← inferType arg) then
      positions := positions.push i
    else
      if bases.size >= 4 then continue
      for slot in ← matchingSlots arg arguments do
        unless (arg.find? (· == slot)).isSome do continue
        if fuel == 0 then return bases.extract 0 limit
        fuel := fuel - 1
        let base := mkAppN fn (args.set! i slot)
        bases ← appendCandidate bases base
        if bases.size >= 4 then break
  if bases.isEmpty then
    if positions.isEmpty then return #[]
    bases := #[property]
  let mut result := bases.filter (· != property)
  for base in bases do
    let baseArgs := base.getAppArgs
    for i in positions do
      let original := args[i]!
      let slots ← matchingSlots original arguments
      -- Try new loop parameters first; retain source parameters in companion positions.
      let fresh := slots.filter fun slot => (property.find? (· == slot)).isNone
      let rest := slots.filter (!fresh.contains ·)
      let support := slots.filter fun slot => (original.find? (· == slot)).isSome
      let companions := support ++ slots.filter (!support.contains ·)
      for slot in fresh ++ rest do
        if fuel == 0 then return result.extract 0 limit
        fuel := fuel - 1
        let changed := baseArgs.set! i slot
        let candidate := mkAppN fn changed
        result ← appendCandidate result candidate
        if result.size >= limit then return result.extract 0 limit
        for j in [:args.size] do
          if j == i then continue
          unless ← numeric (← inferType args[j]!) do continue
          for companion in companions do
            if companion == changed[j]! then continue
            if fuel == 0 then return result.extract 0 limit
            fuel := fuel - 1
            let candidate := mkAppN fn (changed.set! j companion)
            result ← appendCandidate result candidate
            if result.size >= limit then return result.extract 0 limit
  return result.extract 0 limit

/-- Abstract compound source arguments, then vary at most two numeric positions. -/
def compoundCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 24)
    : MetaM (Array Expr) := do
  if maxCandidates == 0 then return #[]
  let mut families := #[]
  for property in properties.extract 0 32 do
    let candidates ← compoundVariants property arguments maxCandidates
    unless candidates.isEmpty do families := families.push candidates
  let mut result := #[]
  for i in [:maxCandidates] do
    for family in families do
      if let some candidate := family[i]? then
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
