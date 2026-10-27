import Lean

open Lean Meta

namespace PAScrape.Structured

private def intArray (e : Expr) : MetaM Bool := do
  if e.hasMVar || e.hasLooseBVars then return false
  let type ← whnf (← inferType e)
  return type.isForall && type.bindingDomain!.isConstOf ``Int &&
    type.bindingBody!.isConstOf ``Int

private def intBound (e : Expr) : MetaM Bool := do
  if e.hasMVar || e.hasLooseBVars || !e.hasFVar then return false
  return (← whnf (← inferType e)).isConstOf ``Int

private def indexShift? (e index : Expr) : Option Expr := do
  let args := e.getAppArgs
  let name := e.getAppFn.constName?.getD .anonymous
  let (left, right) ←
    if name == ``HAdd.hAdd && args.size == 6 && args[0]!.isConstOf ``Int &&
        args[1]!.isConstOf ``Int && args[2]!.isConstOf ``Int then
      some (args[4]!, args[5]!)
    else if name == ``Int.add && args.size == 2 then some (args[0]!, args[1]!)
    else none
  if left == index && !right.containsFVar index.fvarId! then return right
  if right == index && !left.containsFVar index.fvarId! then return left
  none

private def readShifts (body index : Expr) : MetaM (Array Expr) := do
  let mut pending := #[body]
  let mut shifts := #[]
  let mut fuel := 256
  while !pending.isEmpty && fuel > 0 && shifts.size < 2 do
    fuel := fuel - 1
    let e := pending.back!
    pending := pending.pop
    if let .app f argument := e then
      if f.isFVar && (← intArray f) then
        if let some shift := indexShift? argument index then
          if !shift.hasLooseBVars && !shift.hasMVar && !shifts.contains shift then
            shifts := shifts.push shift
      pending := pending.push f |>.push argument
    else if let .forallE _ domain body _ := e then
      pending := pending.push domain |>.push body
    else if let .lam _ domain body _ := e then
      pending := pending.push domain |>.push body
    else if let .letE _ _ value body _ := e then
      pending := pending.push value |>.push body
    else if let .mdata _ body := e then
      pending := pending.push body
  return shifts

private theorem shiftedIndex (offset index : Int) : offset + (index - offset) = index := by omega

private theorem shiftedBase (base offset index : Int) :
    (base + offset) + (index - offset) = base + index := by omega

private def normalizeIndices (expression : Expr) : MetaM Expr := do
  let mut lemmas : SimpTheorems := {}
  for name in #[``Int.sub_nonneg, ``Int.sub_lt_sub_right_iff,
      ``Int.sub_le_sub_right_iff, ``Int.add_sub_cancel, ``Int.sub_add_cancel,
      ``shiftedIndex, ``shiftedBase, ``Int.add_assoc,
      ``Int.sub_sub, ``Int.sub_zero, ``Int.add_zero, ``Int.zero_add] do
    lemmas ← lemmas.addConst name
  let context ← Simp.mkContext { maxSteps := 2000, failIfUnchanged := false } #[lemmas]
  return (← Meta.simp expression context).1.expr

/-- Reindex quantified reads by their source offsets. PA checks the resulting candidates. -/
def absoluteIndexCandidates (property : Expr) (maxCandidates : Nat := 2)
    : MetaM (Array Expr) := do
  if maxCandidates == 0 || property.hasMVar || property.hasLooseBVars then return #[]
  let property ← whnf (← normalizeIndices property)
  let .forallE name domain body bi := property | return #[]
  unless (← whnf domain).isConstOf ``Int do return #[]
  withLocalDecl name bi domain fun index => do
    let body := body.instantiate1 index
    let shifts ← readShifts body index
    let mut candidates := #[]
    for shift in shifts do
      let replacement ← mkAppM ``HSub.hSub #[index, shift]
      let body ← normalizeIndices (body.replaceFVar index replacement)
      let candidate ← mkForallFVars #[index] body
      if candidates.contains candidate then continue
      check candidate
      candidates := candidates.push candidate
      if candidates.size >= maxCandidates then break
    return candidates

/-- Find ordered array reads under integer quantifiers, with bounded unfolding. -/
private partial def reads (array : Expr) (raw : Expr) (depth : Nat)
    (indices : FVarIdSet := {})
    : StateT Nat MetaM Bool := do
  if depth == 0 || (← get) == 0 then return false
  modify (· - 1)
  let e := raw.consumeMData.headBeta
  let indexed := fun value : Expr => value.isApp && value.appFn! == array &&
    (collectFVars {} value.appArg!).fvarIds.any indices.contains
  let args := e.getAppArgs
  let name := e.getAppFn.constName?.getD .anonymous
  if ((name == ``Int.le || name == ``Int.lt) && args.size == 2) ||
      ((name == ``LE.le || name == ``LT.lt) && args.size == 4 && args[0]!.isConstOf ``Int) then
    if indexed args[args.size - 2]! || indexed args[args.size - 1]! then return true
  match e with
  | .forallE name domain body bi =>
    withLocalDecl name bi domain fun x => do
      let indices := if (← whnf domain).isConstOf ``Int then indices.insert x.fvarId! else indices
      reads array (body.instantiate1 x) (depth - 1) indices
  | .lam name domain body bi =>
    withLocalDecl name bi domain fun x => reads array (body.instantiate1 x) (depth - 1) indices
  | .letE _ _ value body _ => reads array (body.instantiate1 value) (depth - 1) indices
  | .app .. =>
    for arg in e.getAppArgs do
      if ← reads array arg (depth - 1) indices then return true
    if ← isProp e then
      let exposed ← whnf e
      if exposed != e then return ← reads array exposed (depth - 1) indices
    return false
  | _ => return false

/-- Propose prefix comparisons for arrays ordered in the source. PA checks them. -/
def prefixCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 24)
    : MetaM (Array Expr) := do
  if maxCandidates == 0 then return #[]
  let mut out := #[]
  for array in arguments do
    unless ← intArray array do continue
    let mut used := false
    let mut fuel := 256
    for property in properties do
      let (found, remaining) ← (reads array property 12).run fuel
      fuel := remaining
      if found then used := true; break
    unless used do continue
    for bound in arguments do
      unless ← intBound bound do continue
      let candidates ← withLocalDeclD `index (mkConst ``Int) fun index => do
        let value := mkApp array index
        let lower ← mkAppM ``LE.le #[mkIntLit 0, index]
        let upper ← mkAppM ``LT.lt #[index, bound]
        let mut candidates := #[]
        for target in #[bound, index, mkIntLit 0] do
          for relation in #[``LT.lt, ``LE.le] do
            let comparison ← mkAppM relation #[value, target]
            let body ← mkArrow lower (← mkArrow upper comparison)
            candidates := candidates.push (← mkForallFVars #[index] body)
        let equality ← mkArrow lower (← mkArrow upper (← mkEq value index))
        candidates := candidates.push (← mkForallFVars #[index] equality)
        return candidates
      for candidate in candidates do
        if out.contains candidate then continue
        check candidate
        out := out.push candidate
        if out.size >= maxCandidates then return out
  return out

end PAScrape.Structured

namespace PAScrape.Structured

private def checked (candidate : Expr) : MetaM Bool := do
  if candidate.hasMVar || candidate.hasLooseBVars then return false
  try
    check candidate
    return ← isProp candidate
  catch e =>
    if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
    return false

private def numeric (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return type.isConstOf ``Int || type.isConstOf ``Nat

/-- Change argument positions independently, keeping compound bounds intact. -/
def slotCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 24)
    : MetaM (Array Expr) := do
  if maxCandidates == 0 then return #[]
  let mut result := #[]
  for property in properties do
    if property.hasMVar || !(← isProp property) then continue
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
      if type.hasMVar || (← isProp type) || (← whnf type).isSort || (← numeric type) then continue
      for replacement in arguments do
        if replacement == arg || replacement.hasMVar then continue
        let replacementType ← inferType replacement
        if replacementType.hasMVar then continue
        unless ← isDefEq type replacementType do continue
        let candidate := mkAppN fn (args.set! i replacement)
        if ← checked candidate then
          unless bases.contains candidate do bases := bases.push candidate
          unless result.contains candidate do result := result.push candidate
          if result.size >= maxCandidates then return result
    for base in bases do
      let args := base.getAppArgs
      for i in [:args.size] do
        let arg := args[i]!
        unless arguments.contains arg do continue
        let type ← inferType arg
        if type.hasMVar || !(← numeric type) then continue
        for replacement in arguments do
          if replacement == arg || replacement.hasMVar then continue
          let replacementType ← inferType replacement
          if replacementType.hasMVar then continue
          unless ← isDefEq type replacementType do continue
          let candidate := mkAppN fn (args.set! i replacement)
          if ← checked candidate then
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
    if depth < 3 && e.isApp && (← listType? (← inferType e)).isSome then
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
      if ← checked candidate then
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
        if ← checked candidate then
          unless result.contains candidate do result := result.push candidate
          if result.size >= maxCandidates then return result
  return result

end PAScrape.Structured
