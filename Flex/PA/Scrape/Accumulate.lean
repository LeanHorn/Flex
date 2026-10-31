import Flex.PA.Scrape.Core

/-! Accumulator completion, guarded fragments, and worklist measures. -/

open Lean Meta

namespace PAScrape.Accumulate

open PAScrape.Internal (isResolved support containsArgument dependsOnArguments appendCandidate)

private def listType (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return isResolved type && !type.hasFVar && type.isAppOfArity ``List 1

private def compose? (left right : Expr) : MetaM (Option Expr) := do
  let type ← whnf (← inferType left)
  if type.isConstOf ``Nat then return some (mkApp2 (mkConst ``Nat.add) left right)
  if type.isConstOf ``Int then return some (mkApp2 (mkConst ``Int.add) left right)
  if ← listType type then return some (← mkAppM ``List.append #[left, right])
  return none

/-- Complete a source observation `acc = F(input)` with `F(remaining)`.
Both composition orders are candidates; PA must establish inductiveness and safety. -/
def candidates (properties arguments : Array Expr) (maxCandidates : Nat := 24)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.filter isResolved
  let mut out := #[]
  let mut fuel := 16 * maxCandidates
  for property in properties.extract 0 32 do
    unless isResolved property do continue
    let some (_, lhs, rhs) := property.eq? | continue
    for (accumulator, target) in #[(lhs, rhs), (rhs, lhs)] do
      unless containsArgument accumulator arguments do continue
      if dependsOnArguments target arguments then continue
      let outputType ← inferType accumulator
      if !isResolved outputType || outputType.hasFVar then continue
      for id in (support target) do
        let input := mkFVar id
        let inputType ← inferType input
        unless ← listType inputType do continue
        for remaining in arguments do
          if remaining == input || (accumulator.find? (· == remaining)).isSome then continue
          if fuel == 0 then return out
          fuel := fuel - 1
          let remainingType ← inferType remaining
          if !isResolved remainingType || remainingType.hasFVar then continue
          unless ← isDefEq inputType remainingType do continue
          let rest := target.replaceFVar input remaining
          if !isResolved rest then continue
          unless ← isDefEq outputType (← inferType rest) do continue
          for (left, right) in #[(accumulator, rest), (rest, accumulator)] do
            let some completed ← compose? left right | continue
            let candidate ← instantiateMVars (← mkEq completed target)
            unless isResolved candidate do continue
            try check candidate
            catch e =>
              if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
              continue
            unless out.contains candidate do out := out.push candidate
            if out.size >= maxCandidates then return out
  return out

private structure Observation where
  accumulator : Expr
  target : Expr

private def observations (properties arguments : Array Expr) : MetaM (Array Observation) := do
  let mut out := #[]
  for property in properties.extract 0 32 do
    unless isResolved property do continue
    let some (_, lhs, rhs) := property.eq? | continue
    for (accumulator, target) in #[(lhs, rhs), (rhs, lhs)] do
      if containsArgument accumulator arguments && !dependsOnArguments target arguments then
        let type ← inferType accumulator
        if isResolved type && !type.hasFVar then out := out.push ⟨accumulator, target⟩
  return out

private def appendChecked (out : Array Expr) (candidate : Expr) : MetaM (Array Expr) := do
  appendCandidate out (← instantiateMVars candidate)

private structure Replacement where
  value : Expr
  slots : Array Expr
  changed : Nat

/-- Simultaneously vary at most two source inputs; keep function and type arguments fixed. -/
private def replacements (observation : Observation) (arguments : Array Expr)
    (scalars : Bool) (cap : Nat) : MetaM (Array Replacement) := do
  if cap == 0 then return #[]
  let mut choices : Array (Expr × Array Expr) := #[]
  for id in (support observation.target) do
    let input := mkFVar id
    let type ← whnf (← inferType input)
    unless isResolved type && !type.hasFVar do continue
    unless (← listType type) || (scalars && (type.isConstOf ``Nat || type.isConstOf ``Int)) do continue
    let mut slots := #[]
    for arg in arguments.extract 0 16 do
      if !isResolved arg || arg == input ||
          (observation.accumulator.find? (· == arg)).isSome then continue
      let argType ← inferType arg
      unless isResolved argType && !argType.hasFVar do continue
      if ← isDefEq type argType then slots := slots.push arg
    unless slots.isEmpty do choices := choices.push (input, slots)
    if choices.size == 4 then break
  let mut out := #[]
  -- Pair replacements precede singles so a narrow budget does not lose synchronization.
  for i in [:choices.size] do
    for j in [i + 1:choices.size] do
      let (x, xs) := choices[i]!
      let (y, ys) := choices[j]!
      for a in xs do
        for b in ys do
          if a == b then continue
          let value := observation.target.replaceFVars #[x, y] #[a, b]
          out := out.push ⟨value, #[a, b], 2⟩
          if out.size >= cap then return out
  for (x, slots) in choices do
    for slot in slots do
      out := out.push ⟨observation.target.replaceFVar x slot, #[slot], 1⟩
      if out.size >= cap then return out
  return out

private def algebraCompositions (left right : Expr) (multipleInputs : Bool)
    : MetaM (Array Expr) := do
  let type ← whnf (← inferType left)
  if type.isConstOf ``Bool then
    return #[mkApp2 (mkConst ``Bool.and) left right, mkApp2 (mkConst ``Bool.or) left right]
  if type.isConstOf ``Nat || type.isConstOf ``Int then
    let mul := if type.isConstOf ``Nat then ``Nat.mul else ``Int.mul
    let add := if type.isConstOf ``Nat then ``Nat.add else ``Int.add
    let product := mkApp2 (mkConst mul) left right
    return if multipleInputs then #[product, mkApp2 (mkConst add) left right] else #[product]
  if multipleInputs && (← listType type) then
    return #[← mkAppM ``List.append #[left, right]]
  return #[]

/-- Complete Boolean/numeric observations and synchronize multiple source inputs. -/
def algebraCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.filter isResolved
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  for observation in ← observations properties arguments do
    for replacement in ← replacements observation arguments true maxCandidates do
      for (left, right) in #[(observation.accumulator, replacement.value),
          (replacement.value, observation.accumulator)] do
        for completed in ← algebraCompositions left right (replacement.changed > 1) do
          if fuel == 0 then return out
          fuel := fuel - 1
          out ← appendChecked out (← mkEq completed observation.target)
          if out.size >= maxCandidates then return out
  return out

private def controlGuards (arguments : Array Expr) : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for arg in arguments.extract 0 16 do
    unless isResolved arg && arg.isFVar do continue
    let type ← whnf (← inferType arg)
    let test ← if type.isConstOf ``Bool then pure (some arg)
      else if type.isAppOfArity ``Option 1 then
        pure (some (← mkAppM ``Option.isSome #[arg]))
      else pure none
    if let some test := test then
      out := out.push (← mkEq test (mkConst ``Bool.true), ← mkEq test (mkConst ``Bool.false))
    if out.size == 4 then break
  return out

/-- A control state can distinguish pending completion from a completed result. -/
def guardedCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.filter isResolved
  let guards ← controlGuards arguments
  if guards.isEmpty then return #[]
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  for observation in ← observations properties arguments do
    let original ← mkEq observation.accumulator observation.target
    let pending ← candidates #[original] arguments maxCandidates
    for (yes, no) in guards do
      for completed in pending do
        for (active, stopped) in #[(yes, no), (no, yes)] do
          if fuel == 0 then return out
          fuel := fuel - 1
          out ← appendChecked out (← mkArrow active completed)
          if out.size >= maxCandidates then return out
          out ← appendChecked out (← mkArrow stopped original)
          if out.size >= maxCandidates then return out
  return out

/-- Compose an observed accumulator, a pending fragment, and the remaining source work. -/
def fragmentCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.filter isResolved
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  for observation in ← observations properties arguments do
    let type ← inferType observation.accumulator
    unless ← listType type do continue
    for replacement in ← replacements observation arguments false maxCandidates do
      for fragment in arguments.extract 0 16 do
        if replacement.slots.contains fragment ||
            (observation.accumulator.find? (· == fragment)).isSome then continue
        let fragmentType ← inferType fragment
        unless isResolved fragmentType && !fragmentType.hasFVar && (← isDefEq type fragmentType) do continue
        let acc := observation.accumulator
        let rest := replacement.value
        for parts in #[#[acc, fragment, rest], #[acc, rest, fragment],
            #[fragment, rest, acc], #[rest, fragment, acc]] do
          if fuel == 0 then return out
          fuel := fuel - 1
          let suffix ← mkAppM ``List.append #[parts[1]!, parts[2]!]
          let value ← mkAppM ``List.append #[parts[0]!, suffix]
          out ← appendChecked out (← mkEq value observation.target)
          if out.size >= maxCandidates then return out
  return out

private def aggregates (function worklist : Expr) (resultType : Expr) : MetaM (Array Expr) := do
  if resultType.isConstOf ``Bool then
    return #[← mkAppM ``List.any #[worklist, function],
      ← mkAppM ``List.all #[worklist, function]]
  let mapped ← mkAppM ``List.map #[function, worklist]
  if resultType.isConstOf ``Nat || resultType.isConstOf ``Int then
    return #[← mkAppM ``List.sum #[mapped]]
  if ← listType resultType then return #[← mkAppM ``List.flatten #[mapped]]
  return #[]

/-- Lift a source observation over pending values of its input type. -/
def worklistCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.filter isResolved
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  for observation in ← observations properties arguments do
    let outputType ← whnf (← inferType observation.accumulator)
    for id in (support observation.target).extract 0 8 do
      let input := mkFVar id
      let inputType ← inferType input
      if !isResolved inputType || inputType.hasFVar || (← isProp input) || (← whnf inputType).isSort then continue
      for todo in arguments.extract 0 16 do
        if fuel == 0 then return out
        fuel := fuel - 1
        let todoType ← whnf (← inferType todo)
        unless todoType.isAppOfArity ``List 1 && isResolved todoType && !todoType.hasFVar do continue
        if (observation.accumulator.find? (· == todo)).isSome then continue
        unless ← isDefEq inputType todoType.appArg! do continue
        let function ← withLocalDeclD `pending inputType fun value =>
          mkLambdaFVars #[value] (observation.target.replaceFVar input value)
        for remaining in ← aggregates function todo outputType do
          for (left, right) in #[(observation.accumulator, remaining),
              (remaining, observation.accumulator)] do
            let values ← if outputType.isConstOf ``Bool then
                algebraCompositions left right false
              else pure ((← compose? left right).toArray)
            for value in values do
              if fuel == 0 then return out
              fuel := fuel - 1
              out ← appendChecked out (← mkEq value observation.target)
              if out.size >= maxCandidates then return out
  return out

end PAScrape.Accumulate
