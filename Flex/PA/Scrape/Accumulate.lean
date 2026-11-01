import Flex.PA.Scrape.Guards

/-! Accumulator completion, guarded fragments, and worklist measures. -/

open Lean Meta

namespace PAScrape.Accumulate

open PAScrape.Internal (isResolved support containsArgument dependsOnArguments appendCandidate
  controlGuards guardStateCandidates)

private def listType (type : Expr) : MetaM Bool := do
  let type ← whnf type
  return isResolved type && !type.hasFVar && type.isAppOfArity ``List 1

private inductive CompletionMode where
  | basic
  | algebra (multipleInputs : Bool)
  | worklist

/-- Each mode chooses operations; the observed function itself is arbitrary. -/
private def operations (mode : CompletionMode) (type : Expr) : MetaM (Array Name) := do
  let type ← whnf type
  if type.isConstOf ``Bool then
    return match mode with
      | .basic => #[]
      | _ => #[``Bool.and, ``Bool.or]
  if type.isConstOf ``Nat || type.isConstOf ``Int then
    let add := if type.isConstOf ``Nat then ``Nat.add else ``Int.add
    let mul := if type.isConstOf ``Nat then ``Nat.mul else ``Int.mul
    return match mode with
      | .algebra true => #[mul, add]
      | .algebra false => #[mul]
      | _ => #[add]
  if ← listType type then
    return match mode with
      | .algebra false => #[]
      | _ => #[``List.append]
  return #[]

/-- Right-associated composition preserves the order of noncommutative pieces. -/
private def compose (operation : Name) (first : Expr) : List Expr → MetaM Expr
  | [] => pure first
  | next :: rest => do
    let right ← compose operation next rest
    if operation == ``List.append then return ← mkAppM operation #[first, right]
    return mkApp2 (mkConst operation) first right

private def completions (mode : CompletionMode) (first : Expr) (rest : List Expr)
    : MetaM (Array Expr) := do
  (← operations mode (← inferType first)).mapM fun op => compose op first rest

private def orders (accumulator remaining : Expr) (fragment : Option Expr := none)
    : Array (Expr × List Expr) :=
  match fragment with
  | none => #[(accumulator, [remaining]), (remaining, [accumulator])]
  | some fragment => #[(accumulator, [fragment, remaining]),
      (accumulator, [remaining, fragment]), (fragment, [remaining, accumulator]),
      (remaining, [fragment, accumulator])]

private structure Observation where
  accumulator : Expr
  target : Expr
  type : Expr

private def observation? (arguments : Array Expr) (accumulator target : Expr)
    : MetaM (Option Observation) := do
  unless containsArgument accumulator arguments && !dependsOnArguments target arguments do
    return none
  let type ← inferType accumulator
  if !isResolved type || type.hasFVar then return none
  return some ⟨accumulator, target, type⟩

private def observations (properties arguments : Array Expr) : MetaM (Array Observation) := do
  let mut out := #[]
  for property in properties.extract 0 32 do
    unless isResolved property do continue
    let some (_, lhs, rhs) := property.eq? | continue
    for (accumulator, target) in #[(lhs, rhs), (rhs, lhs)] do
      if let some observation ← observation? arguments accumulator target then
        out := out.push observation
  return out

private def appendChecked (out : Array Expr) (candidate : Expr) : MetaM (Array Expr) := do
  appendCandidate out (← instantiateMVars candidate)

/-- Propose a completed state or a remaining-work bound from one source property. -/
private def statefulPropertyCandidates (property : Expr) (changing snapshots : Array Expr)
    (maxCandidates : Nat) : MetaM (Array Expr) := do
  unless isResolved property do return #[]
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  if let some (_, lhs, rhs) := property.eq? then
    for (current, target) in #[(lhs, rhs), (rhs, lhs)] do
      unless changing.contains current && !dependsOnArguments target changing do continue
      let args := target.getAppArgs
      unless target.getAppFn.isConst do continue
      for i in [:args.size] do
        unless snapshots.contains args[i]! do continue
        unless ← isDefEq (← inferType args[i]!) (← inferType current) do continue
        for j in [i + 1:args.size] do
          let input := args[j]!
          unless snapshots.contains input && (← listType (← inferType input)) do continue
          for remaining in changing do
            if fuel == 0 then return out
            fuel := fuel - 1
            if remaining == current then continue
            unless ← isDefEq (← inferType remaining) (← inferType input) do continue
            let completed := mkAppN target.getAppFn ((args.set! i current).set! j remaining)
            out ← appendChecked out (← mkEq completed target)
            if out.size >= maxCandidates then return out
  let name := property.getAppFn.constName?.getD .anonymous
  let args := property.getAppArgs
  unless [``LE.le, ``Int.le, ``Nat.le].contains name && args.size >= 2 do return out
  let current := args[args.size - 2]!
  let target := args.back!
  unless changing.contains current && !dependsOnArguments target changing do return out
  let type ← whnf (← inferType current)
  unless type.isConstOf ``Int || type.isConstOf ``Nat do return out
  let measures ← IO.mkRef (#[] : Array Expr)
  discard <| Meta.transform target (pre := fun e => do
    let .app _ input := e | return .continue
    unless e.getAppFn.isConst && snapshots.contains input do return .continue
    if (← listType (← inferType input)) && (← isDefEq (← inferType e) type) then
      measures.modify (·.push e)
    return .continue)
  for measure in ← measures.get do
    for remaining in changing do
      if fuel == 0 then return out
      fuel := fuel - 1
      unless ← isDefEq (← inferType remaining) (← inferType measure.appArg!) do continue
      let pending := mkApp measure.appFn! remaining
      let sum := mkApp2 (mkConst (if type.isConstOf ``Int then ``Int.add else ``Nat.add)) current pending
      out ← appendChecked out (mkAppN property.getAppFn (args.set! (args.size - 2) sum))
      if out.size >= maxCandidates then return out
  return out

/-- Complete source calls using changing slots; preserve the original-state inputs.
Interleave properties so one source cannot consume the whole candidate budget. -/
def statefulCandidates (properties arguments : Array Expr) (stable : Array Bool)
    (maxCandidates : Nat := 16) : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 || stable.isEmpty then return #[]
  let slots := Array.range arguments.size
  let changing := (slots.filter fun i => !(stable[i]?.getD false)).map (arguments[·]!)
  let snapshots := (slots.filter fun i => stable[i]?.getD false).map (arguments[·]!)
  let groups ← (properties.extract 0 32).mapM fun property =>
    statefulPropertyCandidates property changing snapshots maxCandidates
  let mut out := #[]
  for i in [:maxCandidates] do
    for group in groups do
      if let some candidate := group[i]? then
        out ← appendChecked out candidate
        if out.size >= maxCandidates then return out
  return out

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
      let some observation ← observation? arguments accumulator target | continue
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
          unless ← isDefEq observation.type (← inferType rest) do continue
          for (first, tail) in orders accumulator rest do
            for completed in ← completions .basic first tail do
              out ← appendChecked out (← mkEq completed target)
              if out.size >= maxCandidates then return out
  return out

private structure RemainingWork where
  value : Expr
  slots : Array Expr
  changedInputs : Nat

/-- Simultaneously vary at most two source inputs; keep function and type arguments fixed. -/
private def replacements (observation : Observation) (arguments : Array Expr)
    (scalars : Bool) (cap : Nat) : MetaM (Array RemainingWork) := do
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

/-- Complete Boolean/numeric observations and synchronize multiple source inputs. -/
def algebraCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.filter isResolved
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  for observation in ← observations properties arguments do
    for work in ← replacements observation arguments true maxCandidates do
      for (first, tail) in orders observation.accumulator work.value do
        for completed in ← completions (.algebra (work.changedInputs > 1)) first tail do
          if fuel == 0 then return out
          fuel := fuel - 1
          out ← appendChecked out (← mkEq completed observation.target)
          if out.size >= maxCandidates then return out
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
    (out, fuel) ← guardStateCandidates guards original pending out fuel maxCandidates
    if out.size >= maxCandidates || fuel == 0 then return out
  return out

/-- Compose an observed accumulator, a pending fragment, and the remaining source work. -/
def fragmentCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.filter isResolved
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  for observation in ← observations properties arguments do
    let type := observation.type
    unless ← listType type do continue
    for work in ← replacements observation arguments false maxCandidates do
      for fragment in arguments.extract 0 16 do
        if work.slots.contains fragment ||
            (observation.accumulator.find? (· == fragment)).isSome then continue
        let fragmentType ← inferType fragment
        unless isResolved fragmentType && !fragmentType.hasFVar do continue
        unless ← isDefEq type fragmentType do continue
        for (first, tail) in orders observation.accumulator work.value (some fragment) do
          if fuel == 0 then return out
          fuel := fuel - 1
          let value ← compose ``List.append first tail
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

private def worklistResults (observation : Observation) (input inputType worklist : Expr)
    (resultType : Expr) : MetaM (Array Expr) := do
  let function ← withLocalDeclD `pending inputType fun value =>
    mkLambdaFVars #[value] (observation.target.replaceFVar input value)
  aggregates function worklist resultType

/-- Lift a source observation over pending values of its input type. -/
def worklistCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.filter isResolved
  let mut out := #[]
  let mut fuel := 32 * maxCandidates
  for observation in ← observations properties arguments do
    let outputType ← whnf observation.type
    for id in (support observation.target).extract 0 8 do
      let input := mkFVar id
      let inputType ← inferType input
      if !isResolved inputType || inputType.hasFVar then continue
      if (← isProp input) || (← whnf inputType).isSort then continue
      for todo in arguments.extract 0 16 do
        if fuel == 0 then return out
        fuel := fuel - 1
        let todoType ← whnf (← inferType todo)
        unless todoType.isAppOfArity ``List 1 && isResolved todoType && !todoType.hasFVar do continue
        if (observation.accumulator.find? (· == todo)).isSome then continue
        unless ← isDefEq inputType todoType.appArg! do continue
        for remaining in ← worklistResults observation input inputType todo outputType do
          for (first, tail) in orders observation.accumulator remaining do
            for value in ← completions .worklist first tail do
              if fuel == 0 then return out
              fuel := fuel - 1
              out ← appendChecked out (← mkEq value observation.target)
              if out.size >= maxCandidates then return out
  return out

end PAScrape.Accumulate
