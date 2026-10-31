import Flex.PA.Scrape.Core

/-! Quantified regions, collection prefixes, and relational candidates. -/

open Lean Meta

namespace PAScrape.Regions

open PAScrape.Internal (isResolved support dependsOnArguments appendCandidate)

private def add (out : Array Expr) (e : Expr) (cap : Nat) : MetaM (Array Expr) := do
  if out.size >= cap then return out
  appendCandidate out e

private def numeric (e : Expr) : MetaM Bool := do
  if !isResolved e then return false
  let type ← whnf (← inferType e)
  return type.isConstOf ``Nat || type.isConstOf ``Int

private def bounds (arguments : Array Expr) : MetaM (Array Expr) :=
  arguments.filterM fun e => do
    return isResolved e && (← whnf (← inferType e)).isConstOf ``Nat

private def replace (e source target : Expr) : Expr :=
  e.replace fun sub => if sub == source then some target else none

private def listValue (e : Expr) : MetaM Bool := do
  if !isResolved e then return false
  let type ← whnf (← inferType e)
  return !type.hasFVar && type.isAppOfArity ``List 1

private partial def endpoints (e : Expr) (arguments : Array Expr)
    (bound : FVarIdSet := {}) : StateT Nat MetaM (Array Expr) := do
  if (← get) == 0 then return #[]
  modify (· - 1)
  let e := e.consumeMData.headBeta
  let mut out := #[]
  if e.hasFVar && (!dependsOnArguments e arguments || arguments.contains e) &&
      !(support e).any bound.contains && (← numeric e) then
    out := out.push e
  match e with
  | .forallE name type body bi | .lam name type body bi =>
    out := out ++ (← endpoints type arguments bound)
    return ← withLocalDecl name bi type fun x => do
      return out ++ (← endpoints (body.instantiate1 x) arguments (bound.insert x.fvarId!))
  | .app .. =>
    for arg in e.getAppArgs.reverse do
      if (← get) == 0 then break
      out := out ++ (← endpoints arg arguments bound)
  | .letE _ _ value body _ => return ← endpoints (body.instantiate1 value) arguments bound
  | .proj _ _ value => out := out ++ (← endpoints value arguments bound)
  | _ => pure ()
  return out

/-- Vary source endpoints under binders, or restrict an indexed property by a prefix guard. -/
def regionCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.extract 0 16
  let slots ← arguments.filterM numeric
  let mut families := #[]
  for property in properties.extract 0 24 do
    if families.size >= maxCandidates then break
    if !isResolved property || !(← isProp property) then continue
    unless (property.find? Expr.isForall).isSome do continue
    let (sources, _) ← (endpoints property arguments).run 256
    let mut candidates := #[]
    let mut attempts := 128
    for source in sources do
      if candidates.size >= maxCandidates || attempts == 0 then break
      for slot in slots do
        if candidates.size >= maxCandidates || attempts == 0 then break
        attempts := attempts - 1
        if source == slot then continue
        unless ← isDefEq (← inferType source) (← inferType slot) do continue
        candidates ← add candidates (replace property source slot) maxCandidates
    if let .forallE name type body bi := property.consumeMData then
      if type.isConstOf ``Nat || type.isConstOf ``Int then
        for slot in slots do
          if candidates.size >= maxCandidates || attempts == 0 then break
          attempts := attempts - 1
          unless ← isDefEq type (← inferType slot) do continue
          let candidate ← withLocalDecl name bi type fun index => do
            let guard ← mkAppM ``LT.lt #[index, slot]
            mkForallFVars #[index] (← mkArrow guard (body.instantiate1 index))
          candidates ← add candidates candidate maxCandidates
    unless candidates.isEmpty do families := families.push candidates
  let mut out := #[]
  for i in [:maxCandidates] do
    for family in families do
      if let some candidate := family[i]? then out ← add out candidate maxCandidates
      if out.size >= maxCandidates then return out
  return out

private partial def listInputs (e : Expr) (arguments : Array Expr)
    : StateT Nat MetaM (Array Expr) := do
  if (← get) == 0 then return #[]
  modify (· - 1)
  let e := e.consumeMData.headBeta
  if !isResolved e then return #[]
  if (e.isFVar || e.isAppOfArity ``Array.toList 2) &&
      !dependsOnArguments e arguments && (← listValue e) then return #[e]
  let mut out := #[]
  for arg in e.getAppArgs do
    if (← get) == 0 then break
    for input in ← listInputs arg arguments do
      unless out.contains input do out := out.push input
  return out

private def slices (list : Expr) (indices : Array Expr) (cap : Nat) : MetaM (Array Expr) := do
  let mut out := #[]
  for index in indices.extract 0 (min 4 cap) do
    out := out.push (← mkAppM ``List.take #[index, list])
  return out

/-- Observe a source function on a processed prefix; keep unread array regions unchanged. -/
def prefixCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.extract 0 16
  let indices ← bounds arguments
  let mut out := #[]
  for property in properties.extract 0 24 do
    unless isResolved property do continue
    if let some (_, lhs, rhs) := property.eq? then
      for (observed, target) in #[(lhs, rhs), (rhs, lhs)] do
        unless dependsOnArguments observed arguments && !dependsOnArguments target arguments do continue
        let (inputs, _) ← (listInputs target arguments).run 128
        for input in inputs.extract 0 4 do
          for part in ← slices input indices (maxCandidates - out.size) do
            out ← add out (← mkEq observed (replace target input part)) maxCandidates
            if out.size >= maxCandidates then return out
    if out.size >= maxCandidates then return out
  -- Frames are proposed only between arrays already occurring in the source.
  let mut inputs := #[]
  let mut attempts := 128
  for property in properties.extract 0 24 do
    if inputs.size >= 4 || attempts == 0 then break
    for id in (support property) do
      if inputs.size >= 4 || attempts == 0 then break
      attempts := attempts - 1
      let input := mkFVar id
      if dependsOnArguments input arguments || inputs.contains input then continue
      let type ← whnf (← inferType input)
      if type.isAppOfArity ``Array 1 then inputs := inputs.push input
  for array in arguments do
    if attempts == 0 then return out
    if !isResolved array then continue
    attempts := attempts - 1
    let type ← whnf (← inferType array)
    unless type.isAppOfArity ``Array 1 do continue
    for input in inputs.extract 0 4 do
      if attempts == 0 then return out
      attempts := attempts - 1
      unless ← isDefEq type (← inferType input) do continue
      for bound in indices.extract 0 4 do
        let candidate ← withLocalDeclD `index (mkConst ``Nat) fun index => do
          let guard ← mkAppM ``LE.le #[bound, index]
          let current ← mkAppM ``GetElem?.getElem? #[array, index]
          let original ← mkAppM ``GetElem?.getElem? #[input, index]
          mkForallFVars #[index] (← mkArrow guard (← mkEq current original))
        out ← add out candidate maxCandidates
        if out.size >= maxCandidates then return out
  return out

private partial def relations (e : Expr) : StateT Nat MetaM (Array Expr) := do
  if (← get) == 0 then return #[]
  modify (· - 1)
  let e := e.consumeMData.headBeta
  if !isResolved e then return #[]
  if e.isAppOfArity ``List.Pairwise 3 || e.isAppOfArity ``List.Perm 3 then return #[e]
  let mut out := #[]
  for arg in e.getAppArgs do
    if (← get) == 0 then break
    out := out ++ (← relations arg)
  return out

/-- Restrict source list relations to prefixes, and compare output with consumed input regions. -/
def relationalCandidates (properties arguments : Array Expr) (maxCandidates : Nat := 16)
    : MetaM (Array Expr) := withNewMCtxDepth do
  if maxCandidates == 0 then return #[]
  let arguments := arguments.extract 0 16
  let indices ← bounds arguments
  let mut out := #[]
  let mut attempts := 128
  for property in properties.extract 0 24 do
    let (found, _) ← (relations property).run 128
    for relation in found do
      let args := relation.getAppArgs
      let list := args[2]!
      if relation.isAppOfArity ``List.Pairwise 3 && dependsOnArguments list arguments then
        for index in indices.extract 0 4 do
          for op in #[``List.take, ``List.drop] do
            if out.size >= maxCandidates || attempts == 0 then return out
            attempts := attempts - 1
            let part ← mkAppM op #[index, list]
            out ← add out (mkAppN relation.getAppFn (args.set! 2 part)) maxCandidates
      if relation.isAppOfArity ``List.Perm 3 then
        for (current, original) in #[(args[1]!, args[2]!), (args[2]!, args[1]!)] do
          unless dependsOnArguments current arguments && !dependsOnArguments original arguments do continue
          let (inputs, _) ← (listInputs original arguments).run 128
          let mut variants := #[original]
          -- At most two source inputs are varied together, with a shared work budget.
          for input in inputs.extract 0 2 do
            let mut next := #[]
            for base in variants do
              if out.size >= maxCandidates || attempts == 0 then return out
              for part in ← slices input indices (maxCandidates - out.size) do
                if out.size >= maxCandidates || attempts == 0 then return out
                attempts := attempts - 1
                let changed := replace base input part
                next := next.push changed
                out ← add out (← mkAppM ``List.Perm #[current, changed]) maxCandidates
            variants := next.extract 0 16
      if out.size >= maxCandidates then return out
  return out

end PAScrape.Regions
