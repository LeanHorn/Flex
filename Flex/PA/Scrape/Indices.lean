import Flex.PA.Scrape.Core

/-! Absolute-index normalization and ordered-array prefixes. -/

open Lean Meta

namespace PAScrape.Structured

open PAScrape.Internal (indexedPredicates)

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
      let candidates ← indexedPredicates (mkConst ``Int) (some (mkIntLit 0)) (some bound) fun index => do
        let value := mkApp array index
        let mut candidates := #[]
        for target in #[bound, index, mkIntLit 0] do
          for relation in #[``LT.lt, ``LE.le] do
            let comparison ← mkAppM relation #[value, target]
            candidates := candidates.push comparison
        candidates := candidates.push (← mkEq value index)
        return candidates
      for candidate in candidates do
        if out.contains candidate then continue
        check candidate
        out := out.push candidate
        if out.size >= maxCandidates then return out
  return out

end PAScrape.Structured
