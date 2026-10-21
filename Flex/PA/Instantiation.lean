import Lean
import Flex.PA.Qualifier

open Lean Meta

/-- Collect the qualifier's parameter types. -/
private partial def qualifParamTypes (ty : Expr) : List Expr :=
  if ty.isForall then ty.bindingDomain! :: qualifParamTypes ty.bindingBody!
  else []

private def visitAssignments {α}
    (visit : α → List Nat → MetaM (α × Bool))
    : List (Array Nat) → List Nat → α → MetaM (α × Bool)
  | [], selected, state => visit state selected.reverse
  | choices :: rest, selected, state => do
    let mut state := state
    for slot in choices do
      if selected.contains slot then continue
      let (next, keepGoing) ← visitAssignments visit rest (slot :: selected) state
      state := next
      unless keepGoing do return (state, false)
    return (state, true)

/-- Visit compatible assignments without repeating slots. The callback returns
    `false` to stop; assignments are visited in slot order. -/
def foldQualifierInstances {α} (q : Expr) (kvarParamTypes : List Expr)
    (init : α) (visit : α → List Nat → MetaM (α × Bool)) : MetaM α := do
  let paramTypes := qualifParamTypes (← inferType q)
  let slots := kvarParamTypes.toArray
  if paramTypes.length > slots.size then return init
  let choices ← paramTypes.mapM fun ty => do
    let mut compatible := #[]
    for i in [:slots.size] do
      if ← isDefEq ty slots[i]! then
        compatible := compatible.push i
    return compatible
  return (← visitAssignments visit choices [] init).1

/-- Instantiate `q` over compatible, distinct κ slots, up to the optional limit. -/
def instantiateQualifier
    (q : Expr) (kvarParamTypes : List Expr)
    (maxCandidates : Option Nat := none)
    : MetaM (Array (Expr × List Nat)) := do
  if maxCandidates == some 0 then return #[]
  foldQualifierInstances q kvarParamTypes #[] fun out slots => do
    let out := out.push (q, slots)
    return (out, !maxCandidates.any (out.size >= ·))
