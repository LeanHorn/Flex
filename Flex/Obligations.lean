import Lean

/-! Optional provenance markers for certified predicate-head obligations.

When `flex.logObligations` is set, each head obligation that a certificate walker
visits leaves an unassigned marker metavariable whose user name records the head
predicate, the predicates among its hypotheses, and whether the head was proved.
Markers live in the metavariable context, so they survive exactly when the state
that produced them is kept: abandoned attempts roll them back with everything else.
They never enter a proof term. -/

open Lean Meta

register_option flex.logObligations : Bool := {
  defValue := false
  descr := "Leave a marker metavariable for each visited predicate-head obligation."
}

register_option flex.oracleCall : Nat := {
  defValue := 0
  descr := "Internal: identifies the proof-oracle call that budget-failure markers belong to."
}

namespace Flex.Obligations

/-- User-name prefix of obligation markers. -/
def markerPrefix : String := "flex_obligation:"

/-- Record one head obligation when logging is enabled. -/
def record (backend : String) (head : Name) (hypotheses : List Name) (proved : Bool) :
    MetaM Unit := do
  unless flex.logObligations.get (← getOptions) do return
  let payload := Json.mkObj [
    ("kind", toJson "head"), ("backend", toJson backend), ("head", toJson head.toString),
    ("hypotheses", toJson (hypotheses.eraseDups.map (·.toString))),
    ("proved", toJson proved)]
  mark payload

where
  mark (payload : Json) : MetaM Unit :=
    discard <| mkFreshExprMVar (some (mkConst ``True))
      (userName := Name.mkSimple (markerPrefix ++ payload.compress))

/-- Record a query constraint (no predicate in its conclusion) whose hypotheses mention
`hypotheses`. When `goal` is given, the constraint was left as that goal, and whether it was
later proved is read from the goal's assignment at the end of the run. -/
def recordQuery (backend : String) (hypotheses : List Name) (goal : Option MVarId) :
    MetaM Unit := do
  unless flex.logObligations.get (← getOptions) do return
  record.mark (Json.mkObj [
    ("kind", toJson "query"), ("backend", toJson backend),
    ("hypotheses", toJson (hypotheses.eraseDups.map (·.toString))),
    ("goal", match goal with | some id => toJson id.name.toString | none => Json.null),
    ("proved", toJson goal.isNone)])

/-- Record that a proof attempt inside oracle call `call` stopped at a resource limit
(`reason`), so more budget might have proved its goal. -/
def recordLimit (reason : String) : MetaM Unit := do
  unless flex.logObligations.get (← getOptions) do return
  record.mark (Json.mkObj [("kind", toJson "limit"), ("reason", toJson reason),
    ("call", toJson (flex.oracleCall.get (← getOptions)))])

/-- Record that oracle call `call` left its goal unproved. -/
def recordUnproved (call : Nat) : MetaM Unit := do
  unless flex.logObligations.get (← getOptions) do return
  record.mark (Json.mkObj [("kind", toJson "unproved"), ("call", toJson call)])

/-- All markers in the current metavariable context, as JSON payloads. -/
def collect : MetaM (Array Json) := do
  let mut out := #[]
  for (_, decl) in (← getMCtx).decls do
    let name := decl.userName
    if let .str .anonymous text := name then
      if text.startsWith markerPrefix then
        if let .ok json := Json.parse (text.replace markerPrefix "") then
          out := out.push json
  return out

/-- Re-create markers from `kept` that a state rollback removed, so a step that is
undone still reports what it tried. -/
def reinstate (kept : Array Json) : MetaM Unit := do
  unless flex.logObligations.get (← getOptions) do return
  let mut present : Std.HashMap String Nat := {}
  for marker in ← collect do
    present := present.alter marker.compress fun n => some (n.getD 0 + 1)
  for marker in kept do
    let key := marker.compress
    match present[key]? with
    | some (n + 1) => present := present.insert key n
    | _ => record.mark marker

end Flex.Obligations
