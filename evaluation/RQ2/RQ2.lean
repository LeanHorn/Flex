import Flex.Tactic.Tactics.Flex

set_option maxHeartbeats 0
set_option Elab.async false

open Lean Meta Elab Term Tactic

namespace RQ2

private def emit (fields : List (String × Json)) : IO Unit :=
  IO.println ("RQ2 " ++ (Json.mkObj fields).compress)

private def expressionDepth (root : Expr) : Nat := Id.run do
  let children : Expr → List Expr
    | .app f a => [f, a]
    | .lam _ t b _ | .forallE _ t b _ => [t, b]
    | .letE _ t v b _ => [t, v, b]
    | .mdata _ e | .proj _ _ e => [e]
    | _ => []
  let mut depths : Std.HashMap Expr Nat := {}
  let mut pending := [(root, false)]
  while let (e, visited) :: rest := pending do
    pending := rest
    if depths.contains e then continue
    if visited then
      depths := depths.insert e (1 + (children e).foldl (fun n c => max n (depths[c]!)) 0)
    else
      pending := (children e).map (·, false) ++ (e, true) :: pending
  return depths[root]!

/-- Use the same dependency graph and feedback cut as Zap, before any search. -/
private def classify (target : Expr) : TacticM Json := do
  let original ← mkFreshExprMVar target (kind := .syntheticOpaque)
  let goal ← Flex.Preprocess.prepareGoal original.mvarId!
  if ← goal.isAssignedOrDelayedAssigned then
    return Json.mkObj [("kind", toJson "none"), ("eligible", toJson false)]
  let result ← IO.mkRef Json.null
  withPeeledExists (← goal.getType) #[] fun binders body => do
    let mut body := body
    let mut vars : Array KVar := #[]
    for (name, ty, fv) in binders do
      let types ← collectArrowTypes ty
      let mv ← mkFreshExprMVar ty (kind := .syntheticOpaque)
      vars := vars.push {
        name := name
        paramTypes := types
        params := (List.range types.length).map (fun i => Name.mkSimple s!"x{i}")
        mvarId := mv.mvarId! }
      body := body.replaceFVar fv mv
    let ctx : KContext := { kvars := vars.foldl (fun m k => m.insert k.mvarId k) {} }
    let deps ← (exprDeps body).run ctx
    let (elim, cut) ← (exprPartitionKVars body).run ctx
    let cyclic := (tarjanSCC vars.toList deps).filter fun scc =>
      scc.length > 1 || scc.any (fun k => hasSelfLoop k deps)
    let ncyclic := cyclic.flatten.length
    let acyclic := vars.size - ncyclic
    let kind := if vars.isEmpty then "none" else if ncyclic == 0 then "acyclic_only"
      else if acyclic == 0 then "cyclic_only" else "mixed"
    result.set (Json.mkObj [
      ("kind", toJson kind), ("predicates", toJson vars.size),
      ("acyclic", toJson acyclic), ("cyclic", toJson ncyclic),
      ("eliminable", toJson elim.length), ("cut", toJson cut.length),
      ("eligible", toJson (acyclic > 0 && !elim.isEmpty)),
      ("elimination_names", toJson (elim.map (toString ∘ KVar.name))),
      ("cut_names", toJson (cut.map (toString ∘ KVar.name)))])
  result.get

/-- Measure a closed proof of residuals → original, without admitting the residuals. -/
private def certificate (original target : Expr) (goals : List MVarId) : TermElabM Json := do
  let goals ← goals.toArray.mapM (·.revertAll)
  let types ← goals.mapM fun g => do instantiateMVars (← g.getType)
  for type in types do
    if type.hasMVar || type.hasFVar || type.hasLooseBVars then
      throwError "unclosed residual"
  let names := Array.ofFn (n := types.size) fun ⟨i, _⟩ => Name.mkSimple s!"residual{i}"
  withLocalDeclsDND (names.zip types) fun hs => do
    for g in goals, h in hs do g.assign h
    let proof ← mkLambdaFVars hs (← instantiateMVars original)
    let type ← mkForallFVars hs target
    if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "incomplete reduction proof"
    let start ← IO.monoNanosNow
    withoutModifyingEnv <| addDecl (.thmDecl {
      name := ← mkFreshUserName `rq2_certificate, levelParams := [], type, value := proof })
    let elapsed := (← IO.monoNanosNow) - start
    for name in proof.getUsedConstants do
      for axiomName in ← collectAxioms name do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
          throwError "unexpected axiom: {axiomName}"
    return Json.mkObj [("depth", toJson (expressionDepth proof)),
      ("approx_depth", toJson proof.approxDepth.toNat),
      ("constants", toJson proof.getUsedConstants.size), ("kernel_ns", toJson elapsed),
      ("kernel_checked", toJson true), ("residual_goals", toJson goals.size)]

private def envNat (name : String) (default : Nat) : IO Nat := do
  return ((← IO.getEnv name).bind String.toNat?).getD default

def run (name : Name) (id : String) : TermElabM Unit := do
  let saved ← saveState
  let mode := (← IO.getEnv "RQ2_MODE").getD "classify"
  let variant := (← IO.getEnv "RQ2_VARIANT").getD "zap"
  let heartbeats ← envNat "RQ2_HEARTBEATS" 200000
  let timeout ← envNat "RQ2_TIMEOUT" 60
  let recursion ← envNat "RQ2_RECURSION" 4096
  let fieldsRef ← IO.mkRef [("case", toJson id), ("variant", toJson variant)]
  try
    withOptions (fun o => (flex.benchPhases.set o (mode != "classify"))
        |>.setBool `trace.flex (mode != "classify")) <|
      withTheReader Core.Context (fun c => { c with maxRecDepth := recursion, maxHeartbeats := 0 }) do
        let target := Lean.mkConst name
        let fields ← fieldsRef.get
        if mode == "classify" then
          let result ← IO.mkRef Json.null
          let g ← mkFreshExprMVar target
          discard <| Tactic.run g.mvarId! do result.set (← classify target)
          let classification ← result.get
          emit (fields ++ [("status", toJson "classified"), ("classification", classification)])
        else
          let strategy ← match variant with
            | "zap" => pure Flex.Portfolio.ZapCertificate.constructive
            | "zap_grind" => pure .grind
            | "zap_aesop" => pure .aesop
            | _ => throwError "unknown variant {variant}"
          let original ← mkFreshExprMVar target (kind := .syntheticOpaque)
          let events ← IO.mkRef (#[] : Array Flex.Portfolio.PhaseEvent)
          let zapStart ← IO.mkRef (0, 0)
          let zapCost ← IO.mkRef (0, 0)
          let start ← IO.monoNanosNow
          let h0 ← IO.getNumHeartbeats
          let goals ← Tactic.run original.mvarId! do
            Flex.Portfolio.flexImpl {
              config := {
                zapCertificate := strategy
                postprocess := false
                nesting := false
                closeLeaves := false
                splitFree := false
                zapHeartbeats := heartbeats
                totalTimeout := timeout }
              backends := []
              onPhase := fun e => do
                if e.phase == "zap" then
                  let now ← IO.monoNanosNow
                  let hb ← IO.getNumHeartbeats
                  if e.status == "start" then zapStart.set (now, hb)
                  else
                    let (t, h) ← zapStart.get
                    zapCost.set (now - t, hb - h)
                events.modify (·.push e) }
          let h1 ← IO.getNumHeartbeats
          let stop ← IO.monoNanosNow
          let phases := (← events.get).filter (·.status != "start")
          let zapOk := phases.any fun e => e.phase == "zap" && e.status == "ok"
          let (zapNs, zapHb) ← zapCost.get
          let fields := fields ++ [("tactic_ns", toJson (stop - start)),
            ("zap_ns", toJson zapNs), ("zap_heartbeats_raw", toJson zapHb),
            ("heartbeats_raw", toJson (h1 - h0)),
            ("heartbeats", toJson ((h1 - h0) / 1000)),
            ("phases", toJson (phases.map fun e => Json.mkObj [
              ("phase", toJson e.phase), ("status", toJson e.status),
              ("ms", toJson e.elapsedMs)]))]
          fieldsRef.set fields
          if !zapOk then
            emit (fields ++ [("status", toJson "not_reduced")])
          else
            emit (fields ++ [("status", toJson "constructed")])
            let metrics ← certificate original target goals
            emit (fields ++ [("status", toJson "certified"), ("certificate", metrics)])
  catch e =>
    emit ((← fieldsRef.get) ++ [("status", toJson "error"), ("error", toJson (← e.toMessageData.toString))])
  finally
    saved.restore

end RQ2
