import Flex.Tactic.Tactics.Flex
import Flex.CHC.ModelImport

set_option maxHeartbeats 0
set_option Elab.async false

open Lean Meta Elab Term Tactic

namespace RQ2

private def emit (fields : List (String × Json)) : IO Unit :=
  IO.println ("RQ2 " ++ (Json.mkObj fields).compress)

private def children : Expr → List Expr
  | .app f a => [f, a]
  | .lam _ t b _ | .forallE _ t b _ => [t, b]
  | .letE _ t v b _ => [t, v, b]
  | .mdata _ e | .proj _ _ e => [e]
  | _ => []

/-- Follow generated helpers, stopping at declarations present before the trial. -/
private def proofPackage (baseline : Environment) (roots : Array Expr)
    : TermElabM (Array ConstantInfo) := do
  let env ← getEnv
  let mut states : Std.HashMap Name Nat := {}
  let mut pending := roots.toList.flatMap (fun e => e.getUsedConstants.toList.map (·, false))
  let mut ordered := #[]
  while let (name, visited) :: rest := pending do
    pending := rest
    if baseline.contains name || states[name]? == some 2 then continue
    let some info := env.find? name | throwError "missing proof dependency {name}"
    if visited then
      states := states.insert name 2
      ordered := ordered.push info
    else
      if states[name]? == some 1 then throwError "cyclic generated proof dependency {name}"
      let some value := info.value? true | throwError "unsupported generated proof dependency {name}"
      states := states.insert name 1
      let deps := info.type.getUsedConstants.toList ++ value.getUsedConstants.toList
      pending := deps.map (·, false) ++ (name, true) :: pending
  return ordered

/-- DAG metrics: new helper types and bodies are included without materializing expansions. -/
private def expressionStats (roots : Array Expr) (helpers : Array ConstantInfo)
    : Nat × Nat × Nat := Id.run do
  let values : Std.HashMap Name (List Expr) := helpers.foldl (fun m info =>
    m.insert info.name [info.type, info.value! true]) {}
  let descendants := fun (e : Expr) => match e with
    | .const name _ => values.getD name []
    | _ => children e
  let mut depths : Std.HashMap Expr Nat := {}
  let mut constants : NameSet := {}
  let mut pending := roots.toList.map (·, false)
  while let (e, visited) :: rest := pending do
    pending := rest
    if depths.contains e then continue
    if visited then
      depths := depths.insert e (1 + (descendants e).foldl (fun n c => max n (depths[c]!)) 0)
      if let .const name _ := e then constants := constants.insert name
    else
      pending := (descendants e).map (·, false) ++ (e, true) :: pending
  return (roots.foldl (fun n e => max n (depths[e]!)) 0, depths.size, constants.size)

private def replayDeclaration : ConstantInfo → TermElabM Declaration
  | .thmInfo value => pure (.thmDecl value)
  | .defnInfo value => pure (.defnDecl value)
  | .opaqueInfo value => pure (.opaqueDecl value)
  | info => throwError "cannot replay generated declaration {info.name}"

/-- Prepare once per invocation, with identical limits in classification and measurement. -/
private def prepare (goal : MVarId) (heartbeats seconds : Nat) : TermElabM MVarId := do
  let result ← IO.mkRef goal
  let now ← IO.monoMsNow
  let deadline := if seconds == 0 then none else some (now + seconds * 1000)
  let _ ← Tactic.run goal do
    let action := withTheReader Core.Context (fun c => { c with maxHeartbeats := heartbeats * 1000 }) do
      Core.withCurrHeartbeats do
        let next ← Flex.Preprocess.prepareGoal goal
        result.set next
        setGoals (if ← next.isAssignedOrDelayedAssigned then [] else [next])
    let some () ← Flex.Timeout.run deadline action
      | throwError "preprocessing wall-clock budget exhausted"
  result.get

/-- Find predicate goals under positive quantifiers and conjunctions after preparation. -/
private partial def kGoals (goal : MVarId) : MetaM (List MVarId) := do
  if ← goal.isAssignedOrDelayedAssigned then return []
  goal.withContext do
    let type ← whnf (← instantiateMVars (← goal.getType))
    if let .app (.app (.const ``Exists _) domain) _ := type then
      if ← forallTelescopeReducing domain fun _ body => return body.isProp then
        return [goal]
    if type.isForall then
      let (_, child) ← goal.intro1
      kGoals child
    else if type.isAppOfArity ``And 2 then
      (← goal.apply (mkConst ``And.intro)).foldlM (fun acc g => return acc ++ (← kGoals g)) []
    else return []

/-- Use the same dependency graph and feedback cut as Zap, before any search.
Counts are summed over every predicate goal, matching one Zap run per goal. -/
private def classify (goal : MVarId) : TacticM Json := do
  let goals ← kGoals goal
  let (predicates, ncyclic, elim, cut) ← goals.foldlM (init := (0, 0, [], [])) fun acc goal =>
      goal.withContext do
    let result ← IO.mkRef acc
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
      let (e, c) ← (exprPartitionKVars body).run ctx
      let cyclic := (tarjanSCC vars.toList deps).filter fun scc =>
        scc.length > 1 || scc.any (fun k => hasSelfLoop k deps)
      let (p, n, es, cs) := acc
      result.set (p + vars.size, n + cyclic.flatten.length, es ++ e, cs ++ c)
    result.get
  let acyclic := predicates - ncyclic
  let kind := if predicates == 0 then "none" else if ncyclic == 0 then "acyclic_only"
    else if acyclic == 0 then "cyclic_only" else "mixed"
  return Json.mkObj [
    ("kind", toJson kind), ("predicates", toJson predicates), ("predicate_goals", toJson goals.length),
    ("acyclic", toJson acyclic), ("cyclic", toJson ncyclic),
    ("eliminable", toJson elim.length), ("cut", toJson cut.length),
    ("eligible", toJson (acyclic > 0 && !elim.isEmpty)),
    ("elimination_names", toJson (elim.map (toString ∘ KVar.name))),
    ("cut_names", toJson (cut.map (toString ∘ KVar.name)))]

/-- Check residuals → original together with every generated auxiliary dependency. -/
private def certificate (baseline : Environment) (original target : Expr)
    (goals : List MVarId) : TermElabM Json := do
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
    let helpers ← proofPackage baseline #[type, proof]
    let declarations ← helpers.mapM replayDeclaration
    let finalDecl := Declaration.thmDecl {
      name := ← mkFreshUserName `rq2_certificate, levelParams := [], type, value := proof }
    let context ← readThe Core.Context
    let opts := maxRecDepth.set (maxHeartbeats.set
      ((← getOptions).setBool `debug.skipKernelTC false) 0) context.maxRecDepth
    let cancel := context.cancelTk?
    let start ← IO.monoNanosNow
    let mut kernel := baseline.toKernelEnv
    for declaration in declarations.push finalDecl do
      match kernel.addDecl opts declaration cancel with
      | .ok next => kernel := next
      | .error error => throwError "kernel rejected proof package: {error.toMessageData opts}"
    let elapsed := (← IO.monoNanosNow) - start
    for expr in #[type, proof] do
      for name in expr.getUsedConstants do
        for axiomName in ← collectAxioms name do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unexpected axiom: {axiomName}"
    let (depth, nodes, constants) := expressionStats #[type, proof] helpers
    let (directDepth, directNodes, directConstants) := expressionStats #[proof] #[]
    return Json.mkObj [("depth", toJson depth), ("nodes", toJson nodes),
      ("constants", toJson constants), ("auxiliary_declarations", toJson helpers.size),
      ("auxiliary_names", toJson (helpers.map (toString ∘ ConstantInfo.name))),
      ("direct_depth", toJson directDepth), ("direct_nodes", toJson directNodes),
      ("direct_constants", toJson directConstants), ("approx_depth", toJson proof.approxDepth.toNat),
      ("kernel_ns", toJson elapsed), ("kernel_checked", toJson true),
      ("residual_goals", toJson goals.size), ("metrics_version", toJson (2 : Nat))]

private def envNat (name : String) (default : Nat) : IO Nat := do
  return ((← IO.getEnv name).bind String.toNat?).getD default

def run (name : Name) (id : String) : TermElabM Unit := do
  let saved ← saveState
  let mode := (← IO.getEnv "RQ2_MODE").getD "classify"
  let variant := (← IO.getEnv "RQ2_VARIANT").getD "zap"
  let heartbeats ← envNat "RQ2_HEARTBEATS" 200000
  let timeout ← envNat "RQ2_TIMEOUT" 60
  let prepareHeartbeats ← envNat "RQ2_PREPARE_HEARTBEATS" 2000000
  let prepareTimeout ← envNat "RQ2_PREPARE_TIMEOUT" 120
  let recursion ← envNat "RQ2_RECURSION" 4096
  let fieldsRef ← IO.mkRef [("case", toJson id), ("variant", toJson variant)]
  let failureStatus ← IO.mkRef "preparation_failed"
  try
    withOptions (fun o => (flex.benchPhases.set o (mode != "classify"))
        |>.setBool `trace.flex (mode != "classify")) do
      withTheReader Core.Context (fun c => { c with maxRecDepth := recursion, maxHeartbeats := 0 }) do
        let baseline ← getEnv
        let target := Lean.mkConst name
        let original ← mkFreshExprMVar target (kind := .syntheticOpaque)
        let prepStart ← IO.monoNanosNow
        let prepHB ← IO.getNumHeartbeats
        let goal ← try prepare original.mvarId! prepareHeartbeats prepareTimeout
          finally
            let elapsed := (← IO.monoNanosNow) - prepStart
            let used := (← IO.getNumHeartbeats) - prepHB
            fieldsRef.modify (· ++ [("prepare_ns", toJson elapsed), ("prepare_heartbeats_raw", toJson used)])
        let prepared ← instantiateMVars (← goal.getType)
        fieldsRef.modify (· ++ [("prepared_hash", toJson (hash prepared).toNat)])
        failureStatus.set "error"
        if mode == "classify" then
          let result ← IO.mkRef Json.null
          let _ ← Tactic.run goal do result.set (← classify goal)
          let classification ← result.get
          emit ((← fieldsRef.get) ++ [("status", toJson "classified"), ("classification", classification)])
        else
          let strategy ← match variant with
            | "zap" => pure Flex.Portfolio.ZapCertificate.constructive
            | "zap_grind" => pure .grind
            | "zap_aesop" => pure .aesop
            | _ => throwError "unknown variant {variant}"
          let events ← IO.mkRef (#[] : Array Flex.Portfolio.PhaseEvent)
          let zapStart ← IO.mkRef (0, 0)
          let zapCost ← IO.mkRef (0, 0)
          let start ← IO.monoNanosNow
          let h0 ← IO.getNumHeartbeats
          let goals ← Tactic.run goal do
            Flex.Portfolio.flexImpl {
              config := {
                preprocess := false
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
                    zapCost.modify fun (totalNs, totalHb) => (totalNs + now - t, totalHb + hb - h)
                events.modify (·.push e) }
          let h1 ← IO.getNumHeartbeats
          let stop ← IO.monoNanosNow
          let phases := (← events.get).filter (·.status != "start")
          let zapOk := phases.any fun e => e.phase == "zap" && e.status == "ok"
          let (zapNs, zapHb) ← zapCost.get
          let fields := (← fieldsRef.get) ++ [("tactic_ns", toJson (stop - start)),
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
            let metrics ← certificate baseline original target goals
            emit (fields ++ [("status", toJson "certified"), ("certificate", metrics)])
  catch e =>
    emit ((← fieldsRef.get) ++ [("status", toJson (← failureStatus.get)),
      ("error", toJson (← e.toMessageData.toString))])
  finally
    saved.restore

end RQ2
