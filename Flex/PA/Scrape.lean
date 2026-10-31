import Flex.PA.Scrape.Guards
import Flex.PA.Scrape.Observations

/-! Scraping pipeline and public API. Candidate selection order and budgets are shared
across goal, definition, guard, and source-observation passes. -/

open Lean Meta

namespace PAScrape.Internal

private def interleavePredicates (candidates : Array PAAnchoredQualifier) (cap : Nat)
    : Array PAAnchoredQualifier := Id.run do
  let mut families : Array (MVarId × Name × Array PAAnchoredQualifier) := #[]
  for candidate in candidates do
    let mut body := candidate.qualifier
    while body.isLambda do body := body.bindingBody!
    let name := body.getAppFn.constName?.getD .anonymous
    if let some i := families.findIdx? (fun (k, n, _) => k == candidate.kvar && n == name) then
      let (k, n, old) := families[i]!
      families := families.set! i (k, n, old.push candidate)
    else
      families := families.push (candidate.kvar, name, #[candidate])
  let mut result := #[]
  for i in [:cap] do
    for (k, _, family) in families do
      if let some candidate := family[i]? then
        if (result.filter (·.kvar == k)).size < cap then result := result.push candidate
  return result

private def collect (cfg : PAScrapeConfig) (body : Expr) : ScrapeM Unit := do
  for name in cfg.defs do
    unless (← getConstInfo name) matches .defnInfo _ do
      throwError "fix: `{name}` is not a definition to scrape"
    enqueue cfg { fn := ← mkConstWithLevelParams name, requested := true }
  if cfg.mode != .no then clause cfg body
  if automatic cfg && cfg.maxGuardedQualifiers > 0 then
    -- Eligibility has its own bounded traversal; a rejected goal keeps ordinary scraping unchanged.
    let (eligible, _) ← (arithmeticGoal cfg body 0).run {}
    if eligible then
      -- Safety clauses expose demanded properties before transition-clause proposals.
      guardedClauses cfg body true
      guardedClauses cfg body false
  repeat
    let s ← get
    if s.pending.isEmpty then break
    if s.nodes >= cfg.maxNodes then limit "nodes"; break
    let d := s.pending[0]!
    set { s with
      pending := s.pending.extract 1 s.pending.size
      visited := s.visited.push (d.fn, d.typeArgs) }
    inspectDefinition cfg d
  if cfg.mode == .deep then
    let originals := (← get).goal ++ (← get).definitions
    for candidate in originals do
      unless ← visit cfg 0 do break
      for q in ← deepScrapeVariants candidate.expr do
        unless ← visit cfg 0 do break
        lambdaTelescope q fun _ p => addPredicate cfg (candidate.origin ++ ": generalized") .generated p
  if automatic cfg && cfg.maxObservationQualifiers > 0 then
    observationClauses cfg .relate body
    if cfg.maxObservationBinders > 0 then observationClauses cfg .quantify body
    observationClauses cfg .arguments body
  if automatic cfg && cfg.maxAnchoredCandidatesPerKappa > 0 then
    observationClauses { cfg with maxNodes := (← get).nodes + cfg.maxAnchoredNodes } .anchored body
    -- Gather twice the supplemental quota, then share it across named predicates.
    if cfg.maxCompoundCandidatesPerKappa > 0 then
      let ordinary := (← get).anchored
      let quota := 2 * cfg.maxCompoundCandidatesPerKappa
      observationClauses { cfg with
        maxNodes := (← get).nodes + cfg.maxAnchoredNodes
        maxAnchoredAttempts := (← get).anchoredAttempts + cfg.maxAnchoredAttempts
        maxCompoundCandidatesPerKappa := quota
        maxAnchoredCandidatesPerKappa :=
          cfg.maxAnchoredCandidatesPerKappa + quota } .compound body
      let extra := (← get).anchored.extract ordinary.size (← get).anchored.size
      let selected := interleavePredicates extra cfg.maxCompoundCandidatesPerKappa
      modify fun s => { s with anchored := ordinary ++ selected }
    -- Supplemental deep candidates cannot displace the existing anchored pool.
    if cfg.mode == .deep then
      let extraCap := SourceRule.all.foldl (fun n rule => n + rule.cap cfg) 0
      for rule in SourceRule.all do
        if rule.cap cfg == 0 then continue
        observationClauses { cfg with
          maxNodes := (← get).nodes + cfg.maxAnchoredNodes
          maxAnchoredAttempts := (← get).anchoredAttempts + cfg.maxAnchoredAttempts
          maxAnchoredCandidatesPerKappa := cfg.maxAnchoredCandidatesPerKappa +
            cfg.maxCompoundCandidatesPerKappa + extraCap } (.source rule) body

/-- Interleave ordinary sources; observations fill the remaining slots. -/
private def finish (cfg : PAScrapeConfig) (s : ScrapeState) : PAScrapeResult := Id.run do
  let pools := #[s.goal, s.guarded, s.definitions, s.generated]
  let maxSize := pools.foldl (fun n pool => max n pool.size) 0
  let mut selected := #[]
  for i in [:maxSize] do
    for source in pools do
      if let some q := source[i]? then
        if selected.size < cfg.maxQualifiers then selected := selected.push q
  let ordinaryCount := selected.size
  for candidate in s.observations do
    if selected.size < cfg.maxQualifiers then selected := selected.push candidate
  let count := pools.foldl (fun n pool => n + pool.size) s.observations.size
  let limitsHit := if count > selected.size && !s.limitsHit.contains "templates" then
    s.limitsHit.push "templates" else s.limitsHit
  return {
    qualifiers := selected.map (·.expr)
    origins := selected.map (·.origin)
    observationCount := selected.size - ordinaryCount
    anchored := s.anchored
    visitedNodes := s.nodes
    inspectedDefinitions := s.inspected
    rejected := s.rejected
    limitsHit }

end PAScrape.Internal

/-- Candidate templates may capture the caller's context, never temporary scraping binders. -/
def scrapePAQualifiersWithReport (body : Expr) (cfg : PAScrapeConfig) : MetaM PAScrapeResult := do
  let fixed := FVarIdSet.ofArray (← getLCtx).getFVarIds
  let (_, state) ← (PAScrape.Internal.collect cfg (← instantiateMVars body)).run { fixed }
  let result := PAScrape.Internal.finish cfg state
  unless result.limitsHit.isEmpty do
    trace[flex.scrape] "limits reached: {result.limitsHit}"
  return result

def scrapePAQualifiers (body : Expr) (cfg : PAScrapeConfig) : MetaM (Array Expr) := do
  return (← scrapePAQualifiersWithReport body cfg).qualifiers
