import Flex.PA.Scrape.Definitions
import Flex.PA.Scrape.Structured
import Flex.PA.Scrape.Accumulate
import Flex.PA.Scrape.Regions

/-! Relate source observations to predicate arguments; preserve original slot assignments. -/

open Lean Meta

namespace PAScrape.Internal

private structure Observations where
  relations : Array Expr := #[]
  predicates : Array Expr := #[]
  equalities : Array Expr := #[]

private partial def observationAtoms (cfg : PAScrapeConfig) (raw : Expr)
    (out : Observations) (depth : Nat := 0) : ScrapeM Observations := do
  unless ← visit cfg depth do return out
  let e := raw.consumeMData.headBeta
  if let .letE _ _ value body _ := e then
    return ← observationAtoms cfg (body.instantiate1 value) out (depth + 1)
  if let .forallE _ domain body _ := e then
    if (← isProp domain) && !body.hasLooseBVar 0 then
      let out ← observationAtoms cfg domain out (depth + 1)
      return ← observationAtoms cfg body out (depth + 1)
  let fn := e.getAppFn
  let fixed := (← get).fixed
  if ← predicateApplication e then
    unless fn.isFVar && fixed.contains fn.fvarId! do
      return if out.relations.contains e then out else
        { out with relations := out.relations.push e }
  let mut out := out
  if e.isAppOfArity ``Eq 3 && !e.hasMVar && !out.equalities.contains e then
    out := { out with equalities := out.equalities.push e }
  if e.isApp && !e.hasMVar && !e.hasLooseBVars && (← isProp e) then
    let semantic ← match fn with
      | .const name _ => discoverable name
      | .fvar id => pure (fixed.contains id)
      | _ => pure false
    if semantic && !out.predicates.contains e then
      out := { out with predicates := out.predicates.push e }
  -- Quantified observations need their own binding rule; do not cross binders here.
  for arg in e.getAppArgs do
    out ← observationAtoms cfg arg out (depth + 1)
  return out

inductive SourceRule where
  | endpoints | accumulate | algebra | affine | measures | guarded | fragments
  | regions | prefixes | worklists | relational
  deriving BEq

def SourceRule.all : Array SourceRule :=
  #[.endpoints, .accumulate, .algebra, .affine, .measures, .guarded, .fragments,
    .regions, .prefixes, .worklists, .relational]

def SourceRule.cap (cfg : PAScrapeConfig) : SourceRule → Nat
  | .endpoints => cfg.maxEndpointCandidatesPerKappa
  | .accumulate => cfg.maxAccumulatorCandidatesPerKappa
  | .algebra => cfg.maxAlgebraCandidatesPerKappa
  | .affine => cfg.maxAffineCandidatesPerKappa
  | .measures => cfg.maxMeasureCandidatesPerKappa
  | .guarded => cfg.maxStateGuardedCandidatesPerKappa
  | .fragments => cfg.maxFragmentCandidatesPerKappa
  | .regions => cfg.maxRegionCandidatesPerKappa
  | .prefixes => cfg.maxPrefixCandidatesPerKappa
  | .worklists => cfg.maxWorklistCandidatesPerKappa
  | .relational => cfg.maxRelationalCandidatesPerKappa

private def SourceRule.origin : SourceRule → String
  | .endpoints => "endpoint generalization"
  | .accumulate => "accumulator completion"
  | .algebra => "algebraic completion"
  | .affine => "affine endpoints"
  | .measures => "measure transport"
  | .guarded => "state-guarded completion"
  | .fragments => "pending fragments"
  | .regions => "quantified regions"
  | .prefixes => "prefix observations"
  | .worklists => "worklist measures"
  | .relational => "relational completion"

private def SourceRule.generate (properties arguments : Array Expr) (cap : Nat)
    : SourceRule → MetaM (Array Expr)
  | .endpoints => Structured.endpointCandidates properties arguments cap
  | .accumulate => Accumulate.candidates properties arguments cap
  | .algebra => Accumulate.algebraCandidates properties arguments cap
  | .affine => Structured.affineCandidates properties arguments cap
  | .measures => Structured.measureCandidates properties arguments cap
  | .guarded => Accumulate.guardedCandidates properties arguments cap
  | .fragments => Accumulate.fragmentCandidates properties arguments cap
  | .regions => Regions.regionCandidates properties arguments cap
  | .prefixes => Regions.prefixCandidates properties arguments cap
  | .worklists => Accumulate.worklistCandidates properties arguments cap
  | .relational => Regions.relationalCandidates properties arguments cap

inductive ObservationMode where
  | relate | quantify | arguments | anchored | compound | source (rule : SourceRule)
  deriving BEq

private def ObservationMode.isSource : ObservationMode → Bool
  | .source _ => true
  | _ => false

/-- Abstract compound κ arguments, such as record fields, into template parameters. -/
private def observationArguments (cfg : PAScrapeConfig) (observation relation : Expr) : ScrapeM Unit := do
  let mut inputs := #[]
  let mut types := #[]
  for arg in relation.getAppArgs do
    if arg.isFVar || !arg.hasFVar || arg.hasMVar || inputs.contains arg then continue
    unless (observation.find? (· == arg)).isSome do continue
    let ty ← instantiateMVars (← inferType arg)
    if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars || (← isProp ty) ||
        (← whnf ty).isSort then continue
    inputs := inputs.push arg
    types := types.push ty
  if inputs.isEmpty || inputs.size > cfg.maxParams then return
  withLocalDeclsDND (types.map (`argument, ·)) fun parameters => do
    let property := observation.replace fun e =>
      inputs.findIdx? (· == e) |>.map (parameters[·]!)
    -- A retained argument may depend on a field that was abstracted.
    try
      check property
    catch e =>
      if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
      reject
      return
    addPredicate cfg "predicate arguments" .observation property

/-- Retain the observed slot assignment instead of enumerating type-compatible permutations. -/
private def anchorPredicate (cfg : PAScrapeConfig) (origin : String)
    (property relation : Expr) : ScrapeM Unit := do
  if property.isConstOf ``True then return
  if let some (_, lhs, rhs) := property.eq? then
    if lhs == rhs then return
  let .mvar kvar := relation.getAppFn | return
  if (← get).anchoredSeen.contains (property, relation) then return
  modify fun s => { s with anchoredSeen := s.anchoredSeen.insert (property, relation) }
  if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then
    limit "anchored attempts"
    return
  modify fun s => { s with anchoredAttempts := s.anchoredAttempts + 1 }
  if ((← get).anchored.filter (·.kvar == kvar)).size >= cfg.maxAnchoredCandidatesPerKappa then
    limit "anchored candidates"
    return
  if property.hasMVar || property.hasLooseBVars then return
  let args := relation.getAppArgs
  let mut inputs := #[]
  let mut types := #[]
  let mut slots := #[]
  for arg in args, i in [:args.size] do
    if !arg.hasFVar || arg.hasMVar || inputs.contains arg then continue
    unless (property.find? (· == arg)).isSome do continue
    let ty ← instantiateMVars (← inferType arg)
    if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars || (← isProp ty) ||
        (← whnf ty).isSort then continue
    inputs := inputs.push arg
    types := types.push ty
    slots := slots.push i
  if inputs.isEmpty then return
  if origin == "source arguments" && inputs.size <= cfg.maxParams &&
      inputs.all Expr.isFVar then return
  let fixed := (← get).fixed
  withLocalDeclsDND (types.map (`slot, ·)) fun parameters => do
    let body := property.replace fun e =>
      inputs.findIdx? (· == e) |>.map (parameters[·]!)
    let mut q := body.abstract parameters
    for i in (List.range parameters.size).reverse do
      q := .lam (Name.mkSimple s!"q{i}") types[i]! q .default
    if q.hasMVar || q.hasLooseBVars || (support q).any (!fixed.contains ·) then return
    try check q
    catch e =>
      if e.isInterrupt || e.isMaxHeartbeat || e.isMaxRecDepth then throw e
      reject
      return
    unless ← isProp body do return
    if (← get).anchored.any (fun old =>
        old.kvar == kvar && old.qualifier == q && old.slots == slots.toList) then return
    modify fun s => { s with anchored := s.anchored.push ⟨kvar, q, slots.toList, origin⟩ }
    trace[flex.scrape] "{origin}: {q} at slots {slots}"

private def normalizeOffsets (property : Expr) : MetaM Expr := do
  let mut lemmas : SimpTheorems := {}
  for name in #[``Int.sub_eq_add_neg, ``Int.neg_add, ``Int.neg_neg,
      ``Int.add_assoc, ``Int.add_zero, ``Int.zero_add,
      ``Int.add_left_neg, ``Int.add_right_neg] do
    lemmas ← lemmas.addConst name
  let context ← Simp.mkContext { maxSteps := 1000, failIfUnchanged := false } #[lemmas]
  return (← Meta.simp property context).1.expr

/-- Alias equations propose candidates only; PA still checks every resulting predicate. -/
private def anchoredObservation (cfg : PAScrapeConfig) (property relation : Expr)
    (equalities : Array Expr) : ScrapeM Unit := do
  anchorPredicate cfg "source arguments" property relation
  for candidate in ← Structured.absoluteIndexCandidates property do
    anchorPredicate cfg "absolute index" candidate relation
  let mut rewritten := property
  for _ in [:3] do
    let previous := rewritten
    for eq in equalities do
      let a := eq.getArg! 1
      let b := eq.getArg! 2
      let (lhs, rhs) := if a.isFVar then (a, b) else (b, a)
      unless lhs.isFVar && !relation.getAppArgs.contains lhs &&
          !rhs.containsFVar lhs.fvarId! do continue
      rewritten := rewritten.replaceFVar lhs rhs
    if rewritten == previous then break
  if rewritten != property then
    anchorPredicate cfg "source aliases" rewritten relation
    anchorPredicate cfg "source offsets" (← normalizeOffsets rewritten) relation
    for candidate in ← Structured.absoluteIndexCandidates rewritten do
      anchorPredicate cfg "absolute index" candidate relation

/-- Compare observations at κ arguments, optionally quantifying their extra inputs. -/
private def observationPredicates (cfg : PAScrapeConfig) (mode : ObservationMode)
    (props : Array Expr) : ScrapeM Unit := do
  let mut found : Observations := {}
  for p in props do found ← observationAtoms cfg p found
  if let .source rule := mode then
    let origin := rule.origin
    let cap := rule.cap cfg
    for relation in found.relations do
      if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
      let .mvar kvar := relation.getAppFn | continue
      let count := ((← get).anchored.filter fun q => q.kvar == kvar && q.origin == origin).size
      let budget := min (cap - count) (cfg.maxAnchoredAttempts - (← get).anchoredAttempts)
      if budget == 0 then continue
      let mut properties := found.predicates ++ found.equalities
      if rule != .endpoints && rule != .accumulate then
        for property in props do
          if !property.hasMVar && !property.hasLooseBVars && !properties.contains property then
            properties := properties.push property
      let candidates ← rule.generate properties relation.getAppArgs budget
      for candidate in candidates do anchorPredicate cfg origin candidate relation
    return
  if mode == .compound then
    for relation in found.relations do
      if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
      let .mvar kvar := relation.getAppFn | continue
      let count := ((← get).anchored.filter fun q =>
        q.kvar == kvar && q.origin == "compound arguments").size
      let budget := min 24 (min (cfg.maxCompoundCandidatesPerKappa - count)
        (cfg.maxAnchoredAttempts - (← get).anchoredAttempts))
      for candidate in ← Structured.compoundCandidates found.predicates relation.getAppArgs budget do
        anchorPredicate cfg "compound arguments" candidate relation
    return
  let fixed := (← get).fixed
  let observations := if mode == .anchored then
      found.predicates ++ found.equalities else found.predicates
  if mode == .anchored then
    for relation in found.relations do
      if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
      let .mvar kvar := relation.getAppFn | continue
      let count := ((← get).anchored.filter (·.kvar == kvar)).size
      let budget := min 24 (min (cfg.maxAnchoredCandidatesPerKappa - count)
        (cfg.maxAnchoredAttempts - (← get).anchoredAttempts))
      if budget == 0 then continue
      let arguments := relation.getAppArgs
      let families := #[
        ("array prefix", ← Structured.prefixCandidates props arguments budget),
        ("semantic arguments", ← Structured.slotCandidates found.predicates arguments budget),
        ("list structure", ← Structured.listCandidates props arguments budget),
        ("list prefix", ← Structured.listPrefixCandidates props arguments budget)]
      for i in [:families.foldl (fun n (_, candidates) => max n candidates.size) 0] do
        for (origin, candidates) in families do
          if let some candidate := candidates[i]? then
            anchorPredicate cfg origin candidate relation
  for observation in observations do
    let ids := (support observation).filter (!fixed.contains ·)
    for relation in found.relations do
      if mode == .anchored then
        if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
        let .mvar kvar := relation.getAppFn | continue
        if ((← get).anchored.filter (·.kvar == kvar)).size >= cfg.maxAnchoredCandidatesPerKappa then
          continue
        anchoredObservation cfg observation relation found.equalities
        continue
      if mode == .arguments then
        observationArguments cfg observation relation
        continue
      let args := observation.getAppArgs
      let extra := ids.filter (!(support relation).contains ·)
      if (mode == .quantify) != !extra.isEmpty || extra.size > cfg.maxObservationBinders then continue
      -- Extra observation inputs become universal binders, never extra κ parameters.
      -- Do not capture an input belonging to another predicate occurrence.
      let mut binderTypes := #[]
      for id in extra do
        let x := mkFVar id
        unless args.contains x do break
        if found.relations.any (fun r => (support r).contains id) then break
        let ty ← instantiateMVars (← inferType x)
        if ty.hasFVar || ty.hasMVar || ty.hasLooseBVars || (← isProp ty) ||
            (← whnf ty).isSort || (← whnf ty).isForall then break
        binderTypes := binderTypes.push ty
      unless binderTypes.size == extra.size do continue
      let mut type ← inferType observation.getAppFn
      for i in [:args.size] do
        type ← whnf type
        unless type.isForall do break
        let domain := type.bindingDomain!
        let dependent := type.bindingBody!.hasLooseBVar 0
        let isInstance := type.bindingInfo! == .instImplicit
        type := type.bindingBody!.instantiate1 args[i]!
        let arg := args[i]!
        unless arg.isFVar && relation.getAppArgs.contains arg do continue
        if dependent || isInstance || domain.hasFVar || domain.hasMVar ||
            (← isProp domain) || (← whnf domain).isSort then continue
        for replacement in relation.getAppArgs do
          if (← get).observations.size >= cfg.maxObservationQualifiers then
            limit "observation templates"; return
          if (← get).observationPairs >= cfg.maxObservationPairs then
            limit "observation pairs"; return
          unless replacement.isFVar && replacement != arg do continue
          modify fun s => { s with observationPairs := s.observationPairs + 1 }
          let replacementType ← inferType replacement
          if replacementType.hasFVar || replacementType.hasMVar then continue
          unless ← isDefEq domain replacementType do continue
          let other := mkAppN observation.getAppFn (args.set! i replacement)
          let mut property := (mkApp2 (mkConst ``Iff) observation other).abstract (extra.map mkFVar)
          for j in (List.range extra.size).reverse do
            property := .forallE (Name.mkSimple s!"value{j}") binderTypes[j]! property .default
          addPredicate cfg "observation relation" .observation
            property

partial def observationClauses (cfg : PAScrapeConfig) (mode : ObservationMode) (raw : Expr)
    (premises : Array Expr := #[]) (depth : Nat := 0) : ScrapeM Unit := do
  if mode == .anchored || mode == .compound || mode.isSource then
    if (← get).anchoredAttempts >= cfg.maxAnchoredAttempts then return
  else if (← get).observations.size >= cfg.maxObservationQualifiers ||
      (← get).observationPairs >= cfg.maxObservationPairs then return
  unless ← visit cfg depth do return
  let e := raw.consumeMData.headBeta
  if let .letE _ _ value body _ := e then
    observationClauses cfg mode (body.instantiate1 value) premises (depth + 1)
  else if e.isForall then
    let domain := e.bindingDomain!
    -- Keep quantified safety properties intact for binder-aware source rules.
    if mode == .source .regions && !(← isProp domain) && !e.hasMVar then
      observationPredicates cfg mode (premises.push e)
    let premises := if ← isProp domain then premises.push domain else premises
    withLocalDecl e.bindingName! e.bindingInfo! domain fun x =>
      observationClauses cfg mode (e.bindingBody!.instantiate1 x) premises (depth + 1)
  else if let some (left, right) := e.and? then
    observationClauses cfg mode left premises (depth + 1)
    observationClauses cfg mode right premises (depth + 1)
  else
    observationPredicates cfg mode (premises.push e)

end PAScrape.Internal
