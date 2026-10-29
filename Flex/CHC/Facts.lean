import Flex.CHC.Export
import Lean.Meta.Tactic.Replace

namespace Flex.CHC.Facts

open Lean Meta Elab Term

/-- Theorems and definition equations available to semantic projection. -/
structure Config where
  lemmas : Array Name := #[]
  defs : Array Name := #[]
  maxTerms : Nat := 10
  maxFacts : Nat := 128
  deriving Inhabited

private structure Fact where
  proposition : Expr
  proof : Expr

private def equations (cfg : Config) : MetaM (Array Name) := do
  let mut names := cfg.lemmas
  for name in cfg.defs do
    let some eqns ← getEqnsFor? name
      | throwError "CHC facts: no equation theorems for '{name}'"
    for eqn in eqns do
      unless names.contains eqn do names := names.push eqn
  for name in names do
    let info ← getConstInfo name
    unless info.isTheorem do throwError "CHC facts: '{name}' is not a theorem"
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "CHC facts: '{name}' depends on untrusted axiom '{dependency}'"
  return names

private partial def assumptions (proof : Expr) (depth : Nat := 0) : MetaM (Array Fact) := do
  let proposition ← inferType proof
  let mut result := #[{ proposition, proof : Fact }]
  if depth >= 12 then return result
  let reduced ← withReducible <| whnf proposition
  let expanded ← if reduced.isAppOf ``And then pure reduced else do
    pure ((← unfoldDefinition? reduced).getD reduced)
  if expanded.isAppOfArity ``And 2 then
    result := result ++ (← assumptions (← mkAppM ``And.left #[proof]) (depth + 1))
    result := result ++ (← assumptions (← mkAppM ``And.right #[proof]) (depth + 1))
  return result

private def contextFacts : MetaM (Array Fact) := do
  let mut out := #[]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      if ← isProp declaration.type then
        out := out ++ (← assumptions declaration.toExpr)
  return out

private partial def terms (input : Expr) (limit : Nat) (definitions : Array Name)
    (out : Array Expr := #[]) : MetaM (Array Expr) := do
  if out.size >= limit then return out
  let input := input.consumeMData
  let mut out := out
  unless input.hasLooseBVars || input.hasMVar do
    if (← inferType input).isConstOf ``Int &&
        !(input.find? fun e => e.isConst && definitions.contains e.constName!).isSome then
      let small ← match ← getIntValue? (← withReducible <| whnf input) with
        | some n => pure (decide (n.natAbs <= 4))
        | none => pure true
      if small && !out.contains input then out := out.push input
  match input with
  | .app .. =>
    -- Whole application arguments precede their subterms.
    let args := input.getAppArgs
    for a in args do
      if out.size >= limit then break
      unless a.hasLooseBVars || a.hasMVar do
        if (← inferType a).isConstOf ``Int &&
            !(a.find? fun e => e.isConst && definitions.contains e.constName!).isSome then
          let small ← match ← getIntValue? (← withReducible <| whnf a) with
            | some n => pure (decide (n.natAbs <= 4))
            | none => pure true
          if small && !out.contains a then out := out.push a
    for a in args do out ← terms a limit definitions out
    return out
  | _ => pure out

private partial def guardTerms (input : Expr) (cfg : Config)
    (out : Array Expr := #[]) : MetaM (Array Expr) := do
  if out.size >= cfg.maxTerms then return out
  let input := input.consumeMData
  if input.isAppOf ``LE.le || input.isAppOf ``LT.lt ||
      input.isAppOf ``GE.ge || input.isAppOf ``GT.gt then
    return ← terms input cfg.maxTerms cfg.defs out
  if let .app .. := input then
    let mut out := out
    for argument in input.getAppArgs do
      out ← guardTerms argument cfg out
    return out
  return out

private partial def dataArity (type : Expr) (count : Nat := 0) : MetaM Nat := do
  let type ← whnf type
  if let .forallE name domain body bi := type then
    if ← isProp domain then return count
    withLocalDecl name bi domain fun x => dataArity (body.instantiate1 x) (count + 1)
  else return count

private def addFact (proof : Expr) (out : Array Fact) (limit : Nat) : MetaM (Array Fact) := do
  if out.size >= limit || proof.hasMVar then return out
  let proposition ← inferType proof
  if proof.hasLevelMVar || proposition.hasMVar || proposition.hasLevelMVar || out.any (·.proposition == proposition) then return out
  unless ← isProp proposition do return out
  return out.push { proposition, proof }

private partial def ground (proof : Expr) (arity : Nat) (pool : Array Expr)
    (out : Array Fact) (limit : Nat) : MetaM (Array Fact) := do
  if out.size >= limit then return out
  if arity == 0 then return ← addFact proof out limit
  let type ← whnf (← inferType proof)
  let .forallE _ domain _ _ := type | return out
  let mut out := out
  for value in pool do
    if out.size >= limit then break
    if ← withReducible <| isDefEq (← inferType value) domain then
      out ← ground (mkApp proof value) (arity - 1) pool out limit
  return out

private partial def propositionTerms (input : Expr) (out : Array Expr := #[])
    : MetaM (Array Expr) := do
  let input := input.consumeMData
  let mut out := out
  if !input.hasMVar && !input.hasLooseBVars && !out.contains input then
    if ← isProp input then out := out.push input
  for argument in input.getAppArgs do out ← propositionTerms argument out
  if let .forallE _ domain body _ := input then
    out ← propositionTerms domain out
    out ← propositionTerms body out
  return out

private def matched (name : Name) (known : Array Expr) (out : Array Fact)
    (limit : Nat) : MetaM (Array Fact) := do
  let mut out := out
  let lemma ← mkConstWithFreshMVarLevels name
  let arity ← dataArity (← inferType lemma)
  let (data, _, body) ← forallMetaBoundedTelescope (← inferType lemma) arity
  let (premises, _, _) ← forallMetaTelescopeReducing body
  for premise in premises do
    let pattern ← inferType premise
    for fact in known do
      if out.size >= limit then return out
      let saved ← saveState
      try
        if ← withReducible <| isDefEq pattern fact then
          let arguments ← data.mapM instantiateMVars
          unless arguments.any (·.hasMVar) do
            let proof ← instantiateMVars (mkAppN lemma arguments)
            out ← addFact proof out limit
      finally restoreState saved
  return out

private partial def applications (input : Expr) (definition : Name)
    (out : Array Expr := #[]) : Array Expr := Id.run do
  let input := input.consumeMData
  let mut out := out
  if input.isAppOf definition && !input.hasMVar && !input.hasLooseBVars &&
      !out.contains input then out := out.push input
  for argument in input.getAppArgs do out := applications argument definition out
  if let .forallE _ domain body _ := input then
    out := applications domain definition out
    out := applications body definition out
  return out

private def triggered (name : Name) (input : Expr) (known out : Array Fact)
    (cfg : Config) : MetaM (Option (Array Fact)) := do
  let lemma ← mkConstWithFreshMVarLevels name
  let type ← inferType lemma
  let arity ← dataArity type
  let (arguments, _, result) ← forallMetaTelescopeReducing type
  let lhs ← if result.isAppOfArity ``Eq 3 then pure (result.getArg! 1)
    else if result.isAppOfArity ``Iff 2 then pure (result.getArg! 0)
    else return none
  let some definition := lhs.getAppFn.constName? | return none
  unless cfg.defs.contains definition do return none
  let mut triggers := applications input definition
  for fact in known ++ out do
    triggers := applications fact.proposition definition triggers
  let mut out := out
  for trigger in triggers do
    if out.size >= cfg.maxFacts then break
    let saved ← saveState
    try
      if ← withReducible <| isDefEq lhs trigger then
        let data ← (arguments.extract 0 arity).mapM instantiateMVars
        unless data.any (·.hasMVar) do
          out ← addFact (← instantiateMVars (mkAppN lemma data)) out cfg.maxFacts
    finally restoreState saved
  return some out

private def instances (input : Expr) (names : Array Name) (cfg : Config) : MetaM (Array Fact) :=
  withNewMCtxDepth do
    let known ← contextFacts
    let mut pool := #[]
    for fact in known do pool ← guardTerms fact.proposition cfg pool
    let seeds := pool.foldl (fun ids term =>
      (collectFVars {} term).fvarIds.foldl (fun ids id => ids.insert id) ids)
      ({} : Std.HashSet FVarId)
    let candidates ← terms input (cfg.maxTerms * 2) cfg.defs
    for value in candidates do
      if pool.size >= cfg.maxTerms then break
      if (collectFVars {} value).fvarIds.all seeds.contains && !pool.contains value then
        pool := pool.push value
    let mut candidates ← propositionTerms input
    for fact in known do candidates ← propositionTerms fact.proposition candidates
    let mut out := #[]
    for name in names do
      if let some result ← triggered name input known out cfg then
        out := result
        continue
      let lemma ← mkConstWithFreshMVarLevels name
      let arity ← dataArity (← inferType lemma)
      let (parameters, _, _) ← forallMetaBoundedTelescope (← inferType lemma) arity
      let scalar ← parameters.allM fun parameter => return (← inferType parameter).isConstOf ``Int
      if arity <= 2 && scalar then
        out ← ground lemma arity pool out cfg.maxFacts
      else
        let mut available := candidates
        for fact in out do available ← propositionTerms fact.proposition available
        out ← matched name available out cfg.maxFacts
    return out

private def addPremises (input : Expr) (facts : Array Fact) : MetaM (Expr × Expr) := do
  if facts.isEmpty then return (input, mkApp (mkConst ``Iff.refl) input)
  let result ← facts.foldrM (fun f body => mkArrow f.proposition body) input
  let forward ← withLocalDeclD `h input fun h => do
    withLocalDeclsDND (facts.map fun f => (`fact, f.proposition)) fun hypotheses =>
      mkLambdaFVars (#[h] ++ hypotheses) h
  let backward ← withLocalDeclD `h result fun h =>
    mkLambdaFVars #[h] (mkAppN h (facts.map (·.proof)))
  return (result, ← mkAppM ``Iff.intro #[forward, backward])

private partial def enrich (input : Expr) (names : Array Name) (cfg : Config)
    (scope : Option Expr := none) : MetaM (Expr × Expr) := do
  let input ← Prepare.expose input
  if let some (left, right) := input.and? then
    let (left', lp) ← enrich left names cfg (some (scope.getD input))
    let (right', rp) ← enrich right names cfg (some (scope.getD input))
    return (mkApp2 (mkConst ``And) left' right',
      mkApp6 (mkConst ``and_congr) left left' right right' lp rp)
  if let .forallE name domain body bi := input then
    return ← withLocalDecl name bi domain fun x => do
      let body := body.instantiate1 x
      let (result, proof) ← enrich body names cfg (some body)
      return (← mkForallFVars #[x] result,
        mkApp4 (mkConst ``forall_congr' [← getLevel domain]) domain
          (← mkLambdaFVars #[x] body) (← mkLambdaFVars #[x] result)
          (← mkLambdaFVars #[x] proof))
  addPremises input (← instances (scope.getD input) names cfg)

/-- Add instantiated semantic theorems through a checked equivalence. -/
def enrichGoal (goal : MVarId) (kvars : List KVar) (cfg : Config := {}) : TermElabM MVarId :=
  goal.withContext do
    if cfg.lemmas.isEmpty && cfg.defs.isEmpty then return goal
    let names ← equations cfg
    let target ← instantiateMVars (← goal.getType)
    let (result, proof) ← enrich target names cfg
    if result == target then return goal
    let declarations ← kvars.toArray.mapM fun k => return (k.name, ← k.mvarId.getType)
    withLocalDeclsDND declarations fun parameters => do
      let replacements := (kvars.toArray.zip parameters).foldl
        (fun map (k, parameter) => map.insert k.mvarId parameter) ({} : Std.HashMap MVarId Expr)
      checkWithKernel (proof.replace fun e => if e.isMVar then replacements[e.mvarId!]? else none)
    goal.replaceTargetEq result (mkApp3 (mkConst ``propext) target result proof)

end Flex.CHC.Facts
