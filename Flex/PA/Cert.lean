import Lean

import Flex.Core
import Flex.PA.Weaken
import Flex.PA.Check
import Flex.Zap.Emit

open Lean Meta Elab Term Tactic

/-! Certify instantiated predicate heads, retaining ordinary leaves as residual goals. -/

/-- Recognize a predicate head before instantiating its metavariable. -/
def paHead?
    (assign : List (KVar × List (Expr × List Nat)))
    (goal : Expr) :
    Option (KVar × List (Expr × List Nat) × Array Expr) :=
  let fn := goal.getAppFn
  if fn.isMVar then
    (assign.find? (fun (κ, _) => κ.mvarId == fn.mvarId!)).map
      (fun (κ, survivors) => (κ, survivors, goal.getAppArgs))
  else none

/-- Assemble proofs in the same conjunction order as the predicate witness. -/
def conjProofs : List (Expr × Expr) → Expr
  | []           => mkConst ``True.intro
  | [(_, p)]     => p
  | (e0, p0) :: rest =>
    (rest.foldl
      (fun (acc cur : Expr × Expr) =>
        let (accE, accP) := acc
        let (curE, curP) := cur
        (mkApp2 (mkConst ``And) accE curE, mkAndIntro accE curE accP curP))
      (e0, p0)).2

/-- Prove a whole head once. Leaf fallback supports oracles that cannot prove conjunctions. -/
def emitPALeaf
    (κ : KVar)
    (survivors : List (Expr × List Nat))
    (args : Array Expr)
    (oracle : PAOracle := proveLeaf) :
    TermElabM Expr := do
  let bodies ← survivors.mapM fun (q, slots) =>
    Expr.instQualifier q ((slots.map fun i => args[i]!).toArray)
  let target := conjoinExprs bodies
  if bodies.isEmpty then return mkConst ``True.intro
  for declaration in ← getLCtx do
    if (← instantiateMVars declaration.type) == target then return mkFVar declaration.fvarId
  if bodies.length > 1 then
    if let some proof ← oracle target then return proof
  let pairs ← bodies.mapM fun body => do
    match ← oracle body with
    | some proof => pure (body, proof)
    | none => throwError "fix: could not certify a predicate head for '{κ.name}':{indentExpr body}"
  return conjProofs pairs

private def mentionsPredicates (assign : List (KVar × List (Expr × List Nat)))
    (e : Expr) : Bool :=
  (e.find? fun e => e.isMVar && assign.any (fun (κ, _) => κ.mvarId == e.mvarId!)).isSome

/-- Certify heads and validate predicate-dependent safety leaves before keeping residuals. -/
partial def walkPAProof
    (assign : List (KVar × List (Expr × List Nat)))
    (goal : Expr)
    (residualOut : IO.Ref (Array MVarId))
    (oracle : PAOracle := proveLeaf)
    (validateSafety : PAOracle := fun _ => pure none)
    (dependsOnPredicates : Bool := false) :
    TermElabM Expr := do
  if let some (κ, survivors, args) := paHead? assign goal then
    return ← emitPALeaf κ survivors args oracle
  if goal.getAppFn.isMVar then
    throwError "fix: head metavariable{indentExpr goal.getAppFn}\nis not a \
      cut variable handled by PA. Eliminate acyclic κ's with `fusion` first."
  if goal.isForall then
    let dependent := dependsOnPredicates || mentionsPredicates assign goal.bindingDomain!
    let dom ← instantiateMVars goal.bindingDomain!
    let name := goal.bindingName!
    let bi   := goal.bindingInfo!
    return ← withLocalDecl name bi dom fun fv => do
      let body  := goal.bindingBody!.instantiate1 fv
      let inner ← walkPAProof assign body residualOut oracle validateSafety dependent
      mkLambdaFVars #[fv] inner
  if let some (l, r) := goal.and? then
    let pL ← walkPAProof assign l residualOut oracle validateSafety dependsOnPredicates
    let pR ← walkPAProof assign r residualOut oracle validateSafety dependsOnPredicates
    return mkAndIntro l r pL pR
  let contextDepends := (← getLCtx).any fun decl =>
    mentionsPredicates assign decl.type || decl.value?.any (mentionsPredicates assign)
  if dependsOnPredicates || contextDepends || mentionsPredicates assign goal then
    if let some proof ← validateSafety (← instantiateMVars goal) then return proof
  let m ← mkFreshExprMVar (some goal) (kind := .syntheticOpaque)
  residualOut.modify (·.push m.mvarId!)
  return m
