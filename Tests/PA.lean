import Flex.Tactic.Tactics.Fix
import Flex.Fusion.Flatten

namespace PABatchTests

open Lean Meta Elab Term

private def queries (terms : Array (TSyntax `term)) : TermElabM (Array Expr) :=
  terms.mapM fun term => do instantiateMVars (← elabTerm term none)

private def expect (terms : Array (TSyntax `term)) (expected : Array PASynthResult) : TermElabM Unit := do
  let actual ← Flex.PA.smtOracle 2000 (← queries terms)
  unless actual == expected do throwError "PA SMT: expected {repr expected}, got {repr actual}"

run_elab do
  -- Valid and invalid checks must share premises without sharing candidate assertions.
  expect #[← `(∀ x : Int, 0 ≤ x → False),
           ← `(∀ x : Int, 0 ≤ x → 0 ≤ x),
           ← `(∀ x : Int, 0 ≤ x → 1 ≤ x),
           ← `(∀ x : Int, 0 ≤ x → 1 ≤ x + 1)]
    #[.invalid, .valid, .invalid, .valid]
  -- Distinct premises cannot be hoisted into a common conjunction.
  expect #[← `(∀ x : Int, x = 0 → x = 1),
           ← `(∀ x : Int, x = 1 → x = 0)] #[.invalid, .invalid]
  expect #[← `(∀ p : Prop, ∀ b : Bool, p = (b = true) → p → b = true),
           ← `(∀ p : Prop, ∀ b : Bool, p = (b = true) → p → b = false)]
    #[.valid, .invalid]
  expect #[← `(∀ x : Int, 0 ≤ x → 0 ≤ x % 3),
           ← `(∀ x : Int, 0 ≤ x → x / 3 ≤ x)] #[.valid, .valid]
  withLocalDeclD `x (mkConst ``Int) fun x => do
    withLocalDeclD `h (← mkEq x (mkIntLit 3)) fun _ => do
      let result ← Flex.PA.smtOracle 2000 #[← mkAppM ``LE.le #[mkIntLit 0, x]]
      unless result == #[.valid] do throwError "PA SMT omitted a local assumption"
    let zero ← mkEq x (mkIntLit 0)
    let one ← mkEq x (mkIntLit 1)
    for (premise, expected) in #[(zero, #[.valid, .invalid, .valid]),
        (one, #[.invalid, .valid, .invalid])] do
      withLocalDeclD `h premise fun _ => do
        let result ← Flex.PA.smtOracle 2000 #[zero, one, zero]
        unless result == expected do throwError "SMT cache leaked between clause contexts"
  withLetDecl `x (mkConst ``Int) (mkIntLit 3) fun x => do
    let result ← Flex.PA.smtOracle 2000 #[← mkEq x (mkIntLit 3)]
    unless result == #[.valid] do throwError "PA SMT omitted a local definition"
  let result ← Flex.PA.smtOracle 2000 (← queries
    #[← `(∀ x : Int, x = 0 → ∀ n : Nat, n = n),
      ← `(∀ x : Int, x = 0 → 0 ≤ x)])
  unless result.size == 2 && result[1]! == .valid &&
      (match result[0]! with | .unknown _ => true | _ => false) do
    throwError "unsupported candidate contaminated its batch"
  withLocalDeclD `h (← elabTerm (← `(∀ n : Nat, n = n)) none) fun _ => do
    let result ← Flex.PA.smtOracle 2000 #[mkConst ``False]
    unless result.all (fun | .unknown _ => true | _ => false) do
      throwError "SMT treated an incomplete local context as a counterexample"
  withLocalDeclD `e (mkConst ``Empty) fun _ => do
    let result ← Flex.PA.smtOracle 2000 #[mkConst ``False]
    unless result.all (fun | .unknown _ => true | _ => false) do
      throwError "SMT ignored a potentially empty local data type"
  withLocalDeclD `n (mkConst ``Nat) fun n => do
    let result ← Flex.PA.smtOracle 2000 #[← mkEq n n, mkConst ``True]
    unless result.size == 2 && result[1]! == .valid &&
        (match result[0]! with | .unknown _ => true | _ => false) do
      throwError "unsupported free-input sort contaminated another candidate"
  let result ← Flex.PA.smtOracle 2000 (← queries #[← `(∀ x : Nat, x = x)])
  unless result.all (fun | .unknown _ => true | _ => false) do
    throwError "PA SMT accepted an unsupported sort"
  let result ← Flex.PA.smtOracle 2000 (← queries #[← `(
    let _ : HAdd Int Int Int := ⟨fun _ _ => 0⟩
    ∀ x : Int, x + 1 = x)])
  unless result.all (fun | .unknown _ => true | _ => false) do
    throwError "PA SMT erased a nonstandard operator instance"
  let caller ← mkFreshExprMVar (some (mkConst ``Int))
  discard <| Flex.PA.smtOracle 2000 #[← mkEq caller (mkIntLit 0)]
  if ← caller.mvarId!.isAssigned then throwError "PA SMT assigned a caller metavariable"

run_elab do
  -- Zap's shared seed keeps its witnesses scoped inside the premise.
  expect #[← `(∀ A C : Int, (∃ a b : Int, a = 1 + b ∧ A = a ∧ C = b) → A = C + 1),
           ← `(∀ A C : Int, (∃ a b : Int, a = 1 + b ∧ A = a ∧ C = b) → A = C)]
    #[.valid, .invalid]
  -- Negation and alternation must preserve the original quantifier polarity.
  expect #[← `(¬∃ x : Int, x ≠ x), ← `(¬∃ x : Int, x = x),
           ← `(∀ x : Int, ∃ y : Int, y = x + 1),
           ← `(∃ y : Int, ∀ x : Int, y = x + 1)]
    #[.valid, .invalid, .valid, .invalid]
  expect #[← `(∀ pa_0 : Int, ∃ pa_0 : Int, pa_0 = 1),
           ← `(∃ pa_0 : Int, ∀ pa_0 : Int, pa_0 = 1),
           ← `(∀ p : Prop, ∃ b : Bool, p = (b = true))]
    #[.valid, .invalid, .valid]
  for term in #[← `(∃ _ : Empty, True), ← `(∀ h : True, h = True.intro)] do
    let result ← Flex.PA.smtOracle 2000 (← queries #[term])
    unless result.all (fun | .unknown _ => true | _ => false) do
      throwError "unsupported or proof-dependent quantifier was accepted"

end PABatchTests

namespace PAScrapeTests

open Lean Meta Elab Term

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let e ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

private def guarded (result : PAScrapeResult) : Array Expr :=
  result.qualifiers.zip result.origins |>.filterMap fun (q, origin) =>
    if origin == "guarded clause" then some q else none

-- Boolean aliases expose data tests; equality guards also propose interval boundaries.
run_elab do
  let input ← elaborate (← `(∀ k : Int → Int → Prop, ∀ x y flag : Int,
    k x y → 0 = flag → y = 7 → ¬((0 = flag) = (4 ≤ x)) → False))
  let result ← scrapePAQualifiersWithReport input { mode := .standard }
  let expected ← elaborate (← `(fun (y x : Int) => y < 7 ∨ 4 ≤ x))
  unless ← (guarded result).anyM (fun q => isDefEq expected q) do
    throwError "missing guarded interval qualifier"
  unless (guarded result).size ≤ 32 do throwError "guarded template budget exceeded"
  for q in result.qualifiers do
    if q.hasFVar || q.hasMVar || q.hasLooseBVars then throwError "scraped binder escaped"
    check q
  for cfg in #[{ mode := .no }, { mode := .basic },
      { mode := .standard, maxGuardedQualifiers := 0 }] do
    unless (guarded (← scrapePAQualifiersWithReport input cfg)).isEmpty do
      throwError "guarded scraping ignored its mode or disabled budget"
  let limited ← scrapePAQualifiersWithReport input
    { mode := .standard, maxGuardedQualifiers := 1 }
  unless (guarded limited).size == 1 && limited.limitsHit.contains "guarded templates" do
    throwError "guarded template limit ignored"
  let limited ← scrapePAQualifiersWithReport input
    { mode := .standard, maxGuardPairs := 1 }
  unless (guarded limited).size ≤ 4 && limited.limitsHit.contains "guard pairs" do
    throwError "guarded pair limit ignored"
  let repeated ← elaborate (← `(∀ k : Int → Int → Prop,
    (∀ x y : Int, k x y → y = 7 → 4 ≤ x → False) ∧
    (∀ a b : Int, k a b → b = 7 → 4 ≤ a → False)))
  let once ← elaborate (← `(∀ k : Int → Int → Prop,
    ∀ x y : Int, k x y → y = 7 → 4 ≤ x → False))
  unless (guarded (← scrapePAQualifiersWithReport repeated { mode := .standard })) ==
      (guarded (← scrapePAQualifiersWithReport once { mode := .standard })) do
    throwError "alpha-equivalent guarded qualifiers were not deduplicated"
  let unary ← elaborate (← `(∀ k : Int → Prop, ∀ x flag : Int,
    k x → 0 = flag → ¬((0 = flag) = (4 ≤ x)) → False))
  let expected ← elaborate (← `(fun x : Int => 4 ≤ x))
  unless ← (← scrapePAQualifiers unary { mode := .standard }).anyM
      (fun q => isDefEq expected q) do
    throwError "Boolean alias hid a unary arithmetic atom"

-- A guard and property must belong to one clause and one predicate occurrence.
run_elab do
  let separateClauses ← elaborate (← `(∀ k : Int → Int → Prop,
    (∀ x y : Int, k x y → y = 7 → False) ∧
    (∀ x y : Int, k x y → 4 ≤ x → False)))
  let separatePredicates ← elaborate (← `(∀ k l : Int → Prop, ∀ x y : Int,
    k x → l y → y = 7 → 4 ≤ x → False))
  for input in #[separateClauses, separatePredicates] do
    unless (guarded (← scrapePAQualifiersWithReport input { mode := .standard })).isEmpty do
      throwError "combined unrelated clause or predicate arguments"

-- Function applications remain ordinary qualifiers, without recursive guard cross-products.
private def recursiveValue (n : Int) : Int :=
  if n ≤ 0 then 0 else recursiveValue (n - 1) + 1
  termination_by n.toNat

run_elab do
  let input ← elaborate (← `(∀ k : Int → Int → Prop, ∀ x y : Int,
    k x y → 0 ≤ x → y = recursiveValue x))
  let result ← scrapePAQualifiersWithReport input { mode := .standard }
  let expected ← elaborate (← `(fun y x : Int => y = recursiveValue x))
  unless ← result.qualifiers.anyM (fun q => isDefEq q expected) do
    throwError "ordinary scraping lost a function-application qualifier"
  unless (guarded result).isEmpty do
    throwError "guarded scraping combined recursive function applications"
  let ordinary ← scrapePAQualifiers input { mode := .standard, maxGuardedQualifiers := 0 }
  unless result.qualifiers == ordinary do
    throwError "ineligible guard augmentation changed ordinary scraping"
  let arithmetic ← elaborate (← `(∀ k : Int → Int → Prop, ∀ x y : Int,
    k x y → 3 ≤ x + 1 → y = 2 * x - 1))
  unless !(guarded (← scrapePAQualifiersWithReport arithmetic { mode := .standard })).isEmpty do
    throwError "guarded scraping rejected linear arithmetic"
  let quantified ← elaborate (← `(∀ k : Int → Int → Prop, ∀ x y : Int,
    ((∃ z : Int, 0 ≤ z ∧ x = z) → k x y) ∧
    (k x y → y = 7 → 0 ≤ x → False)))
  unless !(guarded (← scrapePAQualifiersWithReport quantified { mode := .standard })).isEmpty do
    throwError "quantified arithmetic seed disabled guarded scraping"

end PAScrapeTests

namespace PAWorklistTests

open Lean Meta Elab Term

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let result ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars result

private def arithmetic : PAOracle := fun target => do
  proveLeafWith (← `(tactic| omega)) target

private partial def fullScan (context : KContext) (clauses : List Expr)
    (assignment : List (KVar × List (Expr × List Nat))) (oracle : PAOracle)
    : TermElabM (List (KVar × List (Expr × List Nat))) := do
  let next ← weakenOnce context clauses assignment oracle
  if next == assignment then return next
  fullScan context clauses next oracle

-- Compare schedules with a complete arithmetic oracle on these finite candidate sets.
run_elab do
  let int := Lean.mkConst ``Int
  let predTy ← mkArrow int (mkSort .zero)
  let mut context : KContext := { kvars := {} }
  let mut predicates : Array Expr := #[]
  let mut kvars : List KVar := []
  for name in [`p, `q, `r] do
    let pred ← mkFreshExprMVar (some predTy) (kind := .syntheticOpaque)
    let κ : KVar := { name, params := [`x], paramTypes := [int], mvarId := pred.mvarId! }
    context := { kvars := context.kvars.insert κ.mvarId κ }
    predicates := predicates.push pred
    kvars := kvars ++ [κ]
  let qualifiers ← #[← `(fun x : Int => 0 ≤ x), ← `(fun x : Int => x ≤ 0),
    ← `(fun x : Int => x = 0)].mapM elaborate
  let initial := kvars.map fun κ => (κ, qualifiers.toList.map (·, [0]))
  let mut savedChecks := false
  for input in #[
      ← `(fun p q r : Int → Prop =>
        p 0 ∧ (∀ x, p x → p (x + 1)) ∧ q 0 ∧ r 7 ∧ (∀ x, p x → 0 ≤ x)),
      ← `(fun p q r : Int → Prop =>
        (∀ x, q x → p x) ∧ (∀ x, p x → q (x + 1)) ∧ p 0 ∧ r 7),
      ← `(fun p q r : Int → Prop =>
        (∀ x, p x ∧ q x → r (x + 1)) ∧ p 0 ∧ q 1 ∧ (∀ x, False → r x))] do
    let formula := (mkAppN (← elaborate input) predicates).headBeta
    let clauses ← (exprFlat formula).run context
    let referenceChecks ← IO.mkRef 0
    let worklistChecks ← IO.mkRef 0
    let reference ← fullScan context clauses initial fun target => do
      referenceChecks.modify (· + 1)
      arithmetic target
    let result ← solveFixpoint context clauses initial fun target => do
      worklistChecks.modify (· + 1)
      arithmetic target
    unless result == reference do throwError "worklist changed the fixed point"
    let batched ← solveFixpoint context clauses initial arithmetic
      (synthOracle := some arithmetic.toSynth)
    unless batched == reference do throwError "batching changed the fixed point"
    let smt ← solveFixpoint context clauses initial arithmetic
      (synthOracle := some (Flex.PA.smtOracle 2000))
    unless smt == reference do throwError "shared clause preparation changed the fixed point"
    savedChecks := savedChecks || (← worklistChecks.get) < (← referenceChecks.get)
  unless savedChecks do throwError "worklist did not skip any unaffected clauses"

  let head := kvars.head!
  let candidates := initial.head!.2
  let solutions ← finalizeSolutions initial
  let compound := (mkApp (← elaborate (← `(fun p : Int → Prop =>
    ∀ x : Int, 0 ≤ x → p x ∧ p (x + 1)))) predicates[0]!).headBeta
  let reference ← weakenClause context compound head candidates solutions arithmetic
  let batched ← weakenClause context compound head candidates solutions arithmetic
    (some (Flex.PA.smtOracle 2000))
  unless batched == reference do throwError "compound clause fallback changed the candidates"
  let clause := mkApp predicates[0]! (mkIntLit 0)
  let malformed : PASynthOracle := fun _ => pure #[]
  let rejected ← try
    discard <| weakenClause context clause head candidates solutions arithmetic (some malformed)
    pure false
  catch _ => pure true
  unless rejected do throwError "malformed batch result was accepted"
  let unknown : PASynthOracle := fun queries => pure (queries.map fun _ => .unknown "test")
  unless (← weakenClause context clause head candidates solutions arithmetic (some unknown)).isEmpty do
    throwError "unknown checks retained unvalidated candidates"
  let guardProved : PASynthOracle := fun queries =>
    pure ((queries.map fun _ => .unknown "test").set! 0 .valid)
  unless (← weakenClause context clause head candidates solutions arithmetic (some guardProved)) == candidates do
    throwError "a valid false-head guard lost candidates"

-- Predicate-valued head arguments use the same assignment as clause premises.
run_elab do
  let prop := mkSort .zero
  let p ← mkFreshExprMVar (some prop) (kind := .syntheticOpaque)
  let r ← mkFreshExprMVar (some (← mkArrow prop prop)) (kind := .syntheticOpaque)
  let pK : KVar := { name := `p, params := [], paramTypes := [], mvarId := p.mvarId! }
  let rK : KVar := { name := `r, params := [`arg], paramTypes := [prop], mvarId := r.mvarId! }
  let context : KContext := { kvars :=
    ({} : Std.HashMap MVarId KVar).insert pK.mvarId pK |>.insert rK.mvarId rK }
  let qualifier ← elaborate (← `(fun p : Prop => p))
  let identity := Expr.fvar ⟨`arg⟩
  let solutions := [(pK, Lean.mkConst ``True), (rK, identity)]
  for argument in #[p, mkApp r (mkApp r p)] do
    let vc ← (specializeClauseForHead rK qualifier [0] solutions (mkApp r argument)).run context
    unless vc.isConstOf ``True do throwError "head arguments retained an unsubstituted predicate"
  let negative ← elaborate (← `(fun p : Prop => ¬p))
  let initial := [(pK, [(Lean.mkConst ``False, [])]), (rK, [(negative, [0])])]
  let fixed ← solveFixpoint context [mkApp r p, p] initial
  unless fixed.all (·.2.isEmpty) do
    throwError "weakening a predicate argument did not revisit its enclosing head"
  if (← p.mvarId!.isAssigned) || (← r.mvarId!.isAssigned) then
    throwError "candidate specialization assigned a caller predicate"

end PAWorklistTests

open Lean Meta Elab Term in
run_elab do
  let int := Lean.mkConst ``Int
  let pred ← mkFreshExprMVar (some (← mkArrow int (mkSort .zero)))
  let κ : KVar := { name := `k, params := [`x], paramTypes := [int], mvarId := pred.mvarId! }
  let qualifiers ← #[← `(fun x : Int => 0 ≤ x),
    ← `(fun x : Int => 1 ≤ x + 1)].mapM fun q => do instantiateMVars (← elabTerm q none)
  withLocalDeclD `x int fun x => do
    withLocalDeclD `h (← mkEq x (mkIntLit 0)) fun _ => do
      -- Whole-head certification and scalar-only custom oracles prove the same type.
      for scalarOnly in #[false, true] do
        let calls ← IO.mkRef 0
        let oracle : PAOracle := fun target => do
          calls.modify (· + 1)
          if scalarOnly && target.isAppOfArity ``And 2 then return none
          proveLeafWith (← `(tactic| grind)) target
        let proof ← emitPALeaf κ (qualifiers.toList.map (·, [0])) #[x] oracle
        let bodies ← qualifiers.toList.mapM fun q => Expr.instQualifier q #[x]
        unless ← isDefEq (← inferType proof) (conjoinExprs bodies) do
          throwError "certificate changed the witness type"
        checkWithKernel (← mkLambdaFVars (← getLCtx).getFVars proof)
        unless (← calls.get) == (if scalarOnly then 3 else 1) do
          throwError "certificate unexpectedly repeated its oracle checks"

open Lean Meta Elab Term Tactic in
-- Even a dishonest synthesis oracle cannot replace the certificate proofs.
run_elab do
  let saved ← saveState
  try
    let target ← elabTerm (← `(∃ k : Int → Prop, k 0 ∧ (∀ x, k x → False))) none
    let goal ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
    let accepted ← try
      let remaining ← Tactic.run goal.mvarId! do
        fixImpl (proofOracle := some Flex.Automation.proofOracle)
          (synthOracle := some (fun targets => pure (targets.map fun _ => .valid)))
      pure remaining.isEmpty
    catch _ => pure false
    if accepted then throwError "synthesis decisions bypassed proof certification"
  finally Flex.CHC.restoreTermState saved
