import Flex.Tactic.Tactics.Fix
import Flex.Tactic.Tactics.Fusion
import Flex.Fusion.Flatten

namespace PADischargeTests

example (x : Int) (p : Prop) (hp : p) : x < x + 1 ∧ p := by
  flex_discharge

set_option flex.automation.proofHeartbeats 0 in
example (p : Prop) (hp : p) : True ∧ (True → p) := by
  flex_discharge
  guard_target = p
  exact hp

private def counter : Prop := ∃ k : Int → Prop,
  k 0 ∧ (∀ n, k n → k (n + 1)) ∧ (∀ n, k n → 0 ≤ n)

set_option flex.automation.proofHeartbeats 0 in
example : counter := by
  unfold counter
  fail_if_success fix (synth := omega)
  fix (synth := omega) (proof := omega)

set_option flex.automation.proofHeartbeats 0 in
example : counter := by
  unfold counter
  fix (oracle := omega)

end PADischargeTests

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

run_elab do
  let decode (output : String) (count : Nat) (stderr := "") :=
    Flex.PA.decodeSmtResponses { completion := .timedOut, stdout := output, stderr } count
  let .ok answers := decode "unsat\nsat\nunknown\nun" 5
    | throwError "rejected complete SMT response prefix"
  unless answers == #[.valid, .invalid, .unknown "solver returned unknown",
      .unknown "SMT batch timed out", .unknown "SMT batch timed out"] do
    throwError "timeout response indices changed"
  let .ok answers := decode "unsat" 1 | throwError "rejected incomplete response"
  unless answers == #[.unknown "SMT batch timed out"] do
    throwError "accepted a response without its newline"
  unless (decode "unsat\n" 1).toOption == some #[.valid] do
    throwError "lost a completed batch at timeout"
  for (output, count) in #[("unsat\n(error \"bad\")\n", 2), ("unsat\n(error", 2),
      ("unsat\nmalformed", 2), ("unsat\nsat\n", 1), ("unsat\nun", 1)] do
    if (decode output count).isOk then throwError "accepted malformed or extra SMT output"
  if (decode "unsat\n" 1 "error").isOk then throwError "ignored solver diagnostics"
  if (Flex.PA.decodeSmtResponses { completion := .exited 0, stdout := "unsat\n" } 2).isOk then
    throwError "accepted missing responses from a completed solver"
  if (Flex.PA.decodeSmtResponses { completion := .exited 1, stdout := "unsat\n" } 1).isOk then
    throwError "accepted responses from a failed solver"

end PABatchTests

namespace PASimplifiedSmtTests

open Lean Meta Elab Term

private structure Buffer where
  values : Int → Int
  bound : Int

run_elab do
  let terms ← #[← `(∀ b : Buffer, 0 ≤ b.bound → 0 ≤ b.bound + 1),
    ← `(∀ b : Buffer, 0 ≤ b.bound → b.bound < 0),
    ← `(∀ b : Buffer, (∀ i : Int, 0 ≤ i → b.values i = i) → b.values 1 = 1),
    ← `(∀ b : Buffer, (∀ i : Int, 0 ≤ i → b.values i = i) → b.values 1 = 2)].mapM
      fun term => elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let results ← Flex.PA.simplifiedSmtOracle 2000 (← terms.mapM instantiateMVars)
  unless results.map (fun | .valid => true | _ => false) == #[true, false, true, false] do
    throwError "simplified SMT lost record fields or shared assertions between queries: {repr results}"
  let terms ← #[← `(∀ x : Int, x ≤ x), ← `(∀ α : Type, Nonempty α),
    ← `(∀ x : Int, x ≤ x + 1)].mapM fun term => elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let results ← Flex.PA.simplifiedSmtOracle 2000 (← terms.mapM instantiateMVars)
  unless results.map (fun | .valid => true | _ => false) == #[true, false, true] do
    throwError "an unsupported candidate contaminated its batch: {repr results}"
  let term ← elabTerm (← `(∀ (α : Type) (x : Int),
    (Nonempty α ∧ x ≤ 5) → x ≤ 6)) none
  synthesizeSyntheticMVarsNoPostponing
  unless (← Flex.PA.simplifiedSmtOracle 2000 #[← instantiateMVars term]) == #[.valid] do
    throwError "an unsupported assumption hid a supported conjunct"
  let caller ← mkFreshExprMVar (some (mkConst ``Int))
  let results ← Flex.PA.simplifiedSmtOracle 2000 #[← mkEq caller (mkIntLit 0)]
  unless results.all (fun | .unknown _ => true | _ => false) do
    throwError "simplified SMT accepted an unresolved metavariable"
  if ← caller.mvarId!.isAssigned then throwError "simplified SMT assigned a caller metavariable"

end PASimplifiedSmtTests

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

-- Zap's existential guards retain clause-local candidates without mixing disjuncts.
run_elab do
  let scrape := fun term => do
    scrapePAQualifiersWithReport (← elaborate term)
      { mode := .standard, maxGuardedQualifiers := 128, maxGuardPairs := 1024 }
  let flat ← scrape (← `(∀ k : Int → Int → Prop, ∀ x y : Int,
    k x y → 0 ≤ x → y ≤ 3 → False))
  let nested ← scrape (← `(∀ k : Int → Int → Prop,
    (∃ x y : Int, k x y ∧ 0 ≤ x ∧ y ≤ 3) → False))
  unless !(guarded flat).isEmpty && guarded flat == guarded nested do
    throwError "existential guards lost flat-clause candidates"
  let branched ← scrape (← `(∀ k : Int → Int → Prop,
    (∃ x y : Int, k x y ∧ ((0 ≤ x ∧ y ≤ 3) ∨ (x ≤ 7 ∧ 11 ≤ y))) → False))
  for term in #[← `(fun x y : Int => x < 0 ∨ y ≤ 3),
      ← `(fun x y : Int => 7 < x ∨ 11 ≤ y)] do
    let expected ← elaborate term
    unless ← (guarded branched).anyM (fun q => isDefEq expected q) do
      throwError "missing branch qualifier"
  let cross ← elaborate (← `(fun x y : Int => x < 0 ∨ 11 ≤ y))
  if ← (guarded branched).anyM (fun q => isDefEq cross q) then
    throwError "combined distinct guard branches"
  for q in branched.qualifiers do
    if q.hasFVar || q.hasMVar || q.hasLooseBVars then throwError "witness binder escaped"
    check q
  let renamed ← scrape (← `(∀ k : Int → Int → Prop,
    (∃ a b : Int, k a b ∧ ((0 ≤ a ∧ b ≤ 3) ∨ (a ≤ 7 ∧ 11 ≤ b))) → False))
  unless guarded branched == guarded renamed do throwError "witness names changed candidates"
  let negative ← scrape (← `(∀ k : Int → Int → Prop,
    (¬∃ x y : Int, k x y ∧ 0 ≤ x ∧ y ≤ 3) → False))
  unless (guarded negative).isEmpty do throwError "opened a negated existential guard"

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

-- Rejected candidates must preserve Zap's progress and allow a different witness.
open Lean Meta Elab Term Tactic in
set_option flex.standardQualifiers false in
run_elab do
  let target ← elabTerm (← `(∃ seed k : Int → Prop,
    seed 0 ∧ (∀ x, seed x → k x) ∧ (∀ x, k x → k (-x)) ∧
    (∀ x, k x → x = 0))) none
  let goal ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
  let remaining ← Tactic.run goal.mvarId! do
    evalTactic (← `(tactic| zap))
    let entry ← getGoals
    let cleaned ← getMainTarget
    for oracle in #[Flex.PA.smtOracle 2000,
        fun targets => pure (targets.map fun _ => .unknown "test"),
        fun _ => pure #[]] do
      let rejected ← try
        fixImpl (proofOracle := some (fun _ => pure none)) (synthOracle := some oracle)
        pure false
      catch _ => pure true
      unless rejected do throwError "kept an invalid or unvalidated predicate"
      unless (← getGoals) == entry && (← instantiateMVars (← getMainTarget)) == cleaned do
        throwError "failed Fix discarded Zap progress or changed its remaining goal"
      if ← (← getMainGoal).isAssigned then throwError "failed Fix assigned its entry goal"
    evalTactic (← `(tactic| refine ⟨fun x : Int => x = 0, ?_⟩))
    evalTactic (← `(tactic| grind))
  unless remaining.isEmpty do throwError "could not choose a different predicate after rollback"
  checkWithKernel (← instantiateMVars goal)

-- A validated residual remains usable; an inconclusive check can use a Lean proof.
open Lean Meta Elab Term Tactic in
set_option flex.standardQualifiers false in
run_elab do
  for inconclusive in #[false, true] do
    let target ← elabTerm (← `(∃ k : Int → Prop, k 0 ∧ (∀ x, k x → x = x))) none
    let goal ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
    let remaining ← Tactic.run goal.mvarId! do
      let oracle := if inconclusive then
        fun targets => pure (targets.map fun _ => .unknown "test")
        else Flex.PA.smtOracle 2000
      let prove := if inconclusive then proveLeaf else fun _ => pure none
      fixImpl (proofOracle := some prove) (synthOracle := some oracle)
      if inconclusive then
        unless (← getGoals).isEmpty do throwError "discarded the safety proof"
      else
        unless (← getGoals).length == 1 do throwError "lost the validated residual"
        evalTactic (← `(tactic| rfl))
    unless remaining.isEmpty do throwError "validated residual could not be completed"
    checkWithKernel (← instantiateMVars goal)
  let target ← elabTerm (← `(∀ p : Prop, p → ∃ k : Int → Prop, k 0 ∧ p)) none
  let goal ← mkFreshExprMVar (some target) (kind := .syntheticOpaque)
  let remaining ← Tactic.run goal.mvarId! do
    evalTactic (← `(tactic| intros p h))
    fixImpl (synthOracle := some (fun _ => throwError "checked a predicate-independent obligation"))
    evalTactic (← `(tactic| assumption))
  unless remaining.isEmpty do throwError "lost an independent residual"
  checkWithKernel (← instantiateMVars goal)

-- Error predicates are identified by a proved constraint, not by their spelling.
open Lean Meta Elab Term in
run_elab do
  let original ← elabTerm (← `(∃ error : Prop, ∃ k : Int → Prop,
    k 0 ∧ (∀ x, k x → x < 0 → error) ∧ (∀ _ : Prop, error → False))) none
  let expected ← elabTerm (← `(∃ k : Int → Prop,
    k 0 ∧ (∀ x, k x → x < 0 → False) ∧ (∀ _ : Prop, False → False))) none
  synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let expected ← instantiateMVars expected
  let (normalized, proof) ← inlineFalsePredicates original
  unless ← isDefEq normalized expected do throwError "error predicate was not inlined"
  checkWithKernel proof
  unless ← isDefEq (← inferType proof) (← mkAppM ``Iff #[original, normalized]) do
    throwError "normalization did not prove equivalence"
  -- A guarded prohibition and a prohibition over an empty domain do not force False.
  for term in #[← `(∃ CHC_COMP_FALSE : Prop, CHC_COMP_FALSE),
      ← `(∃ p : Prop, p ∧ (False → p → False)),
      ← `(∃ p : Prop, p ∧ (∀ _ : Empty, p → False))] do
    let input ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let input ← instantiateMVars input
    let (output, proof) ← inlineFalsePredicates input
    unless output == input do throwError "inlined a proposition not forced false"
    checkWithKernel proof

open Lean Meta Elab Term in
run_elab do
  for term in #[← `(∃ k : Int → Prop, ∃ error : Prop, k 0 ∧ (k 1 → error) ∧ ¬error),
      ← `(∃ first second : Prop, (first → False) ∧ (second → False))] do
    let input ← elabTerm term none
    synthesizeSyntheticMVarsNoPostponing
    let input ← instantiateMVars input
    let (output, proof) ← inlineFalsePredicates input
    if output == input then throwError "missed an error predicate under another existential"
    if proof.hasMVar || proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
      throwError "normalization leaked proof obligations"
    checkWithKernel proof
  let caller ← mkFreshExprMVar (some (mkSort .zero))
  let target ← elabTerm (← `(∃ p : Prop, p ∧ (True → False))) none
  let target := target.replace fun e => if e.isConstOf ``True then some caller else none
  discard <| inlineFalsePredicates target
  if ← caller.mvarId!.isAssigned then throwError "normalization assigned caller metavariable"

namespace PAContextTests

open Lean Meta Elab Term

run_elab do
  let input ← elabTerm (← `(fun (p : Int → Prop) (f : Int → Int)
      (m : Int → Int → Int) =>
    (∀ t s : Int, p t ∧ f t = f s ∧ m t = m s) ∧
    (∀ u v : Int, p u ∧ f u = f v ∧ m u = m v))) none
  synthesizeSyntheticMVarsNoPostponing
  let input ← instantiateMVars input
  lambdaTelescope input fun functions body => do
    let qs ← scrapePAQualifiers body { mode := .basic }
    unless qs.size == 3 do throwError "contextual qualifiers were lost or duplicated"
    let allowed := functions.map Expr.fvarId!
    for q in qs do
      if q.hasMVar || q.hasLooseBVars ||
          !(collectFVars {} q).fvarIds.all allowed.contains then
        throwError "temporary scraping binder escaped"
      check q
    let some (clause, _) := body.and? | throwError "expected two clauses"
    forallTelescope clause fun xs _ => do
      let expected ← #[mkApp functions[0]! xs[0]!,
        ← mkEq (mkApp functions[1]! xs[0]!) (mkApp functions[1]! xs[1]!),
        ← mkEq (mkApp functions[2]! xs[0]!) (mkApp functions[2]! xs[1]!)]
        |>.mapM fun atom => mkLambdaFVars xs atom (usedOnly := true)
      for q in expected do
        unless ← qs.anyM (fun actual => do isDefEq q actual) do
          throwError "fixed function became a qualifier argument"
    withLocalDeclD `other (← inferType functions[0]!) fun other => do
      let changed := body.replaceFVar functions[0]! other
      let fresh ← scrapePAQualifiers changed { mode := .basic }
      unless fresh.any (fun q => q.containsFVar other.fvarId!) do
        throwError "new context function was not captured"
      if fresh.any (fun q => q.containsFVar functions[0]!.fvarId!) then
        throwError "qualifier capture leaked between invocations"

-- The invariant must preserve fixed semantic observations across changing states.
example (p : Int → Prop) (f : Int → Int) (m : Int → Int → Int) :
    ∃ k : Int → Int → Prop,
      (∀ s, p s → k s s) ∧
      (∀ t s u, k t s → p u → f u = f t → m u = m t → k u s) ∧
      (∀ t s, k t s → p t ∧ f t = f s ∧ m t = m s) := by
  fix (scrape := standard)

end PAContextTests

namespace PAObservationTests

open Lean Meta Elab Term

@[simp, grind] private def member (xs : List Int) (key : Int) : Prop := key ∈ xs

private def elaborate (term : TSyntax `term) : TermElabM Expr := do
  let e ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

private def observations (result : PAScrapeResult) : Array Expr :=
  result.qualifiers.zip result.origins |>.filterMap fun (q, origin) =>
    if origin == "observation relation" then some q else none

private def hasInstance (qs : Array Expr) (expected : Expr) : MetaM Bool :=
  lambdaTelescope expected fun xs body => do
    let types ← xs.toList.mapM inferType
    for q in qs do
      for (template, slots) in ← instantiateQualifier q types do
        let candidate ← Expr.instQualifier template (slots.toArray.map (xs[·]!))
        if ← isDefEq candidate body then return true
    return false

run_elab do
  let input ← elaborate (← `(∀ k : List Int → Int → List Int → Prop,
    ∀ current key original, k current key original → True = member original key))
  let expected ← elaborate (← `(fun (current : List Int) (key : Int) (original : List Int) =>
    member current key ↔ member original key))
  for mode in #[PAScrapeMode.standard, .deep] do
    let qs := observations (← scrapePAQualifiersWithReport input { mode })
    unless ← hasInstance qs expected do throwError "missing shared-key observation relation"
    for q in qs do
      if q.hasMVar || q.hasFVar || q.hasLooseBVars then throwError "observation binder escaped"
      check q
  for cfg in #[{ mode := .no }, { mode := .basic },
      { mode := .standard, maxObservationQualifiers := 0 },
      { mode := .standard, maxObservationPairs := 0 },
      { mode := .standard, maxParams := 2 }] do
    unless (observations (← scrapePAQualifiersWithReport input cfg)).isEmpty do
      throwError "observation scraping ignored its mode or limits"
  let limited ← scrapePAQualifiersWithReport input
    { mode := .standard, maxObservationQualifiers := 1 }
  unless (observations limited).size == 1 do throwError "observation template limit ignored"
  let old ← scrapePAQualifiers input
    { mode := .standard, maxQualifiers := 1, maxObservationQualifiers := 0 }
  let augmented ← scrapePAQualifiers input { mode := .standard, maxQualifiers := 1 }
  unless old == augmented do throwError "observation scraping displaced an existing template"

-- A relation requires both observations to fit one predicate occurrence in one clause.
run_elab do
  for term in #[← `(∀ k : List Int → Int → List Int → Prop,
      (∀ current key original, k current key original → True) ∧
      (∀ original key, True = member original key)),
      ← `(∀ k l : List Int → Int → Prop, ∀ current key original,
        k current key → l original key → True = member original key)] do
    let result ← scrapePAQualifiersWithReport (← elaborate term) { mode := .standard }
    unless (observations result).isEmpty do throwError "paired unrelated observations"
  let input ← elaborate (← `(fun (p : List Int → Int → Prop) =>
    ∀ k : List Int → Int → List Int → Prop, ∀ current key original,
      k current key original → True = p original key))
  lambdaTelescope input fun fixed body => do
    let qs := observations (← scrapePAQualifiersWithReport body { mode := .standard })
    let expected ← elaborate (← `(fun (p : List Int → Int → Prop)
        (current : List Int) (key : Int) (original : List Int) =>
      p current key ↔ p original key))
    unless ← hasInstance qs (mkApp expected fixed[0]!).headBeta do
      throwError "fixed semantic function was mistaken for an unknown predicate"
    for q in qs do
      unless (collectFVars {} q).fvarIds.all (· == fixed[0]!.fvarId!) do
        throwError "observation retained a temporary binder"

-- Discover preservation of membership while traversing a list, without tagged qualifiers.
example : ∃ k : List Int → Int → List Int → Prop,
    ∀ key original, k original key original ∧
      (∀ current, k current key original →
        (∀ head tail, current = head :: tail → head ≠ key → k tail key original) ∧
        (∀ head tail, current = head :: tail → head = key → member original key) ∧
        (current = [] → ¬member original key)) := by
  fix (scrape := standard)

end PAObservationTests

namespace PAQuantifiedObservationTests

open Lean Meta Elab Term

@[simp, grind] private def keyMatch (xs : List (Int × Int)) (key value : Int) : Prop :=
  xs.lookup key = some value

private def scrape (name : Name) (binders : Nat) : TermElabM PAScrapeResult := do
  let term ← `(∀ k : List (Int × Int) → Int → List (Int × Int) → Prop,
    ∀ current key original, k current key original →
      ∀ $(mkIdent name) : Int, keyMatch original key $(mkIdent name))
  let e ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  scrapePAQualifiersWithReport (← instantiateMVars e)
    { mode := .standard, maxObservationBinders := binders }

run_elab do
  let result ← scrape `v 1
  let expected ← elabTerm (← `(fun (original : List (Int × Int)) (key : Int)
      (current : List (Int × Int)) => ∀ v, keyMatch original key v ↔ keyMatch current key v)) none
  synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  unless ← result.qualifiers.anyM (fun q => isDefEq q expected) do
    throwError "missing universally quantified observation"
  unless result.qualifiers == (← scrape `renamed 1).qualifiers do
    throwError "observation binder names changed the qualifiers"
  for q in result.qualifiers do
    if q.hasMVar || q.hasFVar || q.hasLooseBVars then throwError "observation binder escaped"
    check q
  if ← (← scrape `v 0).qualifiers.anyM (fun q => isDefEq q expected) then
    throwError "universal observation ignored its binder limit"

example : ∃ k : List (Int × Int) → Int → List (Int × Int) → Prop,
    (∀ key original, k original key original) ∧
    (∀ key original current head value tail, k current key original →
      current = (head, value) :: tail → head ≠ key → k tail key original) ∧
    (∀ key original current value tail, k current key original →
      current = (key, value) :: tail → keyMatch original key value) := by
  fix (scrape := standard)

end PAQuantifiedObservationTests

namespace PAFieldObservationTests

open Lean Meta Elab Term

private structure Block where
  values : Int → Int
  size : Int

@[simp] private def ordered (a : Int → Int) (n : Int) : Prop :=
  ∀ i j, 0 ≤ i → i < j → j < n → a i ≤ a j

run_elab do
  let input ← elabTerm (← `(∀ k : (Int → Int) → Int → Prop,
    ∀ block : Block, k block.values block.size → ordered block.values block.size)) none
  let expected ← elabTerm (← `(fun (a : Int → Int) (n : Int) => ordered a n)) none
  synthesizeSyntheticMVarsNoPostponing
  let input ← instantiateMVars input
  let expected ← instantiateMVars expected
  let result ← scrapePAQualifiersWithReport input { mode := .standard }
  unless ← result.qualifiers.anyM (fun q => isDefEq q expected) do
    throwError "record fields did not become predicate parameters"
  for q in result.qualifiers do
    if q.hasMVar || q.hasFVar || q.hasLooseBVars then throwError "record binder escaped"
    check q
  let disabled ← scrapePAQualifiers input { mode := .standard, maxObservationQualifiers := 0 }
  if ← disabled.anyM (fun q => isDefEq q expected) then
    throwError "field abstraction ignored its budget"

example : ∃ k : Int → (Int → Int) → Int → Prop,
    (∀ block : Block, 0 < block.size → k 1 block.values block.size) ∧
    (∀ n (block next : Block), k n block.values block.size → n < block.size →
      next.size = block.size → ordered next.values (n + 1) →
      k (n + 1) next.values next.size) ∧
    (∀ n (block : Block), k n block.values block.size → ¬n < block.size →
      ordered block.values block.size) := by
  fix (scrape := deep)

private structure DependentBlock where
  size : Nat
  index : Fin (size + 1)

private def accepts (size : Nat) (index : Fin (size + 1)) : Prop := index.val ≤ size

run_elab do
  let input ← elabTerm (← `(∀ k : Nat → DependentBlock → Prop,
    ∀ block : DependentBlock, k block.size block → accepts block.size block.index)) none
  synthesizeSyntheticMVarsNoPostponing
  let result ← scrapePAQualifiersWithReport (← instantiateMVars input) { mode := .standard }
  if result.origins.contains "predicate arguments" then
    throwError "abstracted a field needed by another argument's type"
  for q in result.qualifiers do check q

end PAFieldObservationTests

namespace PAStructuredTests

@[simp] private def sorted (a : Int → Int) (n : Int) : Prop :=
  ∀ i j, 0 ≤ i → i < j → j < n → a i ≤ a j

@[simp] private def update (a : Int → Int) (i v : Int) : Int → Int :=
  fun j => if j = i then v else a j

-- These check generated predicates with automation, not just definitional equality.
example : ∃ k : Int → (Int → Int) → Int → Prop,
    ∀ n, 0 ≤ n →
      (∀ a, k 0 a n) ∧
      (∀ i a, k i a n →
        (¬ i < n → sorted a n) ∧
        (i < n → k (i + 1) (update a i i) n)) := by
  fix (scrape := deep)

example : ∃ k : List (List Int) → Int → Int → Prop,
    (∀ n, 0 ≤ n → k [] n n) ∧
    (∀ slots remaining n, k slots remaining n → 0 < remaining →
      k (slots ++ [[]]) (remaining - 1) n) ∧
    (∀ slots remaining n, k slots remaining n → ¬ 0 < remaining →
      slots = List.replicate n.toNat []) := by
  fix (scrape := deep)

open Lean Meta Elab Term

private def five (a b c d e : Int) : Prop := a + b + c + d ≤ e

private def segment (a : Int → Int) (offset : Int) (b : Int → Int)
    (start len : Int) : Prop :=
  ∀ i : Int, 0 ≤ i → i < len → a (offset + i) = b (start + i)

run_elab do
  let source ← elabTerm (← `(fun (a b : Int → Int) (base lo hi : Int) =>
    segment a (base + lo) b lo (hi - lo))) none
  let expected ← elabTerm (← `(fun (a b : Int → Int) (base lo hi : Int) =>
    ∀ j, lo ≤ j → j < hi → a (base + j) = b j)) none
  synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let expected ← instantiateMVars expected
  lambdaTelescope source fun xs body => do
    let candidates ← PAScrape.Structured.absoluteIndexCandidates body
    unless ← candidates.anyM (fun q => isDefEq q (expected.beta xs)) do
      throwError "missing absolute-index candidate"
    for q in candidates do
      check q
      unless (collectFVars {} q).fvarIds.all (fun id => xs.contains (mkFVar id)) do
        throwError "escaped coordinate binder"
    unless (← PAScrape.Structured.absoluteIndexCandidates body 0).isEmpty do
      throwError "ignored reindexing limit"
  let target ← elabTerm (← `(∀ (a b : Int → Int) (base lo hi : Int),
    (∀ j, lo ≤ j → j < hi → a (base + j) = b j) →
      segment a (base + lo) b lo (hi - lo))) none
  synthesizeSyntheticMVarsNoPostponing
  let proof ← withOptions (·.set `flex.automation.smtTimeout (0 : Nat)) <|
    Flex.Automation.proofOracle (← instantiateMVars target)
  unless proof.isSome do throwError "could not certify the reindexed specification"

run_elab do
  let term ← elabTerm (← `(fun r : Int → Int → Int → Int → Int → Prop =>
    ∀ a b c d e x, r a b c d e → (0 ≤ e → x = e - 1) →
      five a b c d (x + 1))) none
  synthesizeSyntheticMVarsNoPostponing
  let term ← instantiateMVars term
  let r ← mkFreshExprMVar (some term.bindingDomain!) (kind := .syntheticOpaque)
  let body := term.bindingBody!.instantiate1 r
  let result ← scrapePAQualifiersWithReport body { mode := .standard }
  let expected ← elabTerm (← `(fun a b c d e : Int => five a b c d e)) none
  unless ← result.anchored.anyM (fun q => isDefEq expected q.qualifier) do
    throwError "missing source instance through a guarded alias"
  for q in result.anchored do
    if q.qualifier.hasMVar || q.qualifier.hasFVar || q.qualifier.hasLooseBVars then
      throwError "source instance retained a temporary binder"
    check q.qualifier
  unless (← scrapePAQualifiersWithReport body
      { mode := .standard, maxAnchoredAttempts := 0 }).anchored.isEmpty do
    throwError "source instance budget ignored"

run_elab do
  let r ← mkFreshExprMVar (some (← elabTerm (← `(Int → Prop)) none))
  let κ : KVar := {
    name := `k
    mvarId := r.mvarId!
    params := [`x]
    paramTypes := [mkConst ``Int] }
  let bad ← elabTerm (← `(fun b : Bool => b = true)) none
  synthesizeSyntheticMVarsNoPostponing
  let bad ← instantiateMVars bad
  let rejected ← try
    discard <| buildInitialAssignment [κ] #[] (some 0) (some 0)
      #[{ kvar := r.mvarId!, qualifier := bad, slots := [0], origin := "invalid fixture" }]
    pure false
  catch _ => pure true
  unless rejected do throwError "source instance accepted mismatched argument types"
  if ← r.mvarId!.isAssigned then throwError "source validation assigned its predicate"

run_elab do
  let type ← mkFreshExprMVar (some (mkSort (.succ .zero)))
  let property ← elabTerm (← `(List.replicate 2 (0 : Int))) none
  synthesizeSyntheticMVarsNoPostponing
  withLocalDeclD `xs (← mkAppM ``List #[type]) fun xs => do
    let candidates ← PAScrape.Structured.listCandidates #[← instantiateMVars property] #[xs]
    unless candidates.isEmpty do throwError "list candidates accepted an unresolved element type"
    if ← type.mvarId!.isAssigned then throwError "list scraping assigned the caller's type"

private def region (a : Int → Int) (l m r p : Int) : Prop :=
  ∀ x, l ≤ x → x < m → a x ≤ a p ∧ m ≤ r

run_elab do
  let source ← elabTerm (← `(fun (i j : Int) (a : Int → Int) (lo hi : Int) =>
    region (update a i (a hi)) lo i (hi + 1) i)) none
  synthesizeSyntheticMVarsNoPostponing
  lambdaTelescope (← instantiateMVars source) fun xs property => do
    let candidates ← PAScrape.Structured.compoundCandidates #[property] xs
    let expected := mkAppN (mkConst ``region) #[xs[2]!, xs[3]!, xs[0]!, xs[1]!, xs[4]!]
    unless candidates.contains expected do throwError "missing compound-argument candidate"
    for q in candidates do
      check q
      if q.hasMVar || q.hasLooseBVars then throwError "unresolved compound candidate"
      unless (collectFVars {} q).fvarIds.all (fun id => xs.contains (mkFVar id)) do
        throwError "compound candidate retained a temporary binder"
    unless (← PAScrape.Structured.compoundCandidates #[property] xs 0).isEmpty &&
        (← PAScrape.Structured.compoundCandidates #[property] xs 1).size == 1 do
      throwError "compound candidate limit ignored"
    unless (← PAScrape.Structured.compoundCandidates #[property, property] xs) == candidates do
      throwError "duplicate source changed compound candidates"
    let r ← mkFreshExprMVar (some (← mkForallFVars xs (mkSort .zero)))
    let body ← mkForallFVars xs (← mkArrow (mkAppN r xs) property)
    let old ← scrapePAQualifiersWithReport body
      { mode := .deep, maxCompoundCandidatesPerKappa := 0 }
    let new ← scrapePAQualifiersWithReport body
      { mode := .deep, maxCompoundCandidatesPerKappa := 24 }
    unless !old.anchored.isEmpty && new.anchored.any (·.origin == "compound arguments") do
      throwError "missing ordinary or supplemental anchor"
    unless old.qualifiers == new.qualifiers do throwError "compound pass changed ordinary templates"
    for candidate in old.anchored do
      unless new.anchored.any (fun q => q.kvar == candidate.kvar &&
          q.slots == candidate.slots && q.qualifier == candidate.qualifier) do
        throwError "compound pass displaced an ordinary anchor"

end PAStructuredTests

namespace PAFunctionBatchTests
open Lean Meta Elab Term
private abbrev Mapping (α β : Type) [Inhabited β] := α → β
private def related (a : Mapping Int Int) (i : Int) : Prop := a i ≤ a (i + 1)
run_elab do
  let stxs ← pure #[
    ← `(∀ (a b : Mapping Int Int) (i : Int), a = b → related a i → related b i),
    ← `(∀ (a b : Mapping Int Int) (i : Int), a = b → related a i → False),
    ← `(∀ (a b : Mapping Int Int) (i : Int), a = b → related a i → a i = b i)]
  let queries ← stxs.mapM (fun stx => elabTerm stx none)
  synthesizeSyntheticMVarsNoPostponing
  let queries ← queries.mapM instantiateMVars
  let results ← Flex.PA.functionSmtOracle 2000 queries
  unless results.size == 3 && results[0]! == .valid && results[2]! == .valid do
    throwError "function-valued batch lost a valid candidate: {repr results}"
  if results[1]! == .valid then throwError "function batch mixed candidate assertions"
  let x ← mkFreshExprMVar (some (mkConst ``Int))
  let result ← Flex.PA.functionSmtOracle 2000 #[← mkEq x (mkIntLit 0)]
  if result[0]! == .valid || (← x.mvarId!.isAssigned) then
    throwError "function batch accepted or assigned an unresolved input"
end PAFunctionBatchTests
