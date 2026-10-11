import Auto.Tactic
import Batteries.Tactic.OpenPrivate
import Flex.Tactic.Oracles.Stats
import Flex.PA.Check

open Lean Meta Elab Tactic Auto Embedding.Lam

/-!
  # `flex_auto`: lean-auto's trusted SMT mode, specialised for PA queries

  PA issues many small, closely related queries (one per candidate per clause
  per Houdini round). Running stock `auto` on each pays two per-query costs that
  do not depend on the query:

  * **A fresh solver process.** `Auto.Solver.SMT.querySolver` spawns `z3` for
    every call. Here one `z3 -in` process is kept per Lean process and reused;
    each query runs in a `(push)`/`(pop)` scope so no state leaks between
    queries, and a `:timeout` option replaces the process-wide `-T`.
  * **Monomorphization saturation.** PA queries are first-order facts over
    concrete types. Saturation still runs quadratic `instanceOf?` searches
    (term-like and instance defeqs) that cannot add instances for such input.
    When every lemma is monomorphic, `flex_auto` builds only the constant-
    instance map the later translation needs. Otherwise it uses lean-auto's
    full monomorphization.

  The translation (reification, verified preprocessing, `lamFOL2SMT`) is
  lean-auto's own. Options `flex.auto.shareSolver` and `flex.auto.fastMono`
  restore the stock behaviour of each part, for comparison.
-/

register_option flex.auto.shareSolver : Bool := {
  defValue := true
  descr := "flex_auto: reuse one z3 process across queries instead of spawning one per query."
}

register_option flex.auto.dumpDir : String := {
  defValue := ""
  descr := "flex_auto: if set, write each shared-solver query and its answer to this directory."
}

register_option flex.auto.batchClauses : Bool := {
  defValue := true
  descr := "flex_auto as a synthesis oracle: translate each clause visit once and check all its candidates in one solver scope."
}

register_option flex.auto.fastMono : Bool := {
  defValue := true
  descr := "flex_auto: skip monomorphization saturation when all lemmas are already monomorphic."
}

namespace Flex.AutoOracle

/-! ## Shared solver session -/

abbrev Z3Proc := IO.Process.Child ⟨.piped, .piped, .null⟩

structure Session where
  proc      : Z3Proc
  queries   : Nat
  timeoutMs : Option Nat := none

initialize sessionRef : IO.Ref (Option Session) ← IO.mkRef none

/-- Spawn z3 and wait until it answers, so start-up cost is measured here
    (`auto.spawn`) rather than in the first query. -/
private def spawnZ3 : IO Z3Proc := OracleStats.time "auto.spawn" do
  let proc ← IO.Process.spawn { cmd := "z3", args := #["-in", "-smt2"],
                                stdin := .piped, stdout := .piped, stderr := .null }
  proc.stdin.putStr "(echo \"flex-ready\")\n"
  proc.stdin.flush
  let line ← proc.stdout.getLine
  unless line.trimAscii.toString == "flex-ready" do
    throw <| IO.userError s!"flex_auto: unexpected z3 start-up output: {line}"
  return proc

private def dropSession : IO Unit := do
  if let some s ← sessionRef.get then
    try s.proc.kill catch _ => pure ()
  sessionRef.set none

/-- Write a script to the shared z3 process and collect answers. `build`
    receives a tag unique to this exchange and returns the script and the
    markers it echoes, in order; for each marker the result is the last
    `check-sat` answer printed before it. Echoed markers keep reads aligned even
    if z3 prints error lines. A dead process is replaced on next use. -/
def exchange (timeoutMs : Nat) (build : String → String × Array String)
    : IO (Array (Option String)) := do
  let s ← match ← sessionRef.get with
    | some s => pure s
    | none => pure { proc := ← spawnZ3, queries := 0 }
  sessionRef.set (some s)
  let (script, markers) := build s!"flex-{s.queries}"
  try
    let pre := if s.timeoutMs == some timeoutMs then ""
      else s!"(set-option :timeout {timeoutMs})\n"
    s.proc.stdin.putStr (pre ++ script)
    s.proc.stdin.flush
    let mut answers := #[]
    for marker in markers do
      let mut answer := none
      repeat
        let line ← s.proc.stdout.getLine
        if line.isEmpty then
          throw <| IO.userError "flex_auto: z3 exited unexpectedly"
        let line := line.trimAscii.toString
        if line == marker then break
        if line == "sat" || line == "unsat" || line == "unknown" then
          answer := some line
      answers := answers.push answer
    sessionRef.set (some { s with queries := s.queries + 1, timeoutMs := some timeoutMs })
    return answers
  catch e =>
    dropSession
    throw e

def render (cmds : Array IR.SMT.Command) : String :=
  cmds.foldl (fun acc c => acc ++ s!"{c}\n") ""

/-- One query in its own `(push)`/`(pop)` scope, which discards its
    declarations and assertions. `(reset)` would too, but costs ~4 ms per query
    against ~0.2 ms. -/
def queryShared (cmds : Array IR.SMT.Command) (timeoutMs : Nat) : IO (Option String) := do
  let answers ← exchange timeoutMs fun tag =>
    (s!"(push)\n{render cmds}(check-sat)\n(pop)\n(echo \"{tag}\")\n", #[tag])
  return answers[0]!

/-! ## Monomorphization fast path -/

open private collectConstInsts from Auto.Translation.Monomorphization

/-- No universe parameters and no binder ranging over types, classes or
    functions. Saturation cannot instantiate such a lemma further. -/
def isFirstOrderMono (lem : Lemma) : MetaM Bool := do
  if lem.params.size != 0 then return false
  forallTelescope lem.type fun xs _ => xs.allM fun x => do
    let ty ← inferType x
    if ← isProp ty then return true
    if ty.isSort || ty.isForall then return false
    return (← isClass? ty).isNone

open Monomorphization in
/-- Saturation-free `monoMAction`: register the constant instances occurring
    in the lemmas, then apply the same `monomorphic?` filter as
    `getAllMonoLemmaInsts`. -/
def fastMonoAction (lemmas : Array Lemma) : MonoM (LemmaInsts × Array (Array SimpleIndVal)) := do
  for lem in lemmas do
    for ci in ← collectConstInsts lem.params #[] lem.type do
      processConstInst ci
  let lis ← lemmas.filterMapM fun lem => do
    LemmaInst.monomorphic? (← LemmaInst.ofLemmaHOL lem)
  return (lis, ← collectMonoMutInds)

/-- `orderPreserving` demands the fast path, whose output facts follow the
    input lemmas one-to-one (per-clause batches rely on positions). -/
def monomorphize (lemmas inhFacts : Array Lemma) (k : Reif.State → MetaM α)
    (orderPreserving := false) : MetaM α := do
  let fast := flex.auto.fastMono.get (← getOptions) || orderPreserving
  let firstOrder ← lemmas.allM isFirstOrderMono
  if orderPreserving && !firstOrder then
    throwError "flex_auto :: batching needs first-order monomorphic lemmas"
  if fast && firstOrder then
    let ((lis, inds), st) ← OracleStats.time "auto.mono" <|
      (fastMonoAction lemmas).run {}
    MetaState.runWithIntroducedFVars
      (Monomorphization.monomorphize.metaStateMAction inhFacts lis inds st) k
  else
    OracleStats.record "auto.mono_full" 0
    Monomorphization.monomorphize lemmas inhFacts k

/-! ## Pipeline -/

/-- lean-auto's `runAuto.reifMAction`, restricted to SMT with trusted output. -/
def reifAndQuery (uvalids uinhs : Array UMonoFact) (minds : Array (Array SimpleIndVal))
    : LamReif.ReifM Expr := do
  let (commands, _) ← OracleStats.time "auto.reif" do
    let exportFacts ← LamReif.reifFacts uvalids
    let exportFacts := exportFacts.map (REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInds ← LamReif.reifMutInds minds
    let (exportFacts, exportInds) ← LamReif.preprocess exportFacts exportInds
    let lamVarTy := (← LamReif.getVarVal).map Prod.snd
    let lamEVarTy ← LamReif.getLamEVarTy
    let terms ← exportFacts.mapM fun
      | .valid [] t => pure t
      | _ => throwError "flex_auto :: unexpected non-valid fact"
    let sni : SMT.SMTNamingInfo :=
      { tyVal := ← LamReif.getTyVal, varVal := ← LamReif.getVarVal, lamEVarTy }
    let (res, _) ← (lamFOL2SMT sni lamVarTy lamEVarTy terms exportInds).run
    pure res
  for cmd in commands do
    trace[auto.smt.printCommands] "{cmd}"
  let opts ← getOptions
  let unsat ← OracleStats.time "auto.solver" do
    if flex.auto.shareSolver.get opts then
      let timeoutMs := auto.smt.timeout.get opts * 1000
      let answer ← queryShared commands timeoutMs
      let dir := flex.auto.dumpDir.get opts
      unless dir.isEmpty do
        let n := ((← sessionRef.get).map (·.queries)).getD 0
        IO.FS.createDirAll dir
        IO.FS.writeFile s!"{dir}/q{n}.smt2" s!"; answer: {answer}\n{render commands}(check-sat)\n"
      pure (answer == some "unsat")
    else
      pure (← Solver.SMT.querySolver commands).isSome
  unless unsat do throwError "flex_auto :: SMT solver did not prove the goal"
  Meta.mkAppM ``autoSMTSorry #[.const ``False []]

def run (lemmas inhFacts : Array Lemma) : MetaM Expr := Meta.withDefault do
  let lemmas ← rewriteIteCondDecide lemmas
  let (proof, _) ← monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
    let s ← get
    let u ← computeMaxLevel s.facts
    (reifAndQuery s.facts s.inhTys s.inds).run' { u := u })
  return proof

/-! ## Per-clause batches

  Houdini weakening checks, per clause visit, the sat-guard `∀ x̄, H → False`
  and every candidate `∀ x̄, H → c(ā)`. They share binders and hypotheses, so
  the batch opens the binders once, runs lean-auto once over the context and
  all negated candidate goals (one monomorphization, one reification), and
  checks everything in one z3 scope: the context is asserted once, the
  sat-guard is a plain `check-sat`, and each candidate adds its negated goal
  in a nested `(push)`/`(pop)`. Facts are attributed to candidates through
  lean-auto's derivation leaves. -/

private def goalTag (i : Nat) : String := s!"flexGoal {i}"

private def goalIndex? (leaf : String) : Option Nat :=
  if leaf.startsWith "flexGoal " then (leaf.drop 9).toNat? else none

/-- The leaf of candidate VC `c` under the binder prefix it shares with
    `vacuity = ∀ x̄, False`; loose bound variables refer to that prefix. -/
partial def leafUnder? : Expr → Expr → Option Expr
  | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => if d₁ == d₂ then leafUnder? b₁ b₂ else none
  | .const ``False _, c => some c
  | _, _ => none

/-- The candidate whose negated goal a `valid_fact_j` assertion is: goals
    come first, so fact `j < nGoals` is candidate `j`'s. -/
private def factOwner? (nGoals : Nat) : IR.SMT.Command → Option Nat
  | .assert (.attr _ #[.symb "named" name]) =>
    if name.startsWith "valid_fact_" then (name.drop 11).toNat?.filter (· < nGoals) else none
  | _ => none

/-- Translate the negated candidate goals and the context in one lean-auto
    run. Returns the commands shared by all candidates (declarations, context
    facts) and, per candidate, the assertions of its negated goal.

    Facts are matched to candidates by position. The goals are the first
    `nGoals` input facts; reification is one-to-one, and preprocessing maps
    facts one-to-one except that definitions (`x = t`) are removed after being
    substituted into the others, which keeps the order of the rest. A negated
    goal is never definition-shaped, so the goals keep their positions.
    (Derivations cannot be used after reification: it merges identical terms,
    e.g. `0 ≤ ν` and `0 ≤ x` once `ν = x` has been substituted.) -/
def translateClause (nGoals : Nat) (uvalids uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal))
    : LamReif.ReifM (Array IR.SMT.Command × Array (Array IR.SMT.Command)) := do
  for i in [0:nGoals] do
    unless uvalids[i]?.any (·.deriv.collectLeafStrings.contains (goalTag i)) do
      throwError "flex_auto :: candidate goal {i} is not fact {i} after monomorphization"
  let exportFacts ← LamReif.reifFacts uvalids
  let exportFacts := exportFacts.map (REntry.valid [])
  let _ ← LamReif.reifInhabitations uinhs
  let exportInds ← LamReif.reifMutInds minds
  let (exportFacts, exportInds) ← LamReif.preprocess exportFacts exportInds
  if exportFacts.size < nGoals then
    throwError "flex_auto :: preprocessing removed a candidate goal"
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let terms ← exportFacts.mapM fun
    | .valid [] t => pure t
    | _ => throwError "flex_auto :: unexpected non-valid fact"
  let sni : SMT.SMTNamingInfo :=
    { tyVal := ← LamReif.getTyVal, varVal := ← LamReif.getVarVal, lamEVarTy }
  let ((commands, _), _) ← (lamFOL2SMT sni lamVarTy lamEVarTy terms exportInds).run
  let mut shared := #[]
  let mut goals : Array (Array IR.SMT.Command) := Array.replicate nGoals #[]
  for cmd in commands do
    match factOwner? nGoals cmd with
    | some i => goals := goals.modify i (·.push cmd)
    | none => shared := shared.push cmd
  return (shared, goals)

/-- One lemma `¬ gᵢ` per candidate goal, tagged and first (see
    `translateClause`), then the lemmas of the context (per `hs`, `us`). The goal lemmas carry a
    placeholder proof: batch results are verdicts, never proof terms. -/
private def collectClause (hs : TSyntax ``Auto.hints) (us : Array (TSyntax ``Auto.uord))
    (xs goals : Array Expr) : TermElabM (Array Lemma × Array Lemma) := do
  let mvar ← mkFreshExprMVar (mkConst ``False)
  let out ← IO.mkRef (#[], #[])
  discard <| Tactic.run mvar.mvarId! do
    let (lemmas, inhFacts) ← collectAllLemmas hs us (xs.map (·.fvarId!))
    let unfolds ← Prep.topoSortUnfolds (← parseUOrDs us).1
    let goalLemmas ← goals.mapIdxM fun i g => do
      let ty := mkNot g
      unfoldConstAndPreprocessLemma unfolds
        ⟨⟨mkApp (.const ``autoSMTSorry [.zero]) ty, ty, .leaf (goalTag i)⟩, #[]⟩
    out.set (goalLemmas ++ lemmas, inhFacts)
  out.get

/-- Batched `flex_auto` for one clause visit; see `PASynthOracle.checkClause`. -/
def checkClause (hs : TSyntax ``Auto.hints) (us : Array (TSyntax ``Auto.uord))
    (vacuity : Expr) (candidates : Array Expr) : TermElabM (Option (Array Bool)) := do
  let some leaves := candidates.mapM (leafUnder? vacuity)
    | throwError "flex_auto :: candidate VCs do not share the clause's binders"
  forallTelescope vacuity fun xs body => do
    unless body.isConstOf ``False do
      throwError "flex_auto :: unexpected sat-guard shape{indentExpr body}"
    let goals := leaves.map (·.instantiateRev xs)
    let (lemmas, inhFacts) ← OracleStats.time "auto.collect" <| collectClause hs us xs goals
    let ((shared, goalCmds), _) ← Meta.withDefault do
      let lemmas ← rewriteIteCondDecide lemmas
      monomorphize lemmas inhFacts (@id (Reif.ReifM _) do
        let s ← get
        let u ← computeMaxLevel s.facts
        OracleStats.time "auto.reif" <|
          (translateClause goals.size s.facts s.inhTys s.inds).run' { u := u })
        (orderPreserving := true)
    let timeoutMs := auto.smt.timeout.get (← getOptions) * 1000
    OracleStats.time "auto.solver" do
      let guard ← exchange timeoutMs fun tag =>
        (s!"(push)\n{render shared}(check-sat)\n(echo \"{tag}\")\n", #[tag])
      if guard[0]! == some "unsat" then
        discard <| exchange timeoutMs fun _ => ("(pop)\n", #[])
        return none
      let ids := (List.range goalCmds.size).toArray.filter (!goalCmds[·]!.isEmpty)
      let answers ← exchange timeoutMs fun tag =>
        let checks := ids.foldl (init := "") fun acc i =>
          acc ++ s!"(push)\n{render goalCmds[i]!}(check-sat)\n(pop)\n(echo \"{tag}-{i}\")\n"
        (checks ++ s!"(pop)\n(echo \"{tag}\")\n", (ids.map (s!"{tag}-{·}")).push tag)
      let mut ok := Array.replicate goalCmds.size false
      for (i, answer) in ids.zip answers do
        ok := ok.set! i (answer == some "unsat")
      trace[flex.oracle] "flex_auto batch: {goals.size} candidates, untranslated \
        {(List.range goalCmds.size).filter (goalCmds[·]!.isEmpty)}, answers {answers}"
      return some ok

end Flex.AutoOracle

/-- lean-auto's trusted SMT mode, specialised for PA queries (see module doc).
    Solver timeout uses `auto.smt.timeout`; the solver is always z3. Accepts
    auto's hypothesis and definition hints, e.g. `[*] d[fib]`.

    Use `fix (synth := flex_auto)` to prefer it during candidate checking,
    or `fix (oracle := flex_auto)` as a Lean-first fallback for all phases.
    Successful SMT calls use lean-auto's `autoSMTSorry` axiom; a separate proof
    oracle rebuilds the certificate without those synthesis proof terms. -/
syntax (name := flexAuto) "flex_auto" hints uord* : tactic

private def withAutoSMT {m : Type → Type} {α : Type} [MonadWithOptions m] (k : m α) : m α :=
  withOptions (fun o => (o.setBool `auto.smt true).setBool `auto.smt.trust true) k

elab_rules : tactic
  | `(tactic| flex_auto $hs:hints $us:uord*) => withAutoSMT do
  Flex.OracleStats.reportCall ((← getOptions).getBool `flex.benchOracles)
      "flex_auto" (fun _ => "proved") <|
  Flex.OracleStats.time "auto.total" <| withMainContext do
    let (binders, goal) ← (← getMainGoal).intros
    let [nngoal] ← goal.apply (.const ``Classical.byContradiction [])
      | throwError "flex_auto :: unexpected result of Classical.byContradiction"
    let (ngoal, absurd) ← nngoal.intro1
    replaceMainGoal [absurd]
    withMainContext do
      let (lemmas, inhFacts) ← Flex.OracleStats.time "auto.collect" <|
        collectAllLemmas hs us (binders.push ngoal)
      absurd.assign (← Flex.AutoOracle.run lemmas inhFacts)

/-- As a synthesis oracle (`fix (synth := flex_auto …)` or `(oracle := …)`),
    `flex_auto` answers each clause visit from one translation. On any failure
    of the batch it reverts to per-query calls for that clause. -/
initialize registerPASynthBuilder ``flexAuto fun tac trust => do
  let opts ← getOptions
  unless flex.auto.batchClauses.get opts && flex.auto.shareSolver.get opts do return none
  let `(tactic| flex_auto $hs:hints $us:uord*) := tac | return none
  let perQuery := PASynthOracle.ofOracle (proveLeafWith ⟨tac⟩ · trust)
  return some { checkClause := fun vacuity candidates => do
    let saved ← saveState
    try
      Flex.OracleStats.reportCall (opts.getBool `flex.benchOracles) "flex_auto_clause"
          (fun r => if r.isSome then "checked" else "vacuous") do
        Flex.OracleStats.record "batch.candidates" candidates.size
        withAutoSMT <| withSilencedMessages <| withNewMCtxDepth <|
          Flex.OracleStats.time "auto.total" <|
            Flex.AutoOracle.checkClause hs us vacuity candidates
    catch e =>
      saved.restore
      trace[flex.oracle] "flex_auto batch failed, using per-query calls: {e.toMessageData}"
      perQuery.checkClause vacuity candidates }

/-- The stock lean-auto pipeline (fresh solver per query, full
    monomorphization), kept for comparison with `flex_auto`. -/
macro "flex_auto_stock" hs:hints us:uord* : tactic =>
  `(tactic| set_option auto.smt true in
    set_option auto.smt.trust true in
      auto $hs:hints $[$us:uord]*)
