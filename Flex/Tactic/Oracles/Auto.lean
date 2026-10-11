import Auto.Tactic
import Batteries.Tactic.OpenPrivate
import Flex.Tactic.Oracles.Stats

open Lean Meta Elab Tactic Auto Embedding.Lam

/-!
  # `flex_auto`: lean-auto's trusted SMT mode, specialised for PA queries

  PA issues many small, closely related queries (one per candidate per clause
  per Houdini round). Running stock `auto` on each pays two per-query costs that
  do not depend on the query:

  * **A fresh solver process.** `Auto.Solver.SMT.querySolver` spawns `z3` for
    every call. Here one `z3 -in` process is kept per Lean process and reused;
    each query starts with `(reset)` so no state leaks between queries, and a
    per-query `:timeout` replaces the process-wide `-T`.
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

register_option flex.auto.fastMono : Bool := {
  defValue := true
  descr := "flex_auto: skip monomorphization saturation when all lemmas are already monomorphic."
}

namespace Flex.AutoOracle

/-! ## Shared solver session -/

abbrev Z3Proc := IO.Process.Child ⟨.piped, .piped, .null⟩

structure Session where
  proc    : Z3Proc
  queries : Nat

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

/-- Send `cmds` to the shared z3 process and return its `check-sat` answer.
    The trailing `echo` sentinel keeps reads aligned even if z3 prints error
    lines for individual commands. A dead process is replaced on next use. -/
def queryShared (cmds : Array IR.SMT.Command) (timeoutMs : Nat) : IO (Option String) := do
  let s ← match ← sessionRef.get with
    | some s => pure s
    | none => pure { proc := ← spawnZ3, queries := 0 }
  sessionRef.set (some s)
  let sync := s!"flex-sync-{s.queries}"
  try
    let mut buf := s!"(reset)\n(set-option :timeout {timeoutMs})\n"
    for c in cmds do
      buf := buf ++ s!"{c}\n"
    buf := buf ++ s!"(check-sat)\n(echo \"{sync}\")\n"
    s.proc.stdin.putStr buf
    s.proc.stdin.flush
    let mut answer := none
    repeat
      let line ← s.proc.stdout.getLine
      if line.isEmpty then
        throw <| IO.userError "flex_auto: z3 exited unexpectedly"
      let line := line.trimAscii.toString
      if line == sync then break
      if line == "sat" || line == "unsat" || line == "unknown" then
        answer := some line
    sessionRef.set (some { s with queries := s.queries + 1 })
    return answer
  catch e =>
    dropSession
    throw e

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

def monomorphize (lemmas inhFacts : Array Lemma) (k : Reif.State → MetaM α) : MetaM α := do
  let fast := flex.auto.fastMono.get (← getOptions)
  if fast && (← lemmas.allM isFirstOrderMono) then
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
        let body := commands.foldl (fun acc c => acc ++ s!"{c}\n") ""
        IO.FS.createDirAll dir
        IO.FS.writeFile s!"{dir}/q{n}.smt2" s!"; answer: {answer}\n{body}(check-sat)\n"
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

end Flex.AutoOracle

/-- lean-auto's trusted SMT mode, specialised for PA queries (see module doc).
    Solver timeout uses `auto.smt.timeout`; the solver is always z3. Accepts
    auto's hypothesis and definition hints, e.g. `[*] d[fib]`.

    Use `fix (synth := flex_auto)` to prefer it during candidate checking,
    or `fix (oracle := flex_auto)` as a Lean-first fallback for all phases.
    Successful SMT calls use lean-auto's `autoSMTSorry` axiom; a separate proof
    oracle rebuilds the certificate without those synthesis proof terms. -/
elab "flex_auto" hs:hints us:uord* : tactic =>
  withOptions (fun o => (o.setBool `auto.smt true).setBool `auto.smt.trust true) do
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

/-- The stock lean-auto pipeline (fresh solver per query, full
    monomorphization), kept for comparison with `flex_auto`. -/
macro "flex_auto_stock" hs:hints us:uord* : tactic =>
  `(tactic| set_option auto.smt true in
    set_option auto.smt.trust true in
      auto $hs:hints $[$us:uord]*)
