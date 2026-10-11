import Flex.CHC

/-! Backend protocol regressions using fake executables. No installed solver is
needed. The fixtures check exact solver arguments and complete stdin, including
the shared grouped-binder serialization. Run from the repository root with Lake.
Executable Python fixtures are POSIX-only; portable response tests also live in
`Runner.lean`. -/
namespace CHCBackendsDemo

open Lean Meta Qq Flex.CHC

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private inductive Expected where
  | sat | empty | unsat | unknown | error

private def expectOutcome (expected : Expected) (result : SolverResult) : IO Unit := do
  match expected, result.outcome with
  | .sat, .sat definitions =>
    check (definitions.size == 1 && definitions[0]!.tokens[2]? == some "k_0")
      "backend lost the returned predicate definition"
  | .empty, .sat definitions => check definitions.isEmpty "empty model gained definitions"
  | .unsat, .unsat => pure ()
  | .unknown, .unknown diagnostics =>
    check (diagnostics.size == 1) "backend discarded unknown diagnostics"
  | .error, .error message => check (!message.isEmpty) "backend returned an empty error"
  | _, _ => throw (IO.userError s!"unexpected backend outcome; stdout:\n{result.process.stdout}\nstderr:\n{result.process.stderr}")

private abbrev Invoke := String → Nat → IO SolverResult

private def checkAdapter (directory : System.FilePath) (backend label : String)
    (invoke : Invoke) : IO Unit := do
  let executable := (directory / s!"{backend} fixture").toString
  let cases : List (String × Expected × String) := [
    ("sat", .sat, "sat\n((define-fun k_0 ((b Bool) (x Int)) Bool (>= x 0)))\n"),
    ("empty", .empty, "sat\n()\n"),
    ("unsat", .unsat, "unsat\n"),
    ("unknown", .unknown, "unknown\n(:reason-unknown \"fixture incomplete\")\n"),
    ("solver-error", .error, "(error \"fixture rejected input\")\nsat\n()\n"),
    ("malformed", .error, "sat\n((define-fun k_0 () Bool true)\n"),
    ("missing-model", .error, "sat\n"),
    ("exit-error", .error, "sat\n()\n")]
  for (mode, expected, stdout) in cases do
    IO.FS.writeFile (directory / "mode") mode
    let result ← invoke executable 10000
    check (result.process.completion == .exited (if mode == "exit-error" then 7 else 0))
      s!"{label}/{mode}: wrong completion: {repr result.process.completion}; {result.process.stderr}"
    check (result.process.stdout == stdout &&
      result.process.stderr == s!"fixture backend={backend} mode={mode}\n")
      s!"{label}/{mode}: original diagnostics were lost"
    expectOutcome expected result

  let missing ← invoke (directory / "nonexistent-solver").toString 10000
  expectOutcome .error missing
  check (missing.process.completion != .exited 0) s!"{label}: missing solver exited successfully"

  let invalid ← invoke executable 0
  expectOutcome .error invalid
  check (invalid.process.completion matches .ioError _) s!"{label}: zero timeout was accepted"
  check (invalid.process.stdout.isEmpty && invalid.process.stderr.isEmpty)
    s!"{label}: solver ran despite an invalid timeout"

  IO.FS.writeFile (directory / "mode") "timeout"
  let timedOut ← invoke executable 1000
  check (timedOut.outcome matches .timedOut) s!"{label}: timeout was not propagated"
  check (timedOut.process.completion == .timedOut && timedOut.process.elapsedMs < 5000)
    s!"{label}: timeout did not bound the solver invocation"
  check (timedOut.process.stdout == "sat\n" &&
    timedOut.process.stderr == s!"fixture backend={backend} mode=timeout\n")
    s!"{label}: timeout discarded the partial transcript"

  IO.FS.writeFile (directory / "mode") "sat"
  expectOutcome .sat (← invoke executable 10000)

private def backendTests (problem : ExportedProblem) : IO Unit := do
  if System.Platform.isWindows then return
  IO.FS.withTempDir fun directory => do
    let fixture ← IO.FS.readFile "tests/fixtures/chc_backend.py"
    IO.FS.writeFile (directory / "expected.smt2") problem.toSMTLib
    for backend in ["spacer", "eldarica"] do
      let path := directory / s!"{backend} fixture"
      IO.FS.writeFile path fixture
      let chmod ← IO.Process.output { cmd := "chmod", args := #["+x", path.toString] }
      check (chmod.exitCode == 0) s!"could not prepare executable fixture: {chmod.stderr}"
    checkAdapter directory "spacer" "shared Spacer" fun executable timeoutMs =>
      Flex.CHC.run problem { backend := .spacer, executable := some executable, timeoutMs }
    checkAdapter directory "eldarica" "shared Eldarica" fun executable timeoutMs =>
      Flex.CHC.run problem { backend := .eldarica, executable := some executable, timeoutMs }
    checkAdapter directory "spacer" "direct Spacer" fun executable timeoutMs =>
      Spacer.run problem { executable, timeoutMs }
    checkAdapter directory "eldarica" "direct Eldarica" fun executable timeoutMs =>
      Eldarica.run problem { executable, timeoutMs }

run_elab do
  let goal ← mkFreshExprMVar q(∃ k : Bool → Int → Prop,
    (∀ b : Bool, k b 0) ∧
    (∀ b x, k b x → k (Bool.not b) (x + 1)) ∧
    (∀ b x, k b x → x ≥ 0))
  let (_, kvars, bodyGoal) ← peelExistentialsAndIntro goal.mvarId!
  let problem ← exportConstraints kvars (← bodyGoal.getType)
  backendTests problem
  unless !(← bodyGoal.isAssigned) do throwError "backend assigned the constraint goal"
  for kvar in kvars do
    if ← kvar.mvarId.isAssigned then throwError "backend assigned an existential witness"

end CHCBackendsDemo
