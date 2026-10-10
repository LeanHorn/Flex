import Flex.CHC.Solver
import Lean

/-! Solver-response and subprocess regressions. These require Python 3, but no
Z3 or Eldarica installation. Run from the repository root with Lake. -/
namespace CHCRunnerDemo

open Flex.CHC

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def decode (stdout : String) (completion : Process.Completion := .exited 0)
    : SolverResult :=
  SolverResult.ofProcess { completion, stdout, stderr := "", elapsedMs := 0 }

private def expectError (response : String) : IO Unit :=
  match (decode response).outcome with
  | .error _ => pure ()
  | _ => throw (IO.userError s!"accepted invalid solver response: {response}")

private def responseTests : IO Unit := do
  let model := "sat\n((define-fun k_0 ((x Int)) Bool (>= x 0)))\n"
  let parsed := decode model
  check (parsed.process.stdout == model) "decoder lost original stdout"
  match parsed.outcome with
  | .sat definitions =>
    check (definitions.size == 1) "wrong model definition count"
    check (definitions[0]!.tokens[2]? == some "k_0") "lost model symbol"
  | _ => throw (IO.userError "sat with a model was rejected")

  for response in ["sat\n()\n", "success\nsat\n(model)\n"] do
    match (decode response).outcome with
    | .sat definitions => check definitions.isEmpty "empty model gained definitions"
    | _ => throw (IO.userError "explicitly empty model was rejected")
  match (decode "unsat\n").outcome with
  | .unsat => pure ()
  | _ => throw (IO.userError "unsat status was lost")
  for response in ["unknown\n", "unknown\n(:reason-unknown \"incomplete\")\n"] do
    match (decode response).outcome with
    | .unknown diagnostics =>
      check (diagnostics.size == if response.contains "incomplete" then 1 else 0)
        "unknown diagnostics were lost"
    | _ => throw (IO.userError "unknown status was lost")

  for response in ["", "sat\n", "((define-fun k () Bool true))\n",
      "sat\n()\ntrailing", "sat\nsat\n()\n", "sat\n((define-fun k () Bool true)",
      "unsat\n()\n", "unknown\n()\n", "(error \"bad input\")\n",
      "sat\n(error \"model unavailable\")\n",
      "sat\n((define-fun k () Bool true) (define-fun k () Bool false))\n"] do
    expectError response
  match (decode model (.exited 7)).outcome with
  | .error _ => pure ()
  | _ => throw (IO.userError "nonzero exit was accepted despite valid-looking stdout")
  match (decode model .timedOut).outcome with
  | .timedOut => pure ()
  | _ => throw (IO.userError "partial sat output overrode a timeout")
  for completion in [Process.Completion.spawnError "missing", .ioError "broken pipe"] do
    match (decode model completion).outcome with
    | .error _ => pure ()
    | _ => throw (IO.userError "process failure was accepted as sat")

private def fixture (mode : String) (input : String := "") (timeoutMs : Nat := 10000)
    : IO Process.Result :=
  Process.run {
    executable := "python3"
    args := #["tests/fixtures/chc_solver.py", mode]
    timeoutMs } input

private def expectExit (result : Process.Result) (code : UInt32) : IO Unit :=
  match result.completion with
  | .exited actual => check (actual == code) s!"wrong process exit code: {actual}"
  | completion => throw (IO.userError s!"process did not exit normally: {repr completion}; {result.stderr}")

private def checkTimeout (mode input : String) : IO Unit := do
  let result ← fixture mode input 1000
  match result.completion with
  | .timedOut => pure ()
  | _ => throw (IO.userError s!"{mode}: expected timeout")
  check (result.elapsedMs < 5000) s!"{mode}: timeout cleanup exceeded five seconds"
  check (result.stderr == "waiting for cancellation\n") s!"{mode}: timeout lost stderr"
  let some pid := result.stdout.trimAscii.toString.toNat?
    | throw (IO.userError s!"{mode}: child did not report its PID before timing out")
  let probe ← IO.Process.output { cmd := "/bin/kill", args := #["-0", toString pid] }
  check (probe.exitCode != 0) s!"{mode}: timed-out child is still alive or unreaped"

private def processTests : IO Unit := do
  let echoed ← fixture "echo" "test input\n"
  expectExit echoed 0
  check (echoed.stdout == "test input\n" && echoed.stderr == "fixture stderr\n")
    "process output capture changed data"

  let unicode ← fixture "utf8"
  expectExit unicode 0
  check (unicode.stdout == String.ofList (List.replicate 4095 'a') ++ "€🙂")
    "multibyte UTF-8 was corrupted at a pipe read boundary"

  let fromDirectory ← Process.run {
    executable := "python3", args := #["chc_solver.py", "echo"]
    cwd := some "tests/fixtures" } "configured cwd"
  expectExit fromDirectory 0
  check (fromDirectory.stdout == "configured cwd") "child working directory was ignored"

  let largeInput := String.ofList (List.replicate 1048576 'i')
  let drained ← fixture "drain" largeInput
  expectExit drained 0
  let expectedOut := String.ofList (List.replicate 131072 'o') ++ "\ninput-bytes=1048576\n"
  let expectedErr := String.ofList (List.replicate 131072 'e')
  check (drained.stdout == expectedOut && drained.stderr == expectedErr)
    "concurrent stdin/stdout/stderr transfer lost data"

  let failed ← fixture "exit-error"
  expectExit failed 7
  check (failed.stdout == "sat\n()\n" && failed.stderr == "deliberate process failure\n")
    "nonzero exit discarded diagnostics"
  match (SolverResult.ofProcess failed).outcome with
  | .error _ => pure ()
  | _ => throw (IO.userError "failed child produced an accepted solver result")

  let missing ← Process.run { executable := "./tests/fixtures/nonexistent-chc-solver" } ""
  match missing.completion with
  | .spawnError _ => pure ()
  | .exited code => check (code != 0) "missing executable exited successfully"
  | _ => throw (IO.userError "missing executable did not report a launch failure")
  match (SolverResult.ofProcess missing).outcome with
  | .error _ => pure ()
  | _ => throw (IO.userError "missing executable was accepted as a solver result")
  let invalidDeadline ← Process.run { executable := "python3", timeoutMs := 0 } ""
  match invalidDeadline.completion with
  | .ioError _ => pure ()
  | _ => throw (IO.userError "zero timeout was accepted")
  checkTimeout "timeout" ""
  checkTimeout "blocked-stdin" largeInput
  let recovered ← fixture "echo" "after timeout"
  expectExit recovered 0
  check (recovered.stdout == "after timeout") "process runner did not recover after timeout"

#eval responseTests
#eval processTests

end CHCRunnerDemo
