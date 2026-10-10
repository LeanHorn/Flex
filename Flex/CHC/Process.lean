import Lean

namespace Flex.CHC.Process

/-- Run an executable directly, without a shell. The deadline includes writing
the input and draining both output streams, followed by a short cleanup grace. -/
structure Config where
  executable : String
  args : Array String := #[]
  timeoutMs : Nat := 10000
  cwd : Option System.FilePath := none
  deriving Inhabited, Repr

inductive Completion where
  | exited (code : UInt32)
  | timedOut
  | spawnError (message : String)
  | ioError (message : String)
  deriving Inhabited, Repr, BEq

/-- Captured diagnostics are retained even when the child fails or times out. -/
structure Result where
  completion : Completion
  stdout : String := ""
  stderr : String := ""
  elapsedMs : Nat := 0
  deriving Inhabited, Repr

private abbrev Child := IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }
private abbrev Worker := Task (Except IO.Error Unit)

private structure Running where
  child : Child
  exitCode : IO.Ref (Option UInt32)
  input : Worker
  output : Worker
  error : Worker
  stdout : IO.Ref ByteArray
  stderr : IO.Ref ByteArray

/-- Keep bytes until EOF so a UTF-8 character split between reads stays intact.
The reference also preserves output if a later read fails. -/
private def drain (handle : IO.FS.Handle) (buffer : IO.Ref ByteArray) : IO Unit := do
  repeat
    let bytes ← handle.read 4096
    if bytes.isEmpty then return
    buffer.modify (· ++ bytes)

private def start (config : Config) (input : String) : IO Running := do
  let child ← IO.Process.spawn {
    cmd := config.executable, args := config.args, cwd := config.cwd
    stdin := .piped, stdout := .piped, stderr := .piped
    setsid := !System.Platform.isWindows }
  let (stdin, child) ← child.takeStdin
  let stdout ← IO.mkRef ByteArray.empty
  let stderr ← IO.mkRef ByteArray.empty
  let exitCode ← IO.mkRef none
  -- Dedicated threads prevent a blocked pipe from starving another stream.
  let output ← IO.asTask (drain child.stdout stdout) .dedicated
  let error ← IO.asTask (drain child.stderr stderr) .dedicated
  let input ← IO.asTask (do stdin.putStr input; stdin.flush) .dedicated
  return { child, exitCode, input, output, error, stdout, stderr }

/-- `tryWait` reaps a terminated child; subsequent OS waits would fail. -/
private def pollExit (running : Running) : IO (Option UInt32) := do
  if let some code ← running.exitCode.get then return some code
  let result ← running.child.tryWait
  running.exitCode.set result
  return result

private def workers (running : Running) : List Worker :=
  [running.input, running.output, running.error]

private def finished (running : Running) : IO Bool := do
  return (← (workers running).allM fun task => return ← IO.hasFinished task) &&
    (← pollExit running).isSome

private def workerError (running : Running) : IO (Option String) := do
  for (label, task) in [("stdin", running.input), ("stdout", running.output),
      ("stderr", running.error)] do
    if ← IO.hasFinished task then
      if let .error error := ← IO.wait task then
        return some s!"{label}: {error}"
  return none

private def monitor (running : Running) (deadline : Nat) : IO Completion := do
  repeat
    if ← finished running then
      let some code ← running.exitCode.get
        | return .ioError "finished process has no recorded exit status"
      if code != 0 then return .exited code
      if let some error ← workerError running then return .ioError error
      return .exited code
    if let some error ← workerError running then return .ioError error
    if (← IO.monoMsNow) >= deadline then return .timedOut
    IO.sleep 5
  return .ioError "process monitor stopped unexpectedly"

/-- Kill the whole POSIX process group, including children holding output pipes.
Lean's `Child.kill` sends SIGTERM; `/bin/kill` supplies SIGKILL after the grace
period. This is an OS utility, invoked with argv and never through a shell. -/
private def stop (running : Running) : IO Unit := do
  unless ← finished running do
    try running.child.kill catch error =>
      unless (← pollExit running).isSome do throw error
    let graceEnd := (← IO.monoMsNow) + 200
    repeat
      if ← finished running then break
      if (← IO.monoMsNow) >= graceEnd then break
      IO.sleep 5
    unless ← finished running do
      if System.Platform.isWindows then
        throw <| IO.userError "child did not terminate after process cancellation"
      let killed ← IO.Process.output {
        cmd := "/bin/kill"
        args := #["-KILL", "--", s!"-{running.child.pid}"] }
      if killed.exitCode != 0 && !(← finished running) then
        throw <| IO.userError s!"could not kill process group: {killed.stderr.trimAscii}"
  if (← running.exitCode.get).isNone then
    running.exitCode.set (some (← running.child.wait))
  for task in workers running do discard <| IO.wait task

private def collect (running : Running) (completion : Completion) (started : Nat) : IO Result := do
  let stdout := String.fromUTF8? (← running.stdout.get)
  let stderr := String.fromUTF8? (← running.stderr.get)
  let completion := match completion with
    | .exited 0 => if stdout.isNone || stderr.isNone then
        .ioError "solver output contains invalid UTF-8" else completion
    | _ => completion
  return {
    completion
    stdout := stdout.getD ""
    stderr := stderr.getD ""
    elapsedMs := (← IO.monoMsNow) - started }

/-- Run a batch protocol and close stdin once all input has been written.
Failures are values, with captured diagnostics. On POSIX the child runs in its
own process group, which is terminated and reaped on timeout or I/O failure.
A positive timeout is required. -/
def run (config : Config) (input : String) : IO Result := do
  let started ← IO.monoMsNow
  if config.timeoutMs == 0 then
    return { completion := .ioError "timeoutMs must be positive" }
  let running ← try start config input catch error =>
    return { completion := .spawnError error.toString, elapsedMs := (← IO.monoMsNow) - started }
  let mut completion ← try monitor running (started + config.timeoutMs) catch error =>
    pure <| .ioError error.toString
  try stop running catch error =>
    completion := .ioError s!"process cleanup failed: {error}"
  collect running completion started

end Flex.CHC.Process
