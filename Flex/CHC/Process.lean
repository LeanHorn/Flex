import Lean
import Flex.CHC.Native

namespace Flex.CHC.Process

/-- Invoke an executable directly. The timeout covers startup, input, and output. -/
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

private def decodeResult (completion : Completion) (stdout stderr : ByteArray)
    (elapsedMs : Nat) : Result :=
  let stdout := String.fromUTF8? stdout
  let stderr := String.fromUTF8? stderr
  let completion := match completion with
    | .exited 0 => if stdout.isNone || stderr.isNone then
        .ioError "solver output contains invalid UTF-8" else completion
    | _ => completion
  { completion, stdout := stdout.getD "", stderr := stderr.getD "", elapsedMs }

namespace Windows

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
    stdin := .piped, stdout := .piped, stderr := .piped }
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
  let exited := (← pollExit running).isSome
  return exited && (← (workers running).allM fun task => return ← IO.hasFinished task)

private def workerError (running : Running) : IO (Option String) := do
  for (label, task) in [("stdin", running.input), ("stdout", running.output),
      ("stderr", running.error)] do
    if ← IO.hasFinished task then
      if let .error error := ← IO.wait task then
        return some s!"{label}: {error}"
  return none

private def monitor (running : Running) (deadline : Nat) : IO Completion := do
  repeat
    if ← IO.checkCanceled then return .ioError "solver request canceled"
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
      throw <| IO.userError "child did not terminate after process cancellation"
  if (← running.exitCode.get).isNone then
    running.exitCode.set (some (← running.child.wait))
  for task in workers running do discard <| IO.wait task

/-- Cleanup runs after completion, I/O errors, timeout, and cancellation. -/
private def run (config : Config) (input : String) : IO Result := do
  let started ← IO.monoMsNow
  if config.timeoutMs == 0 then
    return { completion := .ioError "timeoutMs must be positive" }
  let running ← try start config input catch error =>
    return { completion := .spawnError error.toString, elapsedMs := (← IO.monoMsNow) - started }
  let mut completion ← try monitor running (started + config.timeoutMs) catch error =>
    pure <| .ioError error.toString
  try stop running catch error =>
    completion := .ioError s!"process cleanup failed: {error}"
  return decodeResult completion (← running.stdout.get) (← running.stderr.get)
    ((← IO.monoMsNow) - started)

end Windows

/-- Run a fresh solver and close stdin after the batch input. POSIX uses a bounded
native pipe pump; timeout and cancellation kill its process group and reap it.
Windows uses Lean's process runner and terminates the direct child. -/
def run (config : Config) (input : String) : IO Result := do
  if System.Platform.isWindows then return ← Windows.run config input
  let started ← IO.monoMsNow
  if config.timeoutMs == 0 || config.timeoutMs >= UInt64.size then
    return { completion := .ioError "timeoutMs must be positive and fit in UInt64" }
  let raw ← try
    Native.run config.executable config.args (config.cwd.map (·.toString) |>.getD "")
      input.toUTF8 config.timeoutMs.toUInt64
    catch error =>
      return { completion := .ioError error.toString, elapsedMs := (← IO.monoMsNow) - started }
  let completion := match raw.kind with
    | 0 => .exited raw.code.toUInt32
    | 1 => .timedOut
    | 2 => .spawnError raw.message
    | _ => .ioError raw.message
  return decodeResult completion raw.stdout raw.stderr ((← IO.monoMsNow) - started)

end Flex.CHC.Process
