import Flex.CHC.Process.Native
import Flex.CHC.Process.Portable

namespace Flex.CHC.Process

/-- Run a fresh solver directly, closing stdin after the batch input.
POSIX uses `posix_spawnp` and a bounded native pipe pump; Windows retains Lean's
process runner. Timeout and cancellation kill the POSIX process group and reap
the child. There is no persistent launcher or shared solver state. -/
def run (config : Config) (input : String) : IO Result := do
  if System.Platform.isWindows then return ← Portable.run config input
  let started ← IO.monoMsNow
  if config.timeoutMs == 0 || config.timeoutMs >= UInt64.size then
    return { completion := .ioError "timeoutMs must be positive and fit in UInt64" }
  let raw ← try
    Native.run config.executable config.args (config.cwd.map (·.toString) |>.getD "")
      input.toUTF8 config.timeoutMs.toUInt64
    catch error =>
      return { completion := .ioError error.toString, elapsedMs := (← IO.monoMsNow) - started }
  let stdout := String.fromUTF8? raw.stdout
  let stderr := String.fromUTF8? raw.stderr
  let completion := match raw.kind with
    | 0 => if raw.code == 0 && (stdout.isNone || stderr.isNone) then
        .ioError "solver output contains invalid UTF-8" else .exited raw.code.toUInt32
    | 1 => .timedOut
    | 2 => .spawnError raw.message
    | _ => .ioError raw.message
  return { completion, stdout := stdout.getD "", stderr := stderr.getD ""
           elapsedMs := (← IO.monoMsNow) - started }

end Flex.CHC.Process
