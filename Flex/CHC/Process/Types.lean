import Lean

namespace Flex.CHC.Process

/-- Run an executable directly, without a shell. The deadline covers startup,
writing input, and draining output; child cleanup finishes before returning. -/
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

end Flex.CHC.Process
