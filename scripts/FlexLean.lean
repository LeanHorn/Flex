import Flex.Tactic.Tactics.Flex

/-!
`flex-lean [--setup SETUP.json] FILE.lean` elaborates one file like `lean`, but with the
Flex tactics linked into this executable as native code. The interpreter runs imported
declarations through these compiled symbols (`supportInterpreter`), so Fix/PA weakening and
Zap run natively. Libraries from this workspace are linked statically, so the setup file's
dynlibs and workspace plugins are not loaded again; toolchain plugins still load.

The executable links Flex's import graph module by module. It contains no Mathlib:
`Flex.CHC.ModelImport` (SMTLib-to-Lean's model translator) is imported by the elaborated
file instead and runs interpreted.
-/

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  if args == ["--version"] then
    IO.println s!"Lean (version {Lean.versionString}), flex-lean native Flex runner"
    return 0
  let (setupPath?, file) ← match args with
    | ["--setup", setup, file] => pure (some setup, file)
    | [file] => pure (none, file)
    | _ => throw <| IO.userError "usage: flex-lean [--setup SETUP.json] FILE.lean"
  let sysroot ← findSysroot
  initSearchPath sysroot
  enableInitializersExecution
  let setup? ← setupPath?.mapM fun path => do
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
    let setup : ModuleSetup ← IO.ofExcept <| fromJson? json
    let toolchain := sysroot.toString
    return { setup with
      dynlibs := #[]
      plugins := setup.plugins.filter (·.path.toString.startsWith toolchain) }
  let input ← IO.FS.readFile file
  let env? ← Elab.runFrontend input {} file `_unknown (setup? := setup?)
  return if env?.isSome then 0 else 1
