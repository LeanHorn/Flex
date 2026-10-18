import Lake
open Lake DSL

package «Flex» where
  version := v!"0.1.0"

-- aesop supplies goal closers; lean-auto and lean-smt supply opt-in SMT oracles.
-- `Std` ships with the Lean toolchain, so it needs no `require`.
-- Flex's core imports are mathlib-free; this lean-smt revision declares
-- mathlib as a transitive package dependency but its `Smt` import does not use it.
-- Keep these pins aligned with lean-smt's Lean v4.34.0 dependency set.
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "355695d523e41d0554926416cba2a2b3544fbbc9"

require auto from git
  "https://github.com/leanprover-community/lean-auto.git" @ "92d628ba41801bd12c9d81f9be12fde97f0ad177"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git" @ "79ef7b3d5e06608d031d75b6d015949b90016875"

-- Keep the CHC importer on main's shared solver dependencies.
require cvc5 from git
  "https://github.com/abdoo8080/lean-cvc5.git" @ "41e47796d4d15712e6064b064ca5d251a1283955"

require smt2lean from git
  "https://github.com/LeanHorn/SMTLib-to-Lean.git" @ "89667053aa420284b6794b6d6caabd551c1f7c79"

@[default_target]
lean_lib «Flex» where

input_file chcProcess.cpp where
  path := "native" / "chc_process.cpp"
  text := true

target chcProcess.o pkg : System.FilePath := do
  let source ← chcProcess.cpp.fetch
  -- As with lean-cvc5, use the host C++ headers and Lean's libc++ ABI.
  -- Lean's bundled C sysroot does not include the C++ standard library headers.
  buildO (pkg.buildDir / "native" / "chc_process.o") source
    #["-I", (← getLeanIncludeDir).toString]
    #["-std=c++17", "-stdlib=libc++", "-O2", "-fPIC", "-Wall", "-Wextra"]
    (compiler := if System.Platform.isWindows then "cc" else "clang")

-- Declared after Flex so Lake selects this narrower library for the FFI module.
-- Precompilation makes the native implementation available to tactics and #eval.
lean_lib FlexCHCNative where
  roots := #[`Flex.CHC.Process.Native]
  precompileModules := true
  moreLinkObjs := #[chcProcess.o]

lean_lib «Demo» where
  globs := #[Glob.submodules `Demo]

lean_lib «Benchmarks» where

lean_exe «flex» where
  root := `Main
