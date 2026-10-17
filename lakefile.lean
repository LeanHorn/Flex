import Lake
open Lake DSL

package «Flex» where
  version := v!"0.1.0"

-- aesop supplies goal closers; lean-auto and lean-smt supply opt-in SMT oracles.
-- `Std` ships with the Lean toolchain, so it needs no `require`.
-- Flex's imported modules are mathlib-free; this lean-smt revision declares
-- mathlib as a transitive package dependency but its `Smt` import does not use it.
-- Keep these pins aligned with lean-smt's Lean v4.34.0 dependency set.
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "355695d523e41d0554926416cba2a2b3544fbbc9"

require auto from git
  "https://github.com/leanprover-community/lean-auto.git" @ "92d628ba41801bd12c9d81f9be12fde97f0ad177"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git" @ "79ef7b3d5e06608d031d75b6d015949b90016875"

@[default_target]
lean_lib «Flex» where

lean_lib «Demo» where
  globs := #[Glob.submodules `Demo]

lean_lib «Benchmarks» where

lean_exe «flex» where
  root := `Main
