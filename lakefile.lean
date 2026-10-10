import Lake
open Lake DSL

package «Flex» where
  version := v!"0.1.0"

-- aesop supplies goal closers; lean-auto and lean-smt supply opt-in SMT oracles.
-- `Std` ships with the Lean toolchain, so it needs no `require`.
-- Flex's imported modules are mathlib-free; this lean-smt revision declares
-- mathlib as a transitive package dependency but its `Smt` import does not use it.
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "3426969888a264d3f69b6f30ab50aa11f28eb38d"

-- v4.29.0-hammer, verified against Flex's v4.29.0-rc8 toolchain.
require auto from git
  "https://github.com/leanprover-community/lean-auto" @ "d5600411d5e766a7cb1e47e3b3393ed64c42efc2"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git" @ "7d1d8239e78daa5197f9a71948776c4627049f5f"

@[default_target]
lean_lib «Flex» where

lean_lib «Demo» where

lean_lib «Benchmarks» where

lean_exe «flex» where
  root := `Main
