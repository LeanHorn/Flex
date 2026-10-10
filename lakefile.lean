import Lake
open Lake DSL

package «Flex» where
  version := v!"0.1.0"

-- Share SMTLib-to-Lean's dependency revisions under Lean v4.33.1.
-- Explicit pins keep the proof oracles and future model importer on the same
-- lean-smt/cvc5 API. SMTLib-to-Lean is available without importing it in Flex.
require aesop from git
  "https://github.com/leanprover-community/aesop" @ "3448c0bcc5ce01b2d1546e483ec3620e32df3d0e"

require auto from git
  "https://github.com/leanprover-community/lean-auto.git" @ "eb9c694863439fb55800228bc4c7babe42b089bf"

require smt from git
  "https://github.com/ufmg-smite/lean-smt.git" @ "5bdc51674065a074ece67b04e10024e9f426ec1f"

require cvc5 from git
  "https://github.com/abdoo8080/lean-cvc5.git" @ "7e3365990661b697ccb30e92d6912f4cc6589322"

require smt2lean from git
  "https://github.com/LeanHorn/SMTLib-to-Lean.git" @ "5b90810d81b3781495c40de671c37c75727931f6"

@[default_target]
lean_lib «Flex» where

lean_lib «Demo» where

lean_lib «Benchmarks» where

lean_exe «flex» where
  root := `Main
