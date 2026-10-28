# Flex

A Lean 4 library for solving Constrained Horn Clauses (CHCs).

## Using as a Dependency

Use Lean **v4.34.0** via `elan`. Add to your `lakefile.toml`:

```toml
[[require]]
name = "Flex"
git = "https://github.com/LeanHorn/Flex"
rev = "main"
```

Fetch and build:

```bash
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
```

Flex depends on `aesop`, `lean-auto`, `lean-smt`, and `SMTLib-to-Lean`.
The update command skips automatic Mathlib cache downloads. lean-smt downloads
cvc5 automatically; `flex_auto` requires `z3` on `PATH`. For Linux native
dependencies and linker setup, see the [CI workflow](.github/workflows/lean_action_ci.yml).

## Usage

`zap` eliminates acyclic predicates. `fix` synthesizes invariants by predicate
abstraction and leaves any unproved residual obligations as Lean goals.

```lean4
import Flex

example : ∃ k : Int → Prop,
    k 5
    ∧ (∀ i, k i → 1 ≤ i → k (i - 1))
    ∧ (∀ i, k i → 0 ≤ i) := by
  fix
```

By default, `fix` uses a [standard qualifier bank](Flex/PA/Qualifier.lean) for
`Int`, `Nat`, and `Bool`, together with definitions tagged `@[qualif]`.

## Scraping and SMT Oracles

Scraping adds qualifier candidates from the goal and definitions:

| Option | Candidates collected |
| --- | --- |
| `fix (scrape := basic)` | Clause conclusions and explicitly selected definitions. |
| `fix (scrape := standard)` | Also premises, bounded guarded arithmetic qualifiers, Boolean observations, and relevant definitions. |
| `fix (scrape := deep)` | Also explores helper definitions and generalizes numeric templates, within search limits. |

Scraping is off by default. Add `(defs := [fib])` to select definitions explicitly.
Use `set_option flex.reportQualifiers true` to inspect scraped candidates in the Infoview.
Disable guarded templates with `(scrapeConfig := { maxGuardedQualifiers := 0 })`.
By default, `fix` batches integer/Boolean SMT checks in short-lived Z3 processes,
rechecks affected clauses after weakening, and uses kernel-checked SMT proofs and
Lean automation for certification and residual goals. `flex_discharge` runs this
proof automation separately, leaving unsolved goals for manual proof.

Optional SMT backends can be selected separately for synthesis and proofs:

```lean4
fix (synth := flex_auto [*]) (proof := flex_smt [*])
```

These options try the selected backend before Lean automation. `flex_auto` uses
a trusted SMT axiom; `flex_smt` reconstructs Lean proofs. Synthesis proof terms
are discarded; only proof-phase evidence enters the final certificate.

See [Demo/Basic.lean](Demo/Basic.lean) for elimination examples and
[Demo/Fix.lean](Demo/Fix.lean) for invariants, scraping, and SMT oracles.

## CHC Solvers

Import `Flex.Tactic.Tactics.Spacer` or `Flex.Tactic.Tactics.Eldarica` for the
`spacer` and `eldarica` tactics. They report and instantiate solver invariants,
certify predicate heads with `grind`, and leave one structured VC for subsequent tactics.
Install `z3` and `eld` on `PATH`, or set `flex.spacer.executable` and
`flex.eldarica.executable`. See [Demo/Spacer.lean](Demo/Spacer.lean) for both.

`Flex.CHC.solveGoal` provides the underlying library API, including complete
certification, residual obligations, and rollback on failure.

## `flex`

Import `Flex.Tactic.Tactics.Flex` for `flex`, which runs `zap`, then tries `fix`,
`spacer`, and `eldarica` on the cyclic predicates. An invariant is kept only if
`flex_discharge` then proves every clause that mentions a predicate; clauses that
mention none are left as separate goals. Each step runs under an equal heartbeat
budget and is rolled back on any failure, so an unsolved goal is left as `zap`
produced it for manual proof.

```lean4
flex (backends := [fix, spacer]) (scrape := standard) (closer := grind)
  (config := { heartbeats := 100000, solverTimeout := 10 })
```

See [Demo/Flex.lean](Demo/Flex.lean) for successes and recoverable failures, and
[Demo/FlexBench](Demo/FlexBench) for FluxRS benchmarks.
