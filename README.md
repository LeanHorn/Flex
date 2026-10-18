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

Flex depends on `aesop`, `lean-auto`, and `lean-smt`. The update command skips
unused Mathlib caches from lean-smt's transitive dependency. lean-smt downloads
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
| `fix (scrape := standard)` | Also premises, Boolean observations, and relevant definitions discovered automatically. |
| `fix (scrape := deep)` | Also explores helper definitions and generalizes numeric templates, within search limits. |

Scraping is off by default. Add `(defs := [fib])` to select definitions explicitly.
Use `set_option flex.reportQualifiers true` to inspect scraped candidates in the Infoview.

Optional SMT backends can be selected separately for synthesis and proofs:

```lean4
fix (synth := flex_auto [*]) (proof := flex_smt [*])
```

These options try the selected backend before Lean automation. `flex_auto` uses
a trusted SMT axiom; `flex_smt` reconstructs Lean proofs. Synthesis proof terms
are discarded; only proof-phase evidence enters the final certificate.

See [Demo/Basic.lean](Demo/Basic.lean) for elimination examples and
[Demo/Fix.lean](Demo/Fix.lean) for invariants, scraping, and SMT oracles.
