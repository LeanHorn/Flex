# Flex

A Lean 4 library for a constraint-solving framework for Constrained Horn Clauses (CHCs).

---

## Using as a Dependency

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/quickstart.html) installed via `elan`

### Step 1 — Add to your `lakefile.toml`

```toml
[[require]]
name = "Flex"
git = "https://github.com/jam-khan/Flex"
rev = "main"
```

### Step 2 — Fetch the dependency

```bash
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
```

This clones the repo into `.lake/packages/Flex/` using your local Git credentials.

### Step 3 — Build

```bash
lake build
```

> **Note:** Flex depends on `aesop`, pinned `lean-auto`, and pinned `lean-smt`.
> Its modules do not import Mathlib, but the pinned lean-smt package declares
> Mathlib as a transitive dependency. `flex_auto` needs `z3` on `PATH`;
> lean-smt downloads its own cvc5 native library during the first build.
> `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update` avoids fetching
> unused Mathlib build caches. Lean and the pinned dependencies use `v4.34.0`,
> the newest common release supported by the pinned lean-smt revision.

---

## Importing

A single import gives you the core API, Lean tactics, and lean-auto/lean-smt wrappers:

```lean4
import Flex
```

This includes all core types, tactics, elaboration, and the solver.

Plain `fix` uses a fixed [standard qualifier bank](Flex/PA/Qualifier.lean),
without scraping or per-example declarations:

| Type | Templates |
| --- | --- |
| `Int` | `x = 0`, `0 < x`, `0 ≤ x`, `x < 0`, `x ≤ 0`; `x = y`, `x > y`, `x ≥ y`, `x < y`, `x ≤ y`, `x ≤ y - 1` |
| `Nat` | `x = 0`, `0 < x`; `x = y`, `x < y`, `x ≤ y` |
| `Bool` | `x = true`, `x = false`, `x = y` |

Templates instantiate over distinct κ parameters of matching types. Registered
`@[qualif]` templates and scraped templates take priority over the standard bank;
duplicate instantiated predicates are removed. Use
`set_option flex.standardQualifiers false` to disable only the standard bank.
The bank contains no function-specific templates or nonzero literal bounds.
For `m` integer parameters it proposes at most `5m + 6m(m - 1)` instances before
deduplication; slot assignments are injective, so repeated slots are excluded.

Scraping is opt-in:

| Option | Candidates collected |
| --- | --- |
| `(scrape := basic)` | Goal heads and explicitly selected definitions. |
| `(scrape := standard)` | Also premises, Boolean observations, and equations of relevant definitions found in the goal. |
| `(scrape := deep)` | Also bounded helper exploration and numeric template generalization. |

`(defs := [fib])` explicitly selects definitions, including those excluded from
automatic discovery. With no `scrape` option, `defs` scrapes only those definitions.
`deep` retains exact candidates in its pool and proposes non-strict bounds from
strict comparisons and parameterized bounds from numeric literals. All candidates
still go through PA and certificate construction; scraping assumes no new facts.

Limits can be overridden per invocation:

```lean4
fix (scrape := deep)
  (scrapeConfig := { maxQualifiers := 256, maxCandidatesPerKappa := 1024 })
```

Defaults are 3 data parameters per template, 128 selected templates, 20,000
traversal visits, traversal depth 64, 16 definition specializations, and helper
depth 2 in `deep` (`standard` inspects only directly discovered definitions).
With scraping enabled, per κ at most 8,192 compatible slot assignments are processed and 2,048 distinct
candidates retained. Truncation produces a warning. These limits bound search
components, not total solver time; larger modes need not solve more goals under
fixed budgets. Abstract type parameters and dependent qualifier slots remain
unsupported; concrete applications such as `List.length` on `List Int` are supported.

Enable `set_option flex.reportQualifiers true` to show candidates and their
origins in the Infoview. `set_option trace.flex.scrape true` gives discovery details.
Reporting is off by default and does not affect scraping.

[Demo/Fix.lean](Demo/Fix.lean) progresses from unary and relational loops to
mixed types, mutually recursive predicates, literal-bound scraping, generalized
sum bounds, and Fibonacci. The first four use plain `fix`. The mixed acyclic/cyclic
examples use `zap` followed by `fix`; the last three add scraping.
Oracle variants reuse the unary countdown.

### Example

```lean4
import Flex

def ex1 : Prop :=
  ∃ κ : Int → Prop,
    ∀ x : Int,
      0 ≤ x →
      (∀ ν : Int, ν = x - 1 → κ ν)
    ∧ (∀ y : Int, κ y →
        ∀ ν : Int, ν = y + 1 → 0 ≤ ν)
```

See the [`Demo/`](./Demo/Basic.lean) folder for more worked examples.
