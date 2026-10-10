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
lake update
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
> `MATHLIB_NO_CACHE_ON_UPDATE=1 lake --keep-toolchain update` avoids fetching
> unused Mathlib build caches. The Lean toolchain remains `v4.29.0-rc8`.

---

## Importing

A single import gives you the core API, Lean tactics, and lean-auto wrapper:

```lean4
import Flex
```

This includes all core types, tactics, elaboration, and the solver.
For lean-smt, additionally import `Flex.Tactic.Oracles.Smt`.

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

## Predicate abstraction: scraping and additional oracles

`fix (oracle := ...)` accepts a per-call fallback tactic. It tries the existing PA oracle
(`omega`, `grind`, then `constructor <;> grind`) first, and calls the fallback
when that oracle cannot close the query. The fallback participates in candidate
implication checks, contradictory-premise checks, certificate construction, and
closing the final goals. Failures and unfinished goals count as unknown/failure,
and failed attempts restore their state.

Use `synth` and `proof` to choose **independent, external-first** oracles:

```lean
import Flex
import Flex.Tactic.Oracles.Smt

set_option auto.smt.timeout 2 in
example : MyConstraint := by
  fix (synth := flex_auto [*]) (proof := flex_smt [*])
```

`synth` controls candidate implication and contradictory-premise checks during
Houdini weakening. `proof` controls certificate leaves and the final residual
goals. Each tries the supplied tactic first, then the existing Lean oracle on
failure, incomplete proof, or unknown. They override `oracle` for their own
phase; unspecified phases retain the legacy oracle or Lean default. Thus
`fix (synth := flex_auto)` uses trusted SMT only for synthesis and rebuilds the
final proof with Lean. The synthesis proof terms are discarded. A proof oracle
still has to establish the selected invariant; a synthesis success alone does
not close the theorem.

`flex_smt` uses lean-smt/cvc5 proof reconstruction with a two-second solver
timeout. Use `smt (timeout := some 1) [*]` directly for other settings. The
structured constraint certificate is still built by Flex; lean-smt discharges
its leaf obligations. Run files importing this native backend with
`lake lean MyFile.lean` or `lake build`, so Lake loads cvc5's native library.
Plain `lake env lean MyFile.lean` does not load the necessary plugin.

lean-auto is included at revision
[`d5600411`](https://github.com/leanprover-community/lean-auto/tree/d5600411d5e766a7cb1e47e3b3393ed64c42efc2)
(`v4.29.0-hammer`), tested on Flex's existing `v4.29.0-rc8` toolchain with Z3
4.15.4. After `import Flex`, use:

```lean
set_option auto.smt.timeout 2 in
example : MyConstraint := by
  fix (oracle := flex_auto)
```

`flex_auto` enables lean-auto's trusted SMT mode for that invocation. It uses
Z3 by default; solver selection and timeout remain configurable through
`auto.smt.solver.name` and `auto.smt.timeout`. All of auto's hints are accepted,
for example `flex_auto [*, my_lemma] d[fib]`. This adds SMT to PA without requiring
proof reconstruction. When used for proofs (including the legacy `oracle`
option), successful calls retain lean-auto's `autoSMTSorry` axiom. With a separate
reconstructing `proof` route, trusted synthesis does not add this axiom to the
resulting theorem; [Demo/OracleRouting.lean](./Demo/OracleRouting.lean) checks this.

```lean
-- After `import Flex.Tactic.Oracles.Smt`:
fix (oracle := smt (timeout := some 2) [*])

-- Skip SMT proof reconstruction when only the solver's answer is wanted:
fix (oracle := smt +trust (timeout := some 2) [*]) (trust := true)

-- lean-auto is already included; configure its SMT mode or use flex_auto:
fix (oracle := auto [*]) (trust := true)

-- After adding lean-blaster and importing Blaster:
fix (oracle := blaster (timeout: 2)) (trust := true)

-- With all three packages imported, try each until it closes the query:
fix (oracle := first
  | (smt +trust (timeout := some 2) [*]; done)
  | (auto [*]; done)
  | (blaster (timeout: 2); done)) (trust := true)
```

For lean-auto's direct SMT mode, configure `auto.smt true`,
`auto.smt.trust true`, and `auto.smt.solver.name "z3"` (or another supported
solver) with `set_option`. Install the corresponding solver executable as well.
`[*]` passes the PA query's local hypotheses to the backend.

`trust := true` permits evidence containing `sorry`, as used by Blaster and
lean-smt's trusted mode. It does not turn an unfinished query into a successful
one. Backend-specific axioms (such as lean-auto's trusted SMT axiom) retain
their own trust semantics; `trust := false` is not an axiom allowlist. Trusted
results are useful for PA experiments, but are not reconstructed Lean proofs.

The upstream interfaces are documented by
[lean-smt](https://github.com/ufmg-smite/lean-smt),
[lean-auto](https://github.com/leanprover-community/lean-auto), and
[Blaster](https://github.com/input-output-hk/Lean-blaster#tactic).
lean-smt is pinned at
[`7d1d8239`](https://github.com/ufmg-smite/lean-smt/tree/7d1d8239e78daa5197f9a71948776c4627049f5f)
and its cvc5 bindings at `4ecae274`; both build on Flex's toolchain.
Blaster is not installed, so its examples above remain integration recipes.
lean-auto/Z3 has been tested on a PA constraint that needs the external
fallback, including rejection of an invalid query (see
[Demo/LeanAuto.lean](./Demo/LeanAuto.lean)). Flex currently uses Lean
`v4.29.0-rc8`; at the time of this change the upstream toolchain files
report [lean-smt v4.34.0](https://github.com/ufmg-smite/lean-smt/blob/main/lean-toolchain),
[lean-auto v4.34.1](https://github.com/leanprover-community/lean-auto/blob/master/lean-toolchain),
and [Blaster v4.24.0](https://github.com/input-output-hk/Lean-blaster/blob/main/lean-toolchain).
Flex pins older compatible lean-auto and lean-smt revisions. Do not assume
the latest branches build together.

### Scraping constraints and Lean definitions

```lean
fix (scrape := head)                    -- concrete clause conclusions
fix (scrape := both)                    -- also concrete premises
fix (scrape := both) (defs := [fib])     -- also inspect fib's equations

-- Combine scraping with the included lean-auto oracle:
fix (scrape := both) (defs := [fib]) (oracle := flex_auto [*] d[fib])

-- Prefer trusted SMT for synthesis and reconstruction for the final proof:
fix (scrape := both) (defs := [fib])
  (synth := flex_auto [*] d[fib]) (proof := flex_smt [*, fib])
```

Options appear in the order `scrape`, `defs`, `oracle`, `synth`, `proof`, `trust`, and any may be
omitted. Plain `fix` still uses the registered `@[qualif]` predicates and Lean
automation. Scraped candidates are local to this invocation and are added to
the registered qualifiers. `solve`, `fixpoint`, and plain `pa_cert` keep their
existing qualifier sources and oracle.

The implementation follows liquid-fixpoint's
[`Horn/Info.hs` scraper](https://github.com/ucsd-progsys/liquid-fixpoint/blob/78acd0e08590e506f71e4168ce92326373d5adef/src/Language/Fixpoint/Horn/Info.hs#L163):
traverse binders and conjunctions, skip κ applications, collect concrete
predicates, abstract their free variables into typed qualifier parameters,
deduplicate, and reject candidates with more than three parameters.
Liquid-fixpoint rotates parameter order because its first parameter has a
distinguished role. Flex's existing instantiator already tries all compatible
ordered slot assignments, so those rotations would duplicate work.

Definition scraping is an additional Flex feature. It uses
`Lean.Meta.getEqnsFor?` to inspect equation lemmas without unfolding recursive
calls indefinitely. For

```lean
@[grind] def fib (n : Int) : Int :=
  if n ≤ 1 then 1 else fib (n - 1) + fib (n - 2)
  termination_by n.toNat
```

it generates candidates including `fun v i => v = fib i`,
`fun v i => v = fib (i - 1)`, `fun v i => v = fib (i - 2)`, and both polarities
of the guard `i ≤ 1`. These enter the usual instantiation and Houdini weakening
pipeline; they are candidate invariants, not assumed facts. The oracle still
needs the function's equations: `@[grind]` supplies them to `grind`, while
external tactics may need explicit hints (`[*, fib]` for current lean-smt,
`d[fib]` for lean-auto).

The initial scraper supports independent monomorphic parameters, up to three
parameters per candidate and 128 scraped templates per call. It skips
dependent/proof parameters and unresolved metavariables, visits only the
explicitly selected definitions, and does not implement PLE or synthesize
arbitrary arithmetic templates. Its bounds are fields of `PAScrapeConfig` for
programmatic callers. Enable `trace.flex.scrape` to inspect candidates or
`trace.flex.oracle` to inspect oracle failures and fallback use.

See [Demo/OracleScrape.lean](./Demo/OracleScrape.lean) for a Fibonacci loop solved
without manual Fibonacci qualifiers, a proof requiring a custom fallback,
and regression checks for scraping and oracle isolation.
[Demo/FibAuto.lean](./Demo/FibAuto.lean) combines definition scraping with actual
lean-auto/Z3 queries for recursive Fibonacci, with the defining equations
supplied through `d[fib]`.

### Comparing oracle performance

```bash
lake build Flex Flex.Tactic.Oracles.Smt
python3 scripts/benchmark_oracles.py --repeats 3
```

The driver compares Lean-only, Lean-first with auto fallback, auto-first
synthesis, smt-first proofs, and both external-first routes. Four fixed cases
cover arithmetic loops, the existing Fibonacci loop, and Fibonacci with scraped
definition predicates. Each case/configuration has a warm-up followed by three
serial measured runs in shuffled order. Both backends have a one-second solver
timeout. The timer covers theorem elaboration, including external solver work;
imports/builds are excluded and process time is reported separately. Candidate
counts, proof axioms, phase times, exact generated sources, and raw output are
saved in [eval/oracle_results.json](./eval/oracle_results.json). Failed,
unfinished, and `sorryAx`-dependent theorems do not count as successful timings.
The flattened summary is [eval/oracle_results.csv](./eval/oracle_results.csv).

Measured on Apple M4, Lean `v4.29.0-rc8`, Z3 4.15.4, and lean-smt's bundled
cvc5 1.3.2 (2026-10-10). Median theorem-elaboration wall time in **milliseconds**:

| Case | Lean only | Lean-first auto fallback | Auto-first synthesis | SMT-first proofs | Both external-first |
|---|---:|---:|---:|---:|---:|
| Countdown | 89 | 2,326 | 6,179 | 288 | 6,329 |
| Counter loop (`loop01`) | 64 | 1,928 | 4,591 | 211 | 4,499 |
| Fibonacci, scraped definitions | 277 | 18,911 | 22,852 | 569 | 22,827 |
| Fibonacci loop (`FibFibFast`) | 1,201 | 51,973 | 80,428 | 1,966 | 81,979 |

All 60 measured executions succeeded. Each case retained the same number of
qualifiers across configurations (respectively 3/6, 2/4, 2/12, and 12/44
surviving/initial). The combined external-first configuration was **68–82×
slower**, and SMT-first proofs alone made the overall solve **1.6–3.3× slower**.
On these already Lean-solvable cases, the external solvers did not improve
coverage. These results isolate oracle ordering with fixed candidate banks;
they do not establish performance on other constraint families. Lean remains
the default, with explicit external-first options available for experimentation.

Enable `set_option flex.benchOracles true` to print `fix`'s synthesis,
certificate, and residual wall times on another constraint. These are useful
for solver comparisons because Lean heartbeats do not measure external CPU time.
