# RQ2: Zap reduction efficiency

Compare **Zap**, **Zap_grind**, and **Zap_aesop** on the same original CHCs.
All use Zap's strongest-solution computation. Only the proof of each eliminated
predicate's head changes: constructive proof terms, default `grind`, or default
`aesop`. There is no fallback between variants.

## Configuration

The harness first prepares the original goal, retaining the proof connecting it
to the original statement. Classification and trials use the same preparation
limits. The following invocation receives that prepared goal:

```lean
flex (backends := []) (config := {
  zapCertificate := .constructive  -- .grind or .aesop
  preprocess := false  -- already prepared by the harness
  nesting := false
  postprocess := false
  closeLeaves := false
  splitFree := false
  zapHeartbeats := 200000
  totalTimeout := 60 })
```

No Fix, SMT oracle, residual discharge, nesting, or post-processing runs.
Common preprocessing simplifies trivial guards and false predicates. `postprocess
:= false` also disables Zap's internal residual cleanup. Each trial runs from the
original statement; no residual is cached or reused. Preparation failure stops
the trial instead of passing an unprepared input to Zap. Prepared expression
hashes must match classification before a trial receives reduction credit.

## Run

Use the repository's pinned Lean toolchain and installed Lake dependencies.
Python 3.9+ is sufficient; this experiment does not invoke an external solver.
Run the commands below from the Flex repository root. The runner automatically
loads shared utilities from `scripts/chc_parity.py` and `scripts/benchmark_flex.py`;
no `PYTHONPATH` setup is needed.

```sh
# Pilot: 100 CHC-COMP cases; select by structure, then run all three variants.
python3 -B evaluation/RQ2/benchmark_rq2.py \
  --corpus evaluation/CHC-COMP/generated \
  --output evaluation/RQ2/results/pilot100 --count 100

# Full eligible corpus, with three repetitions per variant.
python3 -B evaluation/RQ2/benchmark_rq2.py \
  --corpus /path/to/generated-chc-comp \
  --output evaluation/RQ2/results/chc-comp --count 0 --repeats 3

# Refinement-typechecker statement manifests (same format as benchmark_flex.py).
python3 -B evaluation/RQ2/benchmark_rq2.py \
  --manifest /path/to/cases.json \
  --output evaluation/RQ2/results/flux --count 0 --repeats 3

python3 -B evaluation/RQ2/benchmark_rq2.py --output evaluation/RQ2/results/pilot100 --progress

# Retry a fixed manifest with constructive Zap only; preserve preparation failures.
python3 -B evaluation/RQ2/benchmark_rq2.py \
  --manifest /path/to/failures.json --count 0 --variants zap \
  --include-unclassified --output evaluation/RQ2/results/targeted-retry
```

A statement manifest contains `cases`, each with `case`, `suite`, `generated`,
`declaration`, and `format: "lean_statement"`. `generated` names a self-contained
Lean file containing specification definitions, without a proof of the VC.
Paths may be relative to the manifest. SMTLib-to-Lean corpora use their existing
`*-manifest.json` files instead.

For example:

```json
{"cases": [{"case": "flux/example", "suite": "flux",
  "generated": "statements/example.lean", "declaration": "F.Example",
  "format": "lean_statement"}]}
```

`make_manifests.py` builds such manifests from Flux projects and the
LiquidHaskell corpus. Each Flux `Flux/VC/*.lean` file is flattened with its
project-local imports, so only Flex and its dependencies remain; the projects'
own toolchain and Flex pins are not used. Uninterpreted `def f : T := sorry`
becomes `opaque f : T` in the copies. LiquidHaskell files get `FixpointImport`
inlined. Every case is classified in a separate process, avoiding declaration
name collisions between flattened statements.

```sh
python3 -B evaluation/RQ2/make_manifests.py flux PROJECT... --output DIR
python3 -B evaluation/RQ2/make_manifests.py liquidhaskell path/to/liquid-haskell --output DIR
```

Timing trials run **serially**, in a recorded seeded order. Stop competing builds
and evaluations. On macOS, prefix the command with `caffeinate -is` and leave the
lid open. Compilation and module loading happen outside the tactic timer.
Classification uses two workers and one process per case, so one slow input does
not cancel other cases. It finishes before timing begins.

`--classify-only` prepares the selection and frozen build without timing trials.
`--run-only` resumes those exact settings and inputs. Creating `OUTPUT/STOP`
stops between trials; remove it before resuming. Completed trials are preserved.

## Selection and measurements

Only **acyclic-only or mixed graphs with an eliminable predicate**, after common
preprocessing, qualify. Purely cyclic graphs are excluded even when cutting a
cycle would leave removable vertices. As in `flex`, classification descends
positive `∀` and `∧` in the prepared goal and sums over every predicate (∃) goal.
Classification does not repeat preprocessing during this traversal. Graph membership
and Zap's elimination/cut partition are recorded separately. Source duplicates
are removed before selection.
The 100-case pilot balances acyclic/mixed cases and spreads them across suites,
using a fixed seed and **no success-based filtering**. `--count 0` uses every
eligible case. Classification errors stay in the inventory.
For a targeted retry, `--include-unclassified` also schedules these cases and
keeps their failures in the denominator. A successful but unclassified reduction
is reported separately, never silently counted as an eligible success.

A successful **reduction** eliminates the expected predicates, leaves no unproved
head obligations, and has a kernel-checked reduction certificate. It need not prove
the remaining VC. The harness abstracts the remaining goals as assumptions and
checks the resulting `residual → original` proof, rejecting `sorry`, unresolved
variables, or nonstandard axioms. Residuals are used only in memory.

| Paper measurement | Recorded field |
|---|---|
| Constraints successfully reduced | `status = reduced` |
| Zap reduction wall time (ms) | `ms` |
| Reduction heartbeats | `heartbeats` (raw ticks / 1000) |
| Proof-package dependency depth | `depth` |
| Distinct proof-package constants / expression DAG nodes | `constants` / `nodes` |
| Generated auxiliary declarations | `auxiliary_declarations`; names in JSON |
| Complete proof-package kernel recheck time (µs) | `kernel_us` |
| Preparation time / heartbeats | `prepare_ms` / `prepare_heartbeats` |
| Solution / certificate construction time | `sol_ms` / `build_ms` |

Proof metrics include every reachable declaration introduced during the trial,
following dependencies in both types and bodies. Pre-existing library declarations
form the boundary. Helpers are replayed in dependency order into the environment
from before preparation, then the final certificate is checked. The `depth` field
follows helper bodies and types without materializing an expanded proof; `nodes`
counts structurally distinct expression nodes. `direct_depth`, `direct_nodes`,
`direct_constants`, and `approx_depth` retain measurements of the final expression
alone. `metrics_version = 2` distinguishes these results from the old measurements
that omitted auxiliary proofs. Large residual types can still dominate depth.

Reduction time, heartbeats, and elimination counts sum over all Zap invocations
within a query; the internal wall-clock deadline is shared across them.
Preprocessing, Flex bookkeeping, certificate assembly for measurement, and kernel rechecking are outside it;
`flex_ms` records the complete post-preparation `flex` invocation separately.
Preparation receives 2,000,000 heartbeats and 120 seconds; Zap receives 200,000
heartbeats and a fresh 60-second internal deadline after preparation succeeds.
Use `--prepare-heartbeats`, `--prepare-timeout`, `--heartbeats`, and `--timeout`
to change these independent limits. The process safeguard defaults to preparation
plus Flex plus 120 seconds for loading and kernel measurement (300 seconds with
defaults). The recursion limit is 4096. All budgets and selected `--variants` are
recorded. `last_started_subphase` helps locate interrupted work.

`summary.json` contains arithmetic success-only means for Table 2, geometric
means for proof metrics, and paired ratios on jointly reduced queries. Compare
coverage on the entire fixed selection; never replace failed cases. For repeated
runs, raw trial counts are explicit—do not label them as distinct CHC counts.

## Outputs

- `selection.json`: exact inputs, hashes, classification, and sampling rule.
- `results.csv` / `results.jsonl`: per-query, per-variant, per-repeat measurements.
- `summary.json`: coverage, means, and paired ratios.
- `runs/`: original Lean statements plus instrumentation, with raw logs.
- `source/`, `compiled/`, `settings.json`: frozen implementation, build, and limits,
  including modules imported by benchmark statements.

The Lean instrument is `evaluation/RQ2/RQ2.lean`; orchestration is
`evaluation/RQ2/benchmark_rq2.py`. Results are gitignored.
