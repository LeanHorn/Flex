# RQ3a: coverage on refinement-typechecker CHCs

Run from `flex-benchmarks`, with a sibling checkout of `Flex`. Inputs are generated
VC statements and their definitions; existing VC proofs and handwritten witnesses
are never loaded. All results and frozen snapshots go under the chosen output
folder, normally gitignored `Flex/evaluation/results/RQ3a/`.

## Corpus and configurations

| Suite | Predicate-bearing queries |
| --- | ---: |
| `flux_tests` | 337 |
| `flux-medium` | 96 |
| `wave` | 36 |
| `liquid-fixpoint` | 75 |
| **Total** | **544** |

All 544 stay in the denominator, including the eight currently unfinished source
specifications. The Liquid Fixpoint suite includes two confirmed UNSAT fixtures;
positive-test directory membership is not a SAT guarantee. No outcome filtering.

| CLI configuration | Main `flex` pipeline | Internal budget |
| --- | --- | ---: |
| `zap_fix` | Zap → Fix → discharge | 180 s |
| `se` | Spacer → Eldarica if needed → discharge | 180 s |
| `flex` | Zap → Fix → Spacer/Eldarica → discharge | 360 s: two 180 s blocks |

All use the same checked discharge, True/False preprocessing, no nesting, and no
postprocessing. Fix decides candidates with the exact SMT encoding only: the native
Lean fallback for undecided synthesis queries is off (`flex.automation.nativeFallback`),
and undecided candidates are dropped. Certification, safety validation and discharge
still use Lean automation. Non-linear arithmetic is encoded (`flex.smt.encodeNonlinear`
on; off by default in Flex). `invocation.json` records these settings
(`native_fallback`, `smt_encode_nonlinear`); earlier runs used the fallback and must not
be pooled with new ones.
Fix escalates Bank → Basic → Standard → Deep. The combined arm
reserves one 180 s block for Zap + Fix and one for S/E, cancelling each at its own
deadline. `se_zap_fix` uses the same blocks in the opposite order.
Within the S/E block, remaining time is shared among untried backends. The entire
attempt—export, solver retries, import, validation, certification and closing—uses
that allocation. Unused backend time passes forward; accepted progress is retained.

Other limits: 90 s per external solver call, recomputed against its backend
deadline immediately before each call, including retries;
4,000,000 phase heartbeats; 40,000 proof-automation heartbeats; recursion limit
16,384. The outer process watchdog is internal budget + 120 s (300/480 s), allowing
source elaboration and kernel checking, followed by bounded solver cleanup. Fix's
own synthesis cap is set to the pipeline budget; the enclosing block deadline
provides the tighter limit. Cancellation is cooperative, so actual time can exceed
an internal deadline. The watchdog remains separate. A killed process has no
certified outcome unless its record proves one.

New runs record `timeout_policy: reserved_blocks_v1`. Earlier runs used a shared
deadline and a 180 s solver cap; their recorded settings remain unchanged and
must not be pooled with the new policy as a uniform timing experiment.

The combined arm gets twice the budget: compare its coverage with that extra time
explicit. Custom combined budgets must accommodate both standalone blocks:
`--combined-timeout` must be at least twice `--flex-timeout`.

## First setup

Use Python 3.9+, Elan/Lean, a C/C++ build toolchain, Z3, Java and Eldarica. Check out
matching, pinned revisions of both repositories; share those revisions with the
results. The harness records commits, source hashes and solver binary versions.

```sh
git clone https://github.com/LeanHorn/Flex.git
git clone https://github.com/LeanHorn/flex-benchmarks.git
cd Flex
# Use the repository's lean-toolchain and lake-manifest.json pins.
lake --version
MATHLIB_NO_CACHE_ON_UPDATE=1 lake build Flex.Tactic.Tactics.Flex
cd ../flex-benchmarks
z3 --version
eld -h
```

The current development runs used Lean 4.34.0, Z3 4.15.4 and Eldarica 2.3. cvc5 is
provided by the pinned Lean dependencies; a separate CLI installation is not
required. Put `z3` and `eld` on PATH, or pass `--z3 /path/to/z3 --eldarica /path/to/eld`.

On macOS, install Xcode command-line tools and Java, and use the Z3 executable for
your architecture. On Ubuntu, the native packages and Eldarica installation are
specified in the [tested CI setup](../../.github/workflows/lean_action_ci.yml).
Follow its `LEAN_CC` wrapper as well: cvc5 needs the host glibc while Lean uses its
bundled C++ runtime. Avoid unpinned `lake update` when reproducing a run.

For figures, create a Python environment (outside the benchmark source tree) and
install `matplotlib`; the runner and CSV statistics otherwise use the standard
library only. `--no-figures` works without plotting dependencies.

## Run from flex-benchmarks

```sh
# Small end-to-end check: four queries × three configurations.
python3 -B ../Flex/evaluation/RQ3a/benchmark.py \
  --benchmarks . --count 4 --configs zap_fix se flex \
  --workers 1 --output ../Flex/evaluation/results/RQ3a/rq3a-smoke

# Full RQ3a: 544 queries × three configurations = 1,632 trials.
python3 -B ../Flex/evaluation/RQ3a/benchmark.py \
  --benchmarks . --count 0 --configs zap_fix se flex \
  --workers 1 --output ../Flex/evaluation/results/RQ3a/rq3a-full
```

For the two-arm comparison already measured, use `--configs zap_fix se` (1,088
trials). To investigate one arm, use `--configs se` or `--configs zap_fix`.
`--diagnostic` retains detailed failure traces; use the same tracing setting for
all compared runs. `--skip-classification` omits the graph analysis for a
diagnostic run; input sizes and predicate/proof measurements are still recorded.

Inputs and build artifacts are frozen before trials. Each trial classifies its
query's predicate graph (acyclic/cyclic/mixed) in the same Lean process, before the
measured tactic: it is excluded from `flex_ms` and phase times, included in `wall_ms`,
and never excludes queries. Each configuration starts from the
original VC. One trial is run per query/configuration in a seeded, rotated order.
For repetition variability, use separate output folders and report each run;
medians below are across queries, not repeated measurements of one query.

## Workers, server and laptop

`--workers N` bounds concurrent Lean query processes. Each gets its own solver
processes and the same budget. One coordinator appends results, so workers never
write shared result files concurrently. Completion order can differ from the
recorded submission order. Solvers/JVMs may use additional threads and memory.

- For clean latency numbers, use **one worker on an otherwise idle machine**.
- On a Mac, start with **2 workers** for coverage; try 4 only with spare CPU/RAM.
- On a server, start with **4–8 workers**, then scale within allocated physical
  cores and available memory. Check for swapping and throughput before increasing.
- Keep worker count, machine and settings identical between compared arms. The
  parallel run measures performance under that concurrency, not isolated latency.
  Do not run unrelated builds or repairs during the final timing experiment.

On macOS prefix the command with `caffeinate -is`; keep AC connected and the lid
open. On a server run inside `tmux`, or a scheduler allocation with sufficient
wall time and memory. Run one coordinator per output folder; a lock prevents two
coordinators from corrupting a run. Separate allocations need separate outputs.

```sh
# Server example, from flex-benchmarks inside tmux or your allocation:
python3 -B ../Flex/evaluation/RQ3a/benchmark.py \
  --benchmarks . --count 0 --configs zap_fix se flex \
  --workers 8 --output ../Flex/evaluation/results/RQ3a/rq3a-server

# Live progress, including all active workers:
python3 -B ../Flex/evaluation/RQ3a/benchmark.py \
  --output ../Flex/evaluation/results/RQ3a/rq3a-server --progress

# Graceful stop: finish active trials, then stop scheduling.
touch ../Flex/evaluation/results/RQ3a/rq3a-server/STOP
# Remove STOP and repeat the exact original command with --resume.
```

`--prepare-only` freezes the build/selection without running trials. Resume with
the same settings and `--resume`; completed trials are reused. Start a new output
folder after code/settings changes. Reports refresh periodically and at
finish; progress reads the latest records directly.

## Measurements and interpretation

Coverage uses kernel-checked retained progress and disjoint outcomes:

1. Full proof.
2. All invariants inferred and heads eliminated; residual remains.
3. All invariants inferred; head obligations remain or are unknown.
4. Some predicates eliminated.
5. No certified predicate progress.
6. Source-preparation failure.

The raw Lean status `partial` means only that a goal remains. It is **not** counted
as partial inference without evidence of retained predicates. Imported model
attempts are recorded separately from accepted progress. The harness constructs
and kernel-checks the proof from actual residual goals to the original statement;
it never precomputes a residual. Only `propext`, `Classical.choice`, and
`Quot.sound` are accepted; no admitted proofs or extra axioms.

| Metric | What is measured |
| --- | --- |
| `flex_ms` | Tactic time, including synthesis, solver calls, certification and discharge |
| `wall_ms` | Whole query process: Lean startup, elaboration, tactic, formatting and independent kernel check |
| `startup_ms` | Process launch to the first harness event |
| Phase times | Zap, Fix, solver calls, discharge, kernel checking; nested phases must not be summed together |
| Backend scheduling | Attempted/skipped backends, skip reasons, completed calls/retries, and actual allocated deadlines |
| Heartbeats | Tactic/total/phase effort, in Lean's displayed units; external solver work is not counted |
| Predicate counts | Original, remaining, eliminated; retained heads and full-proof milestones |
| Proof metrics | Expression nodes, distinct constants, approximate depth and kernel-check time |
| Input structure | Source bytes and optional acyclic/mixed/cyclic classification |

`statistics.csv` gives count, sum, mean, min, p25, median, p75, p90, p95 and max for
each metric, overall and by suite. It separates all measured queries, full proofs,
and non-proofs. Missing measurements are excluded with their sample count shown;
preparation failures are not zero-time successes. Outer timeouts have measured
process wall time but may lack tactic time. Percentiles use linear interpolation.

`comparisons.csv` measures paired timings only on queries **both arms fully prove**,
with the same count, mean, quartiles, p90/p95 and range for each arm, plus exclusive
coverage. Its `first_*` and `second_*` columns name those distributions; `metric`
distinguishes tactic time (`flex_ms`) from whole-query time (`wall_ms`).
Never interpret the all-query median
alone as proving speed: an unsupported export can return almost immediately.
Peak recursion depth and solver CPU/RSS are not measured; the recursion limit is
recorded explicitly. Budget exhaustion is not evidence that a VC is unprovable.

## Results and reports

| Files | Contents |
| --- | --- |
| `selection.json`, `settings.json`, `metadata.json`, `schedule.json` | Corpus hashes, budgets, workers, revisions, versions and submission order |
| `source/`, `compiled/` | Frozen source and compiled Flex artifacts |
| `results.jsonl`, `results.csv` | Per-query results, times, metrics and provenance |
| `statistics.csv`, `comparisons.csv`, `summary.json` | Timing distributions, paired comparisons and coverage |
| `runs/…/classification.json`, `phases.csv` | Per-trial graph analysis and individual phase measurements |
| `runs/` | Lean inputs, failure logs, solver queries/models and residuals |
| `report.pdf`, `figures/` | Disjoint coverage and proof-completion curves |

JSONL stores one complete JSON record per query/configuration, including events
and artifact paths. CSV is the analysis format for Python/R/spreadsheets; JSON
holds structured settings and summaries. CSV missing values are empty cells,
JSON missing measurements are `null`; neither means zero. Timing columns ending
in `_ms` use milliseconds (`kernel_ns` uses nanoseconds). Sample count `n` is
recorded with each distribution. Mean and average are the same column, `mean`.

```sh
# Recompute tables from saved records; no solver or proof runs:
python3 -B ../Flex/evaluation/RQ3a/report.py \
  ../Flex/evaluation/results/RQ3a/rq3a-full --tables-only
# Generate figures too:
python3 -B ../Flex/evaluation/RQ3a/report.py \
  ../Flex/evaluation/results/RQ3a/rq3a-full
```

For explicit failed-only recovery, `report.py NEW_OUTPUT --merge ORIGINAL RETRY`
combines records, checking matching input hashes and budgets. Later records replace
earlier attempts for the same query/configuration; it never picks the fastest or
best outcome. Each record retains its source run. Such a report is labelled a
consolidated diagnostic result, not a uniform timing experiment.

CHC-COMP belongs to [RQ3b](../RQ3b/README.md), with separate commands and outputs.
This entry point runs RQ3a only.
