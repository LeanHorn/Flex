# RQ3b: coverage on CHC-COMP

Compare three `flex` configurations with Spacer and Eldarica on the original
SMT inputs. Use all 1,730 published tasks in `flex-benchmarks/CHC-COMP`, including
upstream duplicates. The default deliverable is CSV/JSON: no plotting packages
or LaTeX required.

| CLI configuration | Internal budget | Order |
|---|---:|---|
| `se` | 180 s | Spacer, then Eldarica |
| `zap_fix` | 180 s | Zap, then escalating PA scraping |
| `se_zap_fix` | 360 s | S/E stage, then Zap + Fix; at most 180 s each |
| `native_spacer` | 90 s | Original SMT input, requesting a model |
| `native_eldarica` | 90 s | Original SMT input, requesting a model |

Each Flex solver call is capped at 90 s and the remaining backend allocation,
recomputed immediately before every call, including retries. Within S/E, remaining
time is shared among untried backends. A backend allocation covers export, all calls,
import, validation, certification and closing; unused time passes forward.
All Flex arms use the same discharge automation, 4,000,000 phase heartbeats,
40,000 proof-automation heartbeats, and True/False preprocessing. Nesting and
optional postprocessing are off. As in RQ3a, Fix decides candidates with the exact
SMT encoding only (`flex.automation.nativeFallback` off), with non-linear arithmetic
encoded (`flex.smt.encodeNonlinear` on); certification and discharge still use Lean
automation. Fix escalates Bank → Basic → Standard → Deep.
Accepted invariants survive stage timeouts. Zap and Fix act where predicates
remain; an open residual proof does not undo an accepted S/E invariant.
The combined arm has twice the budget: report its coverage with that extra cost.
Both combined orderings reserve a separate 180 s block for Zap + Fix and for S/E.
Custom `--combined-timeout` must allow two `--flex-timeout` blocks.
The policy is recorded as `reserved_blocks_v1`; earlier pilot runs keep their
original settings and must not be pooled with this policy for timing comparisons.

## Collaborator setup

Use sibling checkouts of `Flex` and `flex-benchmarks` at agreed commit revisions.
The benchmark checkout must contain `CHC-COMP/manifest.json`, `selection.json`,
and the archives listed in the manifest. The harness unpacks and verifies them;
no manual extraction or translation is needed.

Prerequisites: Python 3.9+, Elan/Lean, a C/C++ toolchain, Z3, Java and Eldarica.
Use Flex's `lean-toolchain` and `lake-manifest.json`; do not run `lake update`.
The pilot used Lean 4.34.0, Z3 4.15.4 and Eldarica 2.3. cvc5 is supplied by
pinned Lean dependencies. On Ubuntu, follow the package installation and
`LEAN_CC` wrapper in [CI](../../.github/workflows/lean_action_ci.yml).

```sh
cd Flex
z3 --version
eld -h
MATHLIB_NO_CACHE_ON_UPDATE=1 lake build Flex.Tactic.Tactics.Flex
python3 -B evaluation/RQ3a/test_harness.py
cd ../flex-benchmarks
```

## Full run

Run inside `tmux` or a server allocation. Start with 4–8 workers, within the
allocated physical cores and RAM; solvers may use additional threads. Keep the
worker count fixed, avoid swapping and unrelated work. Use one worker for isolated
latency. Build and classification time are excluded from query timings.

```sh
# Prepare all 1,730 tasks × five arms = 8,650 trials. No evaluation yet.
python3 -B ../Flex/evaluation/RQ3b/benchmark.py \
  --benchmarks . --count 0 --workers 8 \
  --output ../Flex/evaluation/results/RQ3b/full --prepare-only

# Start; use this same command to resume an interrupted run.
python3 -B ../Flex/evaluation/RQ3b/benchmark.py \
  --benchmarks . --count 0 --workers 8 \
  --output ../Flex/evaluation/results/RQ3b/full --resume

python3 -B ../Flex/evaluation/RQ3b/benchmark.py \
  --output ../Flex/evaluation/results/RQ3b/full --progress
```

Graceful stop: create `OUTPUT/STOP`, let active trials finish, then remove that
file and repeat the run command. A lock prevents two runners using one output.
Resume rejects changed settings, input hashes, runner code, dependency pins or
solver launchers. Incomplete attempts are archived; completed trials are reused.
Keep dependencies and solver installations unchanged: compiled Flex artifacts
are copied, external installations are not.

To select arms, pass `--configs se zap_fix se_zap_fix`, or
`--configs native_spacer native_eldarica` for baselines alone. Explicit lists
replace the default five arms. Use a new output directory for different settings.

## Local pilot

Use **60 queries and four workers**, with `--count 60 --seed 20261104 --workers 4`
and a separate output directory. This gives 300 trials. Selection covers every
source suite, rotating across within-suite SMT-size quartiles, without filtering
on outcomes. It is a suite-balanced pilot, not a corpus-weighted coverage estimate.
The internal budgets sum to 15 worker-hours before startup/checking overhead;
successful short trials reduce actual runtime.

On macOS, prefix the run command with `caffeinate -i -s`; keep AC connected and
the lid open. The screen can turn off. Run inside `tmux`, or use `nohup` with
stdout/stderr redirected to a log if the terminal may close.

## CSV data

Coverage distinguishes **all invariants retained**, **all heads eliminated**, and
**full kernel-checked proof**, plus partial predicate progress. A native model is
recorded separately and is not counted as a Lean proof.

| File | Observation and contents |
|---|---|
| `results.csv` | One row per query/configuration: outcomes, milestones, predicate counts, structure, hashes, budgets, timings, proof metrics, backend attempts/skips and completed calls/retries |
| `coverage.csv` | Counts and percentages per configuration, overall and by suite; selected/completed/pending denominators |
| `statistics.csv` | n, mean, min, quartiles, median, p90/p95 and max for timing/effort metrics, overall and by suite |
| `comparisons.csv` | Paired coverage differences and timing on queries both Flex arms fully prove |
| `phases.csv` | Per-query phase totals, heartbeats, completed calls and unfinished calls |
| `phase_events.csv` | Every phase start/end/timeout/skip, actual allocation/deadline, monotonic timestamp and raw heartbeat counter |
| `events.csv` | Export/import/certification events, PA stages, candidates, rounds and final checks |
| `discrepancies.csv` | Native-SAT cases whose invariants S/E-only did not retain |

Join on `(study, case, configuration)`; event files add `event_index`.
Native rows use `native_spacer`/`native_eldarica` as configuration names.
`native_ms` is the solver call, `flex_ms` the tactic, and `wall_ms` the entire
Lean process. Timings use milliseconds, except `kernel_ns` (nanoseconds).
Heartbeats use Lean's displayed units; raw phase event counters use thousandths
of those units. Nested phase durations overlap: do not sum them as total time.

CSV booleans are `True`/`False`; missing measurements are empty cells, not zeros.
Unfinished phases have no total time; `completed_ms` retains completed calls.
Percentages use all selected tasks, including failures; `pending` identifies
unfinished trials. Percentiles use linear interpolation across queries, not repeats.
Statistics separate full proofs from non-proofs, and native models from non-models.
A quick export failure is not a quick proof.

Proof depth/node/constant metrics describe the final proof expression; referenced
auxiliary theorem bodies are not expanded. `kernel_ns` measures the final bridge
check, not every kernel check during tactic execution. Peak recursion, solver CPU
time and peak memory are not measured. The recursion limit is recorded. Nested
event arrays, such as per-predicate PA candidates, are JSON inside CSV cells.

## Artifacts and regeneration

Raw records remain in `results.jsonl`, including embedded phase events for new
runs. Keep `selection.json`, `classification.json`, `settings.json`, `metadata.json`
and `schedule.json` with them. SMT inputs, models, Lean inputs, logs and residuals
live in `native/` and `runs/`. Copy the complete output directory for an audit;
CSV analysis needs neither Lean nor solvers. Results are gitignored.

Recreate CSVs from saved records without running proofs or solvers:

```sh
python3 -B ../Flex/evaluation/RQ3b/report.py ../Flex/evaluation/results/RQ3b/full
```

The runner refreshes reports periodically and at completion; `--progress` reads
the latest records immediately. Optional plots require `matplotlib` and an explicit
`--figures` on the report command. No LaTeX is generated. RQ3b's small entry points
share implementation in `evaluation/RQ3a/` and `scripts/`; share the whole Flex
checkout, not just the RQ3b directory.

The outer watchdog allows 120 s beyond Flex's internal limit for startup,
checkpoint output and kernel checking (30 s beyond native solver limits).
Internal cancellation is cooperative and may overrun while an operation stops;
the watchdog remains necessary. Actual allocated time and observed time are separate.
`internal_timeout` and `external_timeout` distinguish a tactic deadline from the
outer watchdog. A raw `partial` only counts as predicate progress when retained
inference is kernel-checked. Watchdog failures stay in the denominator.
