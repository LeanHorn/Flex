# RQ4: qualifier scraping

Compare **Bank, Basic, Standard, Deep, and Incremental** using the main `flex`
pipeline, with Zap followed by Fix and residual discharge. No external CHC
backend runs. Run from `flex-benchmarks` with a sibling checkout of `Flex`.

## Fixed paper population

`selection.json` identifies **391 CHCs / 1,955 trials**, with original source and
prepared Lean hashes. It contains no Imp inputs:

| Suite | CHCs |
| --- | ---: |
| Flux regression tests | 95 |
| Flux examples | 57 |
| WaVe | 9 |
| Liquid Fixpoint | 20 |
| CHC-COMP | 192 |
| RQ1 case studies | 18 |
| **Total** | **391** |

These are 274 cyclic-only and 117 mixed inputs **selected from earlier
kernel-checked Incremental full proofs that retained Fix inference**. This is a
comparison on that fixed success-selected population, not a corpus-wide coverage
estimate. The new run does not screen again or remove new failures. Incremental
is rerun like every other configuration; it is not assumed to prove everything.
Every recorded case identity is retained, without new deduplication.

Inputs come from the committed VC specifications and definitions and the
CHC-COMP archives in `flex-benchmarks`. The runner flattens specification imports
and verifies byte-for-byte agreement with the measured input hashes. It does not
load existing VC proofs, supply handwritten invariants, or reuse residual goals.

## Setup

Use Python **3.10+**, Elan/Lean, Z3 on `PATH`, and the build dependencies in
[Lean CI](../../.github/workflows/lean_action_ci.yml). RQ4 needs neither Eldarica
nor Java. The pinned Lean dependencies provide cvc5 for proof reconstruction.
Tested with Lean 4.34.0 and Z3 4.15.4.

```sh
git clone https://github.com/LeanHorn/Flex.git
git clone https://github.com/LeanHorn/flex-benchmarks.git
cd Flex
# Use the checked-in dependency pins; do not run an unpinned lake update.
lake --version
z3 --version
lake --log-level=error build Flex.Tactic.Tactics.Flex
cd ../flex-benchmarks
```

Inputs are verified against the hashes in `selection.json`; later `flex-benchmarks`
revisions work if the selected sources and archives still match. A mismatch fails
preparation explicitly.
The runner uses Flex's toolchain and packages, not each benchmark subproject's
Lake pin. It compiles and freezes dependencies once before measured trials.
Keep the checkout and dependency packages intact until the run finishes.

First run the **three-case smoke test**, one real input from each corpus:

```sh
python3 -B ../Flex/evaluation/RQ4/benchmark.py --benchmarks . --smoke \
  --output ../Flex/evaluation/results/RQ4/smoke
python3 -B ../Flex/evaluation/RQ4/report.py \
  --results ../Flex/evaluation/results/RQ4/smoke
```

This runs all five configurations, including expected partial results under
weaker scraping. A successful harness test does not require all 15 proofs to close.
For reference, our smoke run proved 1/3, 2/3, 3/3, 3/3, and 3/3 in the
configuration order above.

## Full run, progress, and resume

```sh
python3 -B ../Flex/evaluation/RQ4/benchmark.py --benchmarks . --workers 1 \
  --output ../Flex/evaluation/results/RQ4/full

python3 -B ../Flex/evaluation/RQ4/benchmark.py \
  --output ../Flex/evaluation/results/RQ4/full --progress
```

`--workers N` controls concurrent query processes. Each trial gets the same
independent budgets. Use one worker for isolated latency; more workers can
improve throughput if sufficient physical cores and RAM are available. Each Lean process can use several GB. Report worker count with the
timings, keep it fixed across configurations, and avoid swapping and competing
workloads. The seeded schedule rotates configuration order between queries.

`--prepare-only` verifies all 391 inputs and freezes the build without running
trials. Continue with the same arguments plus `--resume` (omit `--prepare-only`).
Create `OUTPUT/STOP` to stop scheduling after active trials finish; remove it to
resume. A lock prevents two coordinators using the same output. Resume preserves
completed measurements and rejects changed settings or runtime dependencies.
Use a new output directory for a different revision or configuration.

## Configurations and limits

| Name in data | Paper label | Qualifier sources |
| --- | --- | --- |
| `bank` | Bank | 19 built-in templates; scraping disabled |
| `basic` | Basic | Bank plus atoms from constraint heads |
| `standard` | Standard | Also premises, guarded arithmetic, and selected direct definitions |
| `deep` | Deep | Also helper definitions, quantified bounds, and accumulator relationships |
| `auto` | Incremental | Bank → Basic → Standard → Deep, extending the pool when synthesis is not accepted |

All use the public configurations and identical instrumentation. Fixed
Standard/Deep may first try source candidates before their full pool. Generation
limits and ordering mean independently generated pools need not be nested.

- **Zap: 60 s**, including its preprocessing/discharge; **Fix: 120 s** shared
  across scraping, candidate checks, certification, and discharge. Unused Zap
  time does not extend Fix. Accepted checkpoints survive internal timeouts.
- **300 s process watchdog** covers imports, preparation, classification, tactic,
  and independent kernel checking. A killed process is not credited with an
  unverified partial result. Timeout kinds are recorded separately.
- 4,000,000 phase heartbeats; 200,000 native synthesis-fallback heartbeats;
  40,000 proof-automation heartbeats; 500,000 discharge heartbeats; recursion
  limit 16,384.
- True/False preprocessing enabled; nesting and optional postprocessing disabled.
  Nonlinear SMT encoding enabled. Native synthesis fallback is enabled here;
  this intentionally differs from RQ3a's current SMT-only synthesis setting.

`invocation.json` records the actual per-query settings. The runner calls the
same `Flex.Portfolio.flexImpl` used by `flex`, with only Fix in the backend list.

## Data and reporting

Raw records are flushed after every trial. CSV/JSON statistics are generated
after trials, outside the timed window. No plotting packages are needed to run.

```sh
python3 -B ../Flex/evaluation/RQ4/report.py \
  --results ../Flex/evaluation/results/RQ4/full

# Optional paper-style figures; install these in a Python virtual environment.
python3 -m pip install -r ../Flex/evaluation/RQ4/requirements.txt
python3 -B ../Flex/evaluation/RQ4/report.py \
  --results ../Flex/evaluation/results/RQ4/full --figures
```

| Output | Contents |
| --- | --- |
| `results.jsonl`, per-trial logs/events | Raw coverage, checkpoints, timing, and failures |
| `ablation_results.csv` | One row per case/configuration; timing, candidates, inference, head elimination, proof completion, heartbeats, memory, and input/proof sizes |
| `scraping_stages.csv`, `candidate_counts.csv`, `candidate_rounds.csv` | Attempted/accepted/retained levels, candidates by predicate and round |
| `fix_phases.csv`, `scrape_sources.csv`, `scrape_details.csv`, `oracle_*.csv` | Scraping origins, limits, synthesis, safety, certification, and oracle diagnostics |
| `ablation_statistics.csv`, `ablation_comparisons.csv` | Detailed distributions and paired measurements |
| `rq4-summary/` | Compact `summary.json`, coverage/timing/candidate/paired CSVs, and optional figures |
| `selection.json`, `settings.json`, `metadata.json`, `runtime*.json`, `source/` | Inputs, budgets, host/power observations, revisions, hashes, and frozen runtime sources |

`flex_ms` measures tactic time; `wall_ms` also includes startup, imports and final
kernel checking. Timings distinguish successful proofs from all measured trials.
Summaries give sample counts, mean, p25, median, p75, p90, p95 and maximum. Missing
measurements remain null/empty. Speed ratios use jointly proved queries and
geometric means. Never sum nested phase timings as if they were disjoint.

Candidate pool size is the maximum across visited PA stages of the sum of initial
candidates over predicates. It counts instantiated candidates, not templates;
adding all stage counts would double-count Incremental's retained candidates.
Oracle telemetry counts logical validation requests, not physical SMT calls.
Peak RSS describes the Lean child, not aggregate simultaneous solver memory.
One repetition measures neither run-to-run variance nor actual peak recursion.

The optional figures show CHCs proved within each tactic-time budget and median/
p90 candidate-pool sizes. Coverage curves are monotone visual interpolations;
the exact measured points and plotting metadata are exported alongside them.
The report accepts changed coverage and failures: it does not assert particular
counts. `--rebuild` regenerates detailed CSVs from a complete run's raw
events and logs. `Scraping/paper_appendix.py` supplies the plotting helpers;
its own command-line mode is legacy, so use `report.py` for new results.

To package a completed run without binaries/build caches:

```sh
python3 -B ../Flex/evaluation/RQ4/export.py \
  --results ../Flex/evaluation/results/RQ4/full --output /path/to/rq4-data
```

It exports compressed JSONL, analysis CSVs, raw diagnostics, source snapshots,
provenance and checksums. No measurements are rerun.
