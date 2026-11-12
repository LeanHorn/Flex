# Automatic scraping profile

One `flex` run per CHC: Zap, then Fix with automatic Bank → Basic → Standard → Deep
scraping. Fix adds qualifiers only when the previous level does not yield an
accepted assignment. S/E is disabled. Native Lean synthesis fallback is enabled
alongside SMT checks; no handwritten invariants or per-case qualifiers are added.

This measures escalation behavior, not standalone-level performance. A level that
is never reached has not failed. Synthesis acceptance precedes certification;
count an invariant as retained only from the kernel-checked final checkpoint.

The initial cohort contains all cyclic/mixed inputs from 34 RQ1, 21 Liquid Fixpoint,
10 WaVe, 7 FPICE and 52 Mochi cases, plus all 25 current Imp programs: 149 cases.
Selection does not filter by proof outcome. Imp's `imp_prepare` exposes its
generated VC before Flex, without adding invariants.

```sh
python3 evaluation/Scraping/benchmark.py --manifest MANIFEST.json \
  --output evaluation/results/Scraping/auto149-20261112 --workers 3
python3 evaluation/Scraping/benchmark.py \
  --output evaluation/results/Scraping/auto149-20261112 --progress
```

Defaults: 180 seconds shared by the Flex pipeline; a 300-second process watchdog
also covers imports, VC preparation, classification and final kernel checking.
Phase heartbeat limit: 4,000,000; native synthesis fallback: 200,000; proof
automation: 40,000; recursion limit: 16,384. Builds happen once before trials;
compiled Flex artifacts and inputs are frozen. Concurrent workers affect timing.

Results use the existing RQ3 CSV/JSON format: per-query coverage, predicate counts,
head elimination, tactic/process time, heartbeats, phase events and proof metrics.
`scraping_stages.csv` adds each attempted level's candidates, rounds, time and
acceptance. `events.csv` and raw `events.jsonl` retain stage attribution and final
retention; each query also keeps `lean.log`, `residual.txt`, and invocation settings.
Candidate-source statistics and scraping/PA/certification subtimes remain in
`lean.log` as `FIX_SCRAPE` and `FIX_PHASE` records. Peak recursion depth is not
available and remains null. The measurements do not count unchecked candidates
as coverage.

## Full screening for the later ablation

The expanded screening manifest covers all eligible cyclic/mixed cases: 188 from
the 544 refinement-typechecker CHCs, 34 from the 61 RQ1 CHCs, all 25 Imp programs,
and 1,693 CHC-COMP tasks (1,691 cyclic/mixed plus two with unknown classification).
The 37 acyclic-only CHC-COMP tasks are excluded; duplicate benchmark task identities
are preserved. No outcome filtering takes place before screening.

```sh
python3 evaluation/Scraping/benchmark.py --manifest MANIFEST.json \
  --output evaluation/results/Scraping/screen1940-20261112 \
  --workers 4 --timeout 180 --zap-timeout 60 --fix-timeout 120
```

These separate internal caps cover Zap with preprocessing (60 seconds) and Fix
with all scraping levels, validation, certification and discharge (120 seconds).
A Zap timeout preserves its checkpoint and allows Fix to run. The Fix allowance
is per CHC, shared across all predicate goals; unused Zap time does not extend it.
Imp VC preparation and final kernel measurement remain outside these tactic caps.

`fully_proved_manifest.json` contains every kernel-checked full success.
`fix_proved_manifest.json` additionally requires retained Fix inference, excluding
cases solved without it from the scraping comparison. `selection_summary.json`
gives completed and selected counts by the four corpora. Both manifests are
provisional until their `complete` field is true. Failed and partial trials remain
in the full results; the resulting success-selected suite supports a conditional
scraping ablation, not an overall corpus coverage claim.

`--resume` continues a frozen run; `STOP` in its output directory stops new jobs.
On macOS, launch under `caffeinate -i -s` on AC to prevent idle system sleep.
This does not guarantee operation with the lid closed.

## Fifty-case scraping ablation pilot

Queue the pilot after screening; it starts only after every screening trial has
finished. It runs 50 queries under **Bank, Basic, Standard, Deep, and Auto**: 250
fresh trials. It does not start a full-corpus ablation afterwards.

```sh
caffeinate -is python3 evaluation/Scraping/ablation.py \
  --after evaluation/results/Scraping/screen1940-20261112 \
  --output evaluation/results/Scraping/ablation50-20261112 --workers 2
python3 evaluation/Scraping/ablation.py \
  --output evaluation/results/Scraping/ablation50-20261112 --progress
```

Selection requires a kernel-checked full proof with retained Fix inference in the
screening run. The sample contains 20 CHC-COMP, 15 refinement-typechecker, 8 RQ1,
and 7 Imp queries. Within each corpus, sampling spans successful scraping levels,
source families, and input sizes with deterministic tie-breaking. Selection and
input hashes are frozen before the pilot starts. This deliberately balanced,
success-selected sample is for comparing scraping configurations and validating
the plots; its percentages are not full-corpus coverage estimates.

All configurations use the main `flex` pipeline, the screening run's frozen Lean
build and input definitions, Zap for 60 seconds and Fix for 120 seconds, the same
automation, and no S/E. Bank means `scrape := no`. Auto is measured afresh; its
screening timing is not reused. One trial per query/configuration is sufficient
for this pilot, but does not measure run-to-run variability. Two workers measure
latency under that concurrency, not isolated latency.

These are comparisons of the public configurations. Fixed Standard/Deep may try
source candidates before the full pool; Auto grows its pool incrementally.
Bounded template generation can also change candidate ordering and truncation,
so independently generated pools are not assumed to be nested. All attempts and
limit hits are retained in the data.

The report preserves per-query CSVs, raw JSONL events and logs, plus PDF/PNG plots:

- Inference, head elimination, full proofs, and progress attributable to Fix or Zap.
- Template sources, candidates per predicate, candidate changes at each PA round,
  survivors, visited definitions, rejected templates, and generation limits hit.
- Zap, scraping, candidate construction, synthesis, safety checks, certification,
  discharge, startup, kernel and whole-process time; heartbeats and proof size.
- Internal deadlines, heartbeat failures and outer watchdogs separately, with the
  interrupted phase and last checked checkpoint. Missing data is left empty.
- Process CPU time and peak resident memory where available. Peak recursion depth
  is not instrumented; only its configured limit is available. Solver trace counts
  are observed log counts, not a claim of complete attempted-call accounting.

The pilot plots show outcomes per configuration and query, coverage against time,
candidate growth, and where synthesis and certification spend time. Summary CSVs
include quartiles, median, mean, p90/p95 and maximum; paired speed comparisons use
the same successful queries. Timeouts are displayed explicitly rather than
silently dropped or presented as completed timings.

## Full ablation on screened Fix successes

The completed screening selected **406** CHCs with kernel-checked full proofs and
retained Fix inference. This is the entire eligible success set, not a larger
stratified sample: `--count 0` keeps every case identity.

| Corpus | Selected CHCs |
| --- | ---: |
| Flux regression tests | 95 |
| Flux examples | 57 |
| WaVe | 9 |
| Liquid Fixpoint | 20 |
| CHC-COMP | 192 |
| RQ1 | 18 |
| Imp | 15 |
| **Total** | **406** |

There are 289 cyclic-only and 117 mixed constraints. The denominator is conditional
on screening success; use the full screening results to discuss corpus coverage.
All five configurations run afresh on all 406 cases: **2,030 trials**. No pilot
trials are reused, and no unsuccessful full-run trials are removed afterwards.

```sh
caffeinate -is python3 evaluation/Scraping/ablation.py \
  --after evaluation/results/Scraping/screen1940-20261112 \
  --output evaluation/results/Scraping/ablation406-20261112 \
  --count 0 --workers 1 --fresh-runtime
python3 evaluation/Scraping/ablation.py \
  --output evaluation/results/Scraping/ablation406-20261112 --progress
```

`--prepare-only` freezes the setup before starting any trials; continue with the
same arguments and `--resume`. `--fresh-runtime` freezes the current instrumented
library and harness once. The full run enables additional benchmark-only metrics;
it does not change synthesis, scraping, proof search, or time limits. Input and
runtime hashes are verified before and after the run. Host and power information
is saved at these boundaries.

For the full run, one worker avoids contention between query processes. Builds,
hashing, statistics and plotting happen outside the timed trial window; live
progress reads only saved records. Configuration order rotates deterministically
between cases. The complete raw JSONL and per-case events are saved as each trial
finishes. Detailed CSVs and `ablation.pdf` are generated after the run. One trial
per case/configuration does not estimate repeated-run timing variability.

Additional measurements in the full run:

- `FIX_ORACLE` start/end records survive speculative rollback. They count logical
  synthesis requests and their valid/invalid/unknown outcomes for SMT and native
  fallback; they do not claim to count individual SMT `check-sat` calls. Interrupted
  batches have unknown outcome counts, not zero. Older trace-only counts remain
  explicitly marked as observed and potentially incomplete.
- `input_metrics.json` measures the prepared goal's expression DAG size and depth,
  with named model definitions opaque. Source bytes, generated Lean bytes and
  physical Lean LOC are reported separately; they are not expression complexity.
- Proof-package size/depth include newly generated helper declarations. Kernel
  checking replays those helpers and the final bridge against the pre-trial
  environment. Direct bridge metrics remain separately available. Kernel and
  metric collection time are outside `flex_ms`.
- Safety rejection, inconclusive checks, explicit timeouts, observed heartbeat or
  recursion failures, and generation limits remain distinct. Generated qualifier
  origins describe candidate provenance; they do not identify which rules were
  necessary for the final invariant.

Wall-clock measurements include enabled instrumentation overhead. Peak recursion
depth and aggregate simultaneous memory of Lean plus external solver processes
are not measured; missing fields remain null. Keep the immutable raw results and
the recorded schema/metric versions when producing paper tables.
