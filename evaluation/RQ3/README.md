# RQ3: invariant inference and proof coverage

Run this harness from a `flex-benchmarks` checkout, using a sibling Flex checkout.
It reads published inputs; it does not use benchmark proofs or modify the corpus.

| Study | Inputs | Configurations |
| --- | --- | --- |
| RQ3a | Flux tests, Flux-medium, Wave, LiquidHaskell | Zap + Fix; S/E only; full Flex |
| RQ3b | CHC-COMP, recorded SAT arithmetic inputs | Original SMT through Spacer; original SMT through Eldarica; S/E only through Flex |

S/E means Spacer followed by Eldarica if needed. All Lean configurations use the
main `flex` implementation and identical residual discharge. Only True/False
preprocessing is enabled; nesting and postprocessing are off. Fix uses incremental
Bank → Basic → Standard → Deep scraping. The full pipeline tries Zap, Fix, then S/E;
it may exhaust its shared budget before reaching later phases.

## Run

Requirements: the pinned Lean toolchain, Flex dependencies, Z3, Eldarica (including
Java), Python 3.9+, and `matplotlib` for figures. Solver executables must be on PATH
or supplied with `--z3` and `--eldarica`. Setup builds imported modules once.

From `flex-benchmarks`:

```sh
python3 -B ../Flex/evaluation/RQ3/benchmark.py \
  --benchmarks . --output ../Flex/evaluation/RQ3/results/pilot100 --count 100
```

On macOS, prefix that command with `caffeinate -is`. Keep AC power connected and
the lid open: preventing idle sleep does not override lid-close sleep. On a Linux
server, use a persistent terminal/session such as `tmux`.

```sh
# Progress (does not start a run)
python3 -B ../Flex/evaluation/RQ3/benchmark.py \
  --output ../Flex/evaluation/RQ3/results/pilot100 --progress

# Resume: repeat the original command with --resume and identical settings.
# Graceful stop after the current trial:
touch ../Flex/evaluation/RQ3/results/pilot100/STOP
# Remove STOP before resuming.

# Regenerate figures from saved records
python3 -B ../Flex/evaluation/RQ3/report.py ../Flex/evaluation/RQ3/results/pilot100
```

Use `--prepare-only` to build and freeze inputs without timing trials, and
`--count 0` for the full available corpus. Results are gitignored in Flex.

## Selection and budgets

The 100-query RQ3a pilot allocates 30 Flux tests, 12 Flux-medium, 8 Wave and 50
LiquidHaskell queries. RQ3b selects 100 distinct SMT inputs across available source
suites. Within each allocation, selection rotates through families and input-size
quartiles with seed `20261104`; it does not consult previous outcomes. The published
320-query LiquidHaskell collection is itself a curated subset, not the complete
LiquidHaskell corpus. Classification into acyclic/mixed/cyclic occurs after
selection and does not exclude failures. Source preparation failures remain in the
denominator. In particular, an unimplemented source specification is not admitted.

| Limit | Default |
| --- | ---: |
| Shared internal time: Zap + Fix or S/E only | 180 s |
| Shared internal time: Zap + Fix + S/E | 360 s |
| Individual S/E solver call / native baseline | 180 s, capped by remaining Flex time inside Flex |
| Flex phase heartbeats | 4,000,000 |
| Proof automation heartbeats | 40,000 |
| Recursion limit | 16,384 |
| Outer Lean process watchdog | Internal budget + 120 s (300 s / 480 s), plus bounded solver cleanup |

These are whole-pipeline budgets, including discharge. Fix's synthesis limit is
set to the pipeline budget; all phases remain subject to the shared deadline.
Spacer and Eldarica share that deadline, so a long Spacer attempt can leave little
time for Eldarica. The outer watchdog allows elaboration and kernel checking time.
Override the internal budgets with `--flex-timeout` and `--combined-timeout`.
Each run records the effective budgets per configuration in `settings.json`.

Trials run serially, once each, with configuration order rotated between inputs.
Builds, corpus extraction and structural classification are outside timings.
`flex_ms` measures the tactic; `wall_ms` includes Lean startup, source elaboration,
instrumentation and the independent kernel check. Native solver time includes
process startup. The two native 180-second runs are separate reference results.
The combined Flex configuration receives twice the internal budget of either
component configuration; compare its coverage with that additional time explicit.
Original SMT
assertions are preserved; response/process-control commands are replaced with a
model request. Both original and sent SMT are available for comparison.

## Measurements

- **All predicates instantiated:** no predicate existential remains in the final
  checkpoint, and its proof back to the original goal passes the kernel.
- **All heads eliminated:** the above, with no tracked head obligations remaining.
  An unknown head count is not counted as success.
- **Fully proved:** no residual goals, with a kernel-checked proof of the input.
- **Partial progress:** some predicates removed, or all instantiated with residual
  obligations. Raw solver models and imported candidates are reported separately;
  a discarded attempt never counts as retained progress.

The independent check abstracts the actual residual goals in memory and checks
`residuals → original`; it does not precompute or hardcode residuals for tactics.
Proofs containing admissions or nonstandard axioms are rejected. Only `propext`,
`Classical.choice` and `Quot.sound` are accepted.

Each query records phase wall times and heartbeats, source size, SCC classification,
predicate counts, solver output, exported SMT, imported invariants, residual goals,
kernel time and proof size. Proof depth is Lean's `approxDepth`; peak recursion
depth is unavailable and is reported as null, not as the configured limit.

## Outputs

| File | Contents |
| --- | --- |
| `selection.json`, `settings.json`, `metadata.json` | Inputs, hashes, settings, revisions, solver versions |
| `source/`, `compiled/` | Frozen harness/source and Flex build artifacts |
| `results.jsonl` | Append-only per-trial records, flushed after every trial |
| `results.csv`, `phases.csv`, `summary.json` | Analysis tables and aggregate counts |
| `classification.json` | Predicate graph classification, outside timing |
| `discrepancies.csv` | Native SAT cases without all predicates retained by Flex |
| `runs/`, `native/` | Complete per-query logs and solver artifacts |
| `pilot-report.pdf`, `figures/` | Coverage, timing and size/progress plots |

Figures refresh every 30 trials and at completion. Unfinished reports are labelled
provisional. The runner freezes the selection and compiled Flex artifacts: fixes
made during a run belong in a separately named run, not in mixed results.
