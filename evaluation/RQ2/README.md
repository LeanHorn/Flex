# RQ2: Zap reduction efficiency

Compare **Zap**, **Zap_grind**, and **Zap_aesop** on the same original CHCs.
All use Zap's strongest-solution computation. Only the proof of each eliminated
predicate's head changes: constructive proof terms, default `grind`, or default
`aesop`. There is no fallback between variants.

## Configuration

```lean
flex (backends := []) (config := {
  zapCertificate := .constructive  -- .grind or .aesop
  preprocess := true
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
original statement; no residual is cached or reused.

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

# Flux or LiquidHaskell statement manifests (same format as benchmark_flex.py).
python3 -B evaluation/RQ2/benchmark_rq2.py \
  --manifest /path/to/cases.json \
  --output evaluation/RQ2/results/flux --count 0 --repeats 3

python3 -B evaluation/RQ2/benchmark_rq2.py --output evaluation/RQ2/results/pilot100 --progress
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
inlined. Statement-manifest cases are classified one per file, since flattened
cases share declaration names.

```sh
python3 -B evaluation/RQ2/make_manifests.py flux PROJECT... --output DIR
python3 -B evaluation/RQ2/make_manifests.py liquidhaskell path/to/liquid-haskell --output DIR
```

Timing trials run **serially**, in a recorded seeded order. Stop competing builds
and evaluations. On macOS, prefix the command with `caffeinate -is` and leave the
lid open. Compilation and module loading happen outside the tactic timer.
Classification uses two workers; it finishes before timing begins.

`--classify-only` prepares the selection and frozen build without timing trials.
`--run-only` resumes those exact settings and inputs. Creating `OUTPUT/STOP`
stops between trials; remove it before resuming. Completed trials are preserved.

## Selection and measurements

Only **acyclic-only or mixed graphs with an eliminable predicate**, after common
preprocessing, qualify. Purely cyclic graphs are excluded even when cutting a
cycle would leave removable vertices. As in `flex`, classification descends
positive `∀` and `∧` to every predicate (∃) goal and sums over them. Graph membership and Zap's elimination/cut
partition are recorded separately. Source duplicates are removed before selection.
The 100-case pilot balances acyclic/mixed cases and spreads them across suites,
using a fixed seed and **no success-based filtering**. `--count 0` uses every
eligible case. Classification errors stay in the inventory.

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
| Proof expression depth | `depth` (exact); `approx_depth` also retained |
| Distinct proof constants | `constants` |
| Kernel recheck time (µs) | `kernel_us` |

The reduction timer covers the Zap phase. Preprocessing, Flex bookkeeping,
certificate assembly for measurement, and kernel rechecking are outside it;
`flex_ms` records the complete `flex` invocation separately. All variants receive
200,000 heartbeats for the Zap phase, a 60-second shared internal deadline, and
a 120-second process safety limit. The recursion limit is 4096. Default tactic
options are otherwise unchanged. These budgets are recorded and configurable.

`summary.json` contains arithmetic success-only means for Table 2, geometric
means for proof metrics, and paired ratios on jointly reduced queries. Compare
coverage on the entire fixed selection; never replace failed cases. For repeated
runs, raw trial counts are explicit—do not label them as distinct CHC counts.

## Outputs

- `selection.json`: exact inputs, hashes, classification, and sampling rule.
- `results.csv` / `results.jsonl`: per-query, per-variant, per-repeat measurements.
- `summary.json`: coverage, means, and paired ratios.
- `runs/`: original Lean statements plus instrumentation, with raw logs.
- `source/`, `compiled/`, `settings.json`: frozen implementation, build, and limits.

The Lean instrument is `evaluation/RQ2/RQ2.lean`; orchestration is
`evaluation/RQ2/benchmark_rq2.py`. Results are gitignored.
