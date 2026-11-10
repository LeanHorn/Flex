# CHC benchmark probe

Runs `solveGoal` (Spacer, heads only, `grind` on the residual) on every κ VC of the four CHC
suites in `flex-benchmarks`: `flux_tests`, `flux-medium`, `wave`, and the liquid-fixpoint CHC
queries.

```sh
scripts/chc-bench/list.sh > .lake/chc-bench-list.txt          # "VC ROOT" per line
scripts/chc-bench/run.sh .lake/chc-bench-list.txt .lake/chc-bench/new        # this checkout
scripts/chc-bench/run.sh .lake/chc-bench-list.txt .lake/chc-bench/base ../lean-fixpoint-base
python3 scripts/chc-bench/compare.py .lake/chc-bench/base .lake/chc-bench/new
```

- `flat.py` inlines a VC's project-local imports into one file and appends `probe.lean`
  (extra arguments become `set_option` lines, e.g. `"flex.smt.encodeNonlinear true"`).
- `run.sh` is resumable: logs that already contain a `PROBE` line are skipped. It uses
  `lake lean`, not `lake env lean`, because the cvc5 FFI needs Lake's dynlib setup.
- Probes compile against the Flex build on disk; do not rebuild Flex while a run is in progress.
- For a baseline, use a worktree at the base commit with `.lake/packages` symlinked to this
  checkout's packages.

Outcomes: `closed` (solved, or every residual goal closed by `grind`), `residual` (some residual
goal left), or the failing stage (`prepare`, `exporting`, `solver`, `importing`, ...).
