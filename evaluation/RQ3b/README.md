# RQ3b: coverage on CHC-COMP

RQ3b evaluates the 1,730 CHC-COMP tasks in `flex-benchmarks`, including upstream
duplicates. [RQ3a](../RQ3a/README.md) separately evaluates the 544
refinement-typechecker queries.

The default arms are Spacer on original SMT, Eldarica on original SMT, and S/E
through `flex`. Compare native model availability with checked Flex outcomes:
invariants retained, heads eliminated, and full proof. Native SAT/model output
alone is not a Lean proof.

Use the installation and worker instructions in the RQ3a README. Both parts share
the measurement implementation, budgets, CSV schema and reporting code; their
entry points and result directories are separate.

From a `flex-benchmarks` checkout next to `Flex`:

```sh
# All CHC-COMP tasks; omit --count 0 for a 100-query pilot.
python3 -B ../Flex/evaluation/RQ3b/benchmark.py \
  --benchmarks . --count 0 --workers 1 \
  --output ../Flex/evaluation/results/RQ3b/full

python3 -B ../Flex/evaluation/RQ3b/benchmark.py \
  --output ../Flex/evaluation/results/RQ3b/full --progress

python3 -B ../Flex/evaluation/RQ3b/report.py \
  ../Flex/evaluation/results/RQ3b/full
```

Default limits are 180 s per native solver and 180 s shared by the S/E Flex
pipeline, plus a 120 s process-watchdog allowance for Flex. Spacer can consume
the pipeline budget before Eldarica runs. `--configs se` selects only the Flex
arm and omits native baselines.

Reports include the same quartiles, median, p90/p95, mean and per-query metrics as
RQ3a, plus native model coverage and `discrepancies.csv` for native-SAT queries
whose invariants were not retained through Flex. Results are gitignored.
