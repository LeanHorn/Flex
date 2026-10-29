# RQ1 invariant-synthesis baseline

The local `flex-benchmarks` corpus contains 131 case-study VCs excluding Wave
and `flux-medium`. This runner selects only the **61 with unknown predicates**:
27 acyclic-only, 18 cyclic-only, and 16 mixed. The 70 κ-free VCs are inventoried
but not compiled or evaluated. Classification is a generated-source dependency
analysis; the Lean harness independently counts remaining predicate binders.

The primary progress criterion is **retained predicate instantiation**, even
when head obligations remain for manual proof. Head elimination and complete
automatic proof are separate measurements. Two independent tracks use current Flex:

- **Zap + Fix (Deep)**: standard bank, definition/goal scraping,
  batched SMT synthesis, and checked Lean certification. This is one fixed
  scraping mode, not a portfolio of modes.
- **Zap + Spacer/Eldarica**: Spacer first; Eldarica retries the same post-Zap
  goal if predicate heads have not all been certified.

Head certification uses Flex's shared reconstructed-SMT/native automation.
Residual discharge is disabled unless `--discharge` is passed. Defaults:
180 seconds per case/track, 60 seconds for PA preparation/synthesis checks,
60 seconds per CHC solver, two million heartbeats per phase, recursion 16384.
The hard process deadline includes certification; PA checks are cooperative.
One repetition runs serially. Lean timings exclude imports; process wall time
and startup are recorded separately. Solver startup remains included.

```sh
caffeinate -i python3 scripts/benchmark_rq1.py \
  --output evaluation/RQ1/results/baseline-YYYYMMDD
```

Use `--source PATH` for another `flex-benchmarks` checkout. `--cases suite/Name`
restricts a diagnostic run; `--prepare-only` checks imports without synthesis.
Every output directory must be fresh. `--compare OLD_RUN` compares only the
selected cases and variants against a complete saved run. Their statements,
specification dependencies and budgets must match; gained/lost proofs and
synthesis cases are written to `comparison.json`. No baseline is rerun.
`--reuse-completed OLD_RUN` can continue an interrupted run without repeating
checked cases: specification dependencies, Flex/harness code, solver binaries
and budgets must match. Reused rows retain their provenance; startup timings
are left unavailable. Failed or timed-out attempts are retried.

The runner copies only VC statements and their specification dependencies into
isolated workspaces. It imports no `User/Proof` files, per-VC qualifiers, or
handwritten witnesses, and rejects admissions/axioms. Required generic array
lemmas already imported by the specification remain available. No source
project or Flex dependency pin is changed.

`progress.json` shows the active case. `results.csv`, `results.jsonl`, and
`summary.json` contain outcomes and synthesis counts. Case directories retain
phase events, residuals, proof terms, solver candidates, and diagnostics.
`metadata.json`, `selection.json`, and workspace manifests record code, source,
dependency, tool and budget provenance. Generated data stays gitignored.

Count interpretation:

- Zap receives credit only when predicate binders actually disappear.
- Fix receives credit only after it commits and the resulting proof/bridge
  passes kernel checking; reaching a PA fixed point alone earns no credit.
- S/E imports and head certification are separate measurements. The certificate
  records remaining heads even when they are embedded in one structured VC;
  a resource-limit fallback reports this count as unknown.
- `instantiation_complete` means all unknown predicates have retained witnesses
  and a checked bridge preserves the remaining obligations. This is useful
  synthesis progress, even if the candidates' head obligations remain unproved.
- `elimination_complete` means all predicate witnesses are instantiated and
  their heads certified, with a kernel-checked bridge to the residual VC.
  `synthesis_progress` also credits partial predicate instantiation.
- `proved` additionally means a checked proof of the complete original VC.
  Remaining goals are saved for manual proof. Preparation failures and timeouts
  remain visible and in the denominator.

The earlier 46/131 and 8/34 figures describe existing proof scripts, not results
of this automatic track. PR1 measures a new reproducible baseline; replaying
handwritten proofs or supplying their qualifiers is a separate experiment.
Current Fix rolls back if head certification fails; S/E retains candidates
with explicit obligations. The baseline records that behavioral difference.

The [S/E design notes](se-plan.txt) include a motivating prefix-invariant example
and distinguish automatic synthesis from experiments requiring bespoke lemmas.
