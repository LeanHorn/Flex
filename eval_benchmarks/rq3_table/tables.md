# Table 1: Non-trivial VCs and Proof Failures

| Benchmark | Non-trivial VCs | Failures | Success % | Success % (cyclic) | fixpoint-hs time | Lean Time |
|-----------|----------------:|---------:|----------:|-------------------:|----------:|----------:|
| flux-medium | 148 | 16 | 89.2% | 78.3% | — | 9.5m |
| wave | 77 | 3 | 96.1% | 70.0% | — | 4.0m |
| Flux lean-bench | 614 | 21 | 96.6% | 83.8% | — | 18.0m |
| Liquid-fixpoint | 47 | 2 | 95.7% | 100.0% | — | 2.1m |
| **Total** | **886** | **42** | **95.3%** | **82.3%** | **—** | **33.6m** |

# Table 2: Kvar Classification of Non-trivial VCs

| Benchmark | none | acyclic | cyclic | both | Total |
|-----------|-----:|--------:|-------:|-----:|------:|
| flux-medium | 52 | 36 | 16 | 44 | 148 |
| wave | 41 | 26 | 1 | 9 | 77 |
| Flux lean-bench | 352 | 182 | 31 | 49 | 614 |
| Liquid-fixpoint | 22 | 11 | 13 | 1 | 47 |
| **Total** | **467** | **255** | **61** | **103** | **886** |
