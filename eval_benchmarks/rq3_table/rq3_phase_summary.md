# RQ3: Proof-Time Phase Breakdown

Where Lean's proof time goes for the `zap ; simp ; solve` pipeline, across four benchmark
suites. **All numbers below are for non-trivial, passing constraints only** — 1,041 of 1,924
generated VCs are trivial (`True`) and 42 failed; both are excluded entirely, leaving 841
VCs. Cells are mean heartbeats/1000 per VC (mean wall-clock ms per VC) — heartbeats are
deterministic, ms is indicative (one machine).

Buckets: **zap** (acyclic-κ elimination) · **simp** (cleanup) · **PA** (predicate
abstraction / fixpoint on cyclic κ) · **discharge** (closing the residual VC).

## Mean per VC — overall (all suites combined)

| κ-structure | zap | simp | PA | discharge | Total |
|---|--:|--:|--:|--:|--:|
| All | 76.8 (18.9ms) | 1,248.3 (97.6ms) | 24,320.0 (1,737.6ms) | 7,692.0 (669.3ms) | 33,337.0 (2,523.3ms) |
| No cyclic κ | 52.0 (15.1ms) | 541.5 (43.4ms) | 0.0 (0.0ms) | 258.0 (31.7ms) | 851.4 (90.2ms) |
| Has cyclic κ | 206.5 (38.6ms) | 4,944.6 (381.2ms) | 151,504.5 (10,824.4ms) | 46,569.2 (4,003.6ms) | 203,224.8 (15,247.9ms) |

## Mean per VC — both cyclic κs and acyclic κs

| Benchmark | zap | simp | PA | discharge | Total |
|---|--:|--:|--:|--:|--:|
| wave | 183.0 (44.3ms) | 1,546.7 (127.8ms) | 27,561.0 (2,442.8ms) | 1,053.1 (132.6ms) | 30,343.8 (2,747.6ms) |
| flux-medium | 122.2 (24.0ms) | 3,637.4 (282.0ms) | 67,679.2 (4,341.1ms) | 32,592.5 (2,579.6ms) | 104,031.3 (7,226.7ms) |
| Flux lean-bench | 57.2 (15.6ms) | 771.5 (60.0ms) | 15,618.5 (1,173.0ms) | 3,414.8 (349.8ms) | 19,862.0 (1,598.5ms) |
| Liquid-fixpoint | 26.0 (4.2ms) | 0.0 (0.0ms) | 5,888.9 (342.6ms) | 1,647.3 (137.3ms) | 7,562.2 (484.1ms) |
| **Total** | **76.8 (18.9ms)** | **1,248.3 (97.6ms)** | **24,320.0 (1,737.6ms)** | **7,692.0 (669.3ms)** | **33,337.0 (2,523.3ms)** |

## Mean per VC — no cyclic κ

| Benchmark | zap | simp | PA | discharge | Total |
|---|--:|--:|--:|--:|--:|
| wave | 149.1 (35.5ms) | 1,214.7 (98.9ms) | 0.0 (0.0ms) | 643.8 (77.9ms) | 2,007.7 (212.3ms) |
| flux-medium | 61.2 (15.9ms) | 1,331.0 (105.9ms) | 0.0 (0.0ms) | 274.3 (32.3ms) | 1,666.5 (154.0ms) |
| Flux lean-bench | 40.0 (13.0ms) | 359.0 (28.7ms) | 0.0 (0.0ms) | 171.0 (22.1ms) | 569.9 (63.9ms) |
| Liquid-fixpoint | 19.1 (3.7ms) | 0.0 (0.0ms) | 0.0 (0.0ms) | 847.6 (91.3ms) | 866.8 (95.0ms) |
| **Total** | **52.0 (15.1ms)** | **541.5 (43.4ms)** | **0.0 (0.0ms)** | **258.0 (31.7ms)** | **851.4 (90.2ms)** |

## Mean per VC — has cyclic κ

| Benchmark | zap | simp | PA | discharge | Total |
|---|--:|--:|--:|--:|--:|
| wave | 507.7 (128.9ms) | 4,724.6 (405.1ms) | 291,359.1 (25,824.0ms) | 4,970.1 (655.9ms) | 301,561.6 (27,013.9ms) |
| flux-medium | 232.3 (38.8ms) | 7,808.6 (600.5ms) | 190,077.9 (12,192.1ms) | 91,040.5 (7,186.4ms) | 289,159.3 (20,017.8ms) |
| Flux lean-bench | 191.5 (36.0ms) | 3,991.6 (304.6ms) | 137,536.3 (10,329.6ms) | 28,735.8 (2,907.3ms) | 170,455.3 (13,577.4ms) |
| Liquid-fixpoint | 41.2 (5.4ms) | 0.0 (0.0ms) | 18,928.6 (1,101.1ms) | 3,417.9 (239.2ms) | 22,387.7 (1,345.8ms) |
| **Total** | **206.5 (38.6ms)** | **4,944.6 (381.2ms)** | **151,504.5 (10,824.4ms)** | **46,569.2 (4,003.6ms)** | **203,224.8 (15,247.9ms)** |
