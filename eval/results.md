# Evaluation: `solve_fixpoint` vs `zap` + `solve_fixpoint`

Comparison over every example in `demo/basic.lean`, measuring heartbeats
(deterministic, `IO.getNumHeartbeats`/1000) and wall-clock ms
(`IO.monoMsNow`). Harness: `eval/BasicCompare.lean` (run with
`set_option Elab.async false` so tactic work is measured synchronously).

- **A** = `unfold; solve_fixpoint` — the integrated solver (old branch-stripping
  scope zap + predicate abstraction + grind/aesop discharge).
- **B** = `unfold; zap; all_goals solve_fixpoint` — new LCA-scoped `zap`
  eliminates the acyclic κ structurally (certifying proof term), then
  `solve_fixpoint` discharges the (clean) residual.

| example | A hb | B hb | hb ×faster | A ms | B ms | ms ×faster | A | B |
|---|--:|--:|--:|--:|--:|--:|:-:|:-:|
| `ex1` | 416 | 158 | 2.6× | 21 | 9 | 2.3× | ok | ok |
| `ex2` | 1093 | 309 | 3.5× | 40 | 12 | 3.3× | ok | ok |
| `ex3` | 3068 | 385 | 8.0× | 124 | 15 | 8.3× | ok | ok |
| `ex4` | 1440 | 316 | 4.6× | 52 | 12 | 4.3× | ok | ok |
| `ex5` | 1383 | 311 | 4.4× | 50 | 12 | 4.2× | ok | ok |
| `ex6` | 689 | 303 | 2.3× | 24 | 12 | 2.0× | ok | ok |
| `ex7` | 1023 | 236 | 4.3× | 38 | 9 | 4.2× | ok | ok |
| `ex8` | 446 | 182 | 2.5× | 19 | 7 | 2.7× | ok | ok |
| `ex9` | 4045 | 519 | 7.8× | 129 | 19 | 6.8× | ok | ok |
| `ex10` | 1551 | 286 | 5.4× | 57 | 11 | 5.2× | ok | ok |
| `ex11` | 4320 | 568 | 7.6× | 151 | 21 | 7.2× | ok | ok |
| `ex12` | 6452 | 747 | 8.6× | 217 | 29 | 7.5× | ok | ok |
| `ex13` | 2272 | 491 | 4.6× | 82 | 20 | 4.1× | ok | ok |
| `ex14` | 6705 | 912 | 7.4× | 231 | 37 | 6.2× | ok | ok |
| `ex_nat` | 505 | 201 | 2.5× | 21 | 8 | 2.6× | ok | ok |
| `ex_bool` | 348 | 131 | 2.7× | 13 | 5 | 2.6× | ok | ok |
| `ex_pair` | 797 | 359 | 2.2× | 32 | 13 | 2.5× | ok | ok |
| `ex_prod` | 862 | 403 | 2.1× | 33 | 15 | 2.2× | ok | ok |
| `ex_userfn` | 496 | 360 | 1.4× | 23 | 15 | 1.5× | ok | ok |
| `ex_stress` | 38072 | 2569 | 14.8× | 1200 | 101 | 11.9× | ok | ok |
| **TOTAL** | **75983** | **9746** | **7.8×** | **2557** | **382** | **6.7×** | | |

- **Geometric-mean speedup (heartbeats): 4.1×** across 20 examples.
- Aggregate: 75983 → 9746 heartbeats (7.8× less), 2557 → 382 ms (6.7× less).
- Every example is faster with `zap` first; the margin grows with κ-count /
  nesting depth (`ex_stress`, 5 κ: 14.8×; `ex12`/`ex14`, 4 κ: ~7–9×).

## Reading

`solve_fixpoint` leans on grind/aesop search to discharge clauses; the LCA-scoped
`zap` replaces that search with a deterministic, kernel-checked structural
elimination of the acyclic κ, so the downstream grind has little or nothing left
to do. The clean scope (prefix binders/guards folded into κ-params instead of extra
`∃`/conjuncts) is what keeps the residual small enough for grind to close cheaply.

_Numbers are from one run on this machine; heartbeats are deterministic, ms are
indicative. Reproduce: `lake env lean eval/BasicCompare.lean`._
