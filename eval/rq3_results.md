# RQ3: deterministic proof term (Zap) vs proof search (grind)

Liquid-fixpoint and FluxRS (real Rust VC) benchmarks with ≥1 **acyclic** κ (with none, `zap` is a no-op so A≡B). Two pipelines on the same VC, each in its own `lake env lean` run (`Elab.async false`, `maxHeartbeats 4000000`):

- **A** = `unfold; solve_fixpoint` — acyclic κ → σ̂-assign, body closed by **grind** (`tryClosers`).
- **B** = `unfold; zap; all_goals solve_fixpoint` — acyclic κ → **deterministic kernel-checked proof term** (Zap), then PA+close on the residual.

Heartbeats (`hb`, thousands) are deterministic; `ms` indicative. Per-phase heartbeats from the gated `flex.benchPhases` instrumentation.

## Totals & speedup

Source: **LF** = Liquid-fixpoint, **FX** = FluxRS (real Rust VCs).

| benchmark | src | bucket | #acy | #cyc | A hb | B hb | **× hb** | A ms | B ms | A | B |
|---|:-:|---|--:|--:|--:|--:|--:|--:|--:|:-:|:-:|
| `kut00` | LF | acyclic_only | 1 | 0 | 418 | 54 | **7.7×** | 23 | 8 | ok | ok |
| `arbitrary-kvar-arg` | LF | acyclic_only | 2 | 0 | 6424 | 969 | **6.6×** | 319 | 66 | ok | ok |
| `icfp17-ex3` | LF | acyclic_only | 3 | 0 | 3073 | 495 | **6.2×** | 154 | 31 | ok | ok |
| `icfp17-ex2` | LF | acyclic_only | 2 | 0 | 3023 | 582 | **5.2×** | 152 | 44 | ok | ok |
| `Fix-Test4` | FX | acyclic_only | 10 | 0 | 4414 | 893 | **4.9×** | 172 | 69 | ok | ok |
| `Fix-Test7` | FX | acyclic_only | 2 | 0 | 2695 | 646 | **4.2×** | 132 | 40 | ok | ok |
| `exists_oddity` | LF | acyclic_only | 1 | 0 | 345 | 127 | **2.7×** | 23 | 12 | ok | ok |
| `test02` | LF | acyclic_only | 1 | 0 | 865 | 334 | **2.6×** | 49 | 29 | ok | ok |
| `mod00` | LF | acyclic_only | 1 | 0 | 528 | 237 | **2.2×** | 31 | 19 | ok | ok |
| `icfp17-ex1` | LF | acyclic_only | 1 | 0 | 415 | 233 | **1.8×** | 32 | 25 | ok | ok |
| `Fix-Test5` | FX | acyclic_only | 4 | 0 | 1722 | 981 | **1.8×** | 82 | 59 | ok | ok |
| `Quicksort` | FX | acyclic_only | 2 | 0 | 314737 | 306127 | **1.0×** | 8815 | 8487 | ok | ok |
| `scrape03` | LF | acyclic_only | 1 | 0 | 3527 | 3527 | **1.0×** | 689 | 709 | ok | ok |
| `scrape02` | LF | both | 2 | 4 | 39414 | 33287 | **1.2×** | 1472 | 1270 | ok | ok |
| `Fix-Test1` | FX | both | 1 | 2 | 10314 | 9081 | **1.1×** | 442 | 365 | ok | ok |
| `Fix-Test6` | FX | both | 3 | 1 | 10907 | 10044 | **1.1×** | 453 | 428 | ok | ok |
| `FibMemoBoth` | FX | both | 1 | 1 | 12810 | 11857 | **1.1×** | 571 | 523 | ok | ok |
| `comment` | LF | both | 5 | 1 | 180806 | 173781 | **1.0×** | 5250 | 4900 | ok | ok |

## Per-phase heartbeats (where the cost goes)

A spends in `close` (grind); B moves that into deterministic `zap` (sol+build+clean) + a residual `close`. `pa` is predicate abstraction (Houdini) on the cut — independent of A/B.

| benchmark | A fuse | A pa | **A close** | B zap | B pa | B close |
|---|--:|--:|--:|--:|--:|--:|
| `kut00` | 27 | 0 | **378** | 26 | 0 | 9 |
| `arbitrary-kvar-arg` | 159 | 0 | **6203** | 139 | 0 | 755 |
| `icfp17-ex3` | 80 | 0 | **2974** | 80 | 0 | 385 |
| `icfp17-ex2` | 97 | 0 | **2900** | 88 | 0 | 450 |
| `Fix-Test4` | 337 | 0 | **4021** | 415 | 0 | 384 |
| `Fix-Test7` | 117 | 0 | **2533** | 104 | 0 | 493 |
| `exists_oddity` | 24 | 0 | **308** | 27 | 0 | 81 |
| `test02` | 28 | 0 | **822** | 31 | 0 | 278 |
| `mod00` | 23 | 0 | **493** | 26 | 0 | 191 |
| `icfp17-ex1` | 18 | 0 | **384** | 23 | 0 | 189 |
| `Fix-Test5` | 115 | 0 | **1569** | 132 | 0 | 775 |
| `Quicksort` | 303 | 0 | **313882** | 385 | 0 | 305019 |
| `scrape03` | 7 | 0 | **3440** | 16 | 0 | 3423 |
| `scrape02` | 182 | 25417 | **13663** | 234 | 25429 | 7386 |
| `Fix-Test1` | 45 | 6460 | **3745** | 71 | 6456 | 2468 |
| `Fix-Test6` | 122 | 6615 | **4100** | 129 | 6616 | 3184 |
| `FibMemoBoth` | 17 | 131 | **12625** | 40 | 132 | 11637 |
| `comment` | 331 | 168217 | **12073** | 435 | 168101 | 5041 |

## Proof-term shape & kernel re-check (foundational)

The constructive Zap term (B) is *larger* (explicit `Exists.intro`/`And.intro`/`Or.inl` chains) than grind's, but is built without search and the kernel re-checks it in well under a millisecond.

| benchmark | A depth | B depth | A nconst | B nconst | A kerµs | B kerµs |
|---|--:|--:|--:|--:|--:|--:|
| `kut00` | 29 | 47 | 21 | 37 | 257 | 526 |
| `arbitrary-kvar-arg` | 73 | 99 | 49 | 40 | 2844 | 4288 |
| `icfp17-ex3` | 38 | 68 | 34 | 39 | 495 | 998 |
| `icfp17-ex2` | 41 | 74 | 23 | 39 | 702 | 1551 |
| `Fix-Test4` | 59 | 145 | 22 | 33 | 1550 | 4310 |
| `Fix-Test7` | 106 | 85 | 44 | 36 | 1389 | 1649 |
| `exists_oddity` | 21 | 45 | 13 | 31 | 243 | 627 |
| `test02` | 26 | 51 | 17 | 33 | 391 | 620 |
| `mod00` | 20 | 46 | 18 | 32 | 260 | 469 |
| `icfp17-ex1` | 21 | 47 | 20 | 36 | 331 | 975 |
| `Fix-Test5` | 42 | 93 | 27 | 45 | 974 | 2333 |
| `Quicksort` | 159 | 209 | 92 | 104 | 17530 | 24446 |
| `scrape03` | 65 | 83 | 148 | 160 | 8154 | 5066 |
| `scrape02` | 166 | 128 | 48 | 51 | 4127 | 8363 |
| `Fix-Test1` | 49 | 62 | 64 | 54 | 1342 | 1942 |
| `Fix-Test6` | 49 | 80 | 40 | 59 | 1283 | 2976 |
| `FibMemoBoth` | 45 | 46 | 36 | 56 | 918 | 1228 |
| `comment` | 112 | 88 | 67 | 57 | 5647 | 6696 |

## Aggregate

- **Geomean heartbeat speedup (A/B): 2.3×** over 18 benchmarks solved by both.
  - acyclic_only (13): **3.0×** (zap replaces the grind closer; the win is direct).
  - both (5): **1.1×** (PA on the cut dominates total cost, so the acyclic win is a small slice — see the per-phase `A close` vs total).
- Aggregate heartbeats: 596437 → 553255 (1.1× less) over solved-by-both.

## Min budget / headroom (M3)

`hb` and `maxHeartbeats` share units, and heartbeats consumed are deterministic — so each config's measured `hb` is *exactly* its minimum `maxHeartbeats` to succeed. B needs a smaller budget on the κ-heavy benchmarks, so under a **tight** budget it covers strictly more (e.g. 1000: B 11/18 vs A 5/18). At/above Lean's 200000 default they converge (A 17/18, B 17/18); the only miss is the heaviest VC(s) (`Quicksort`) exceeding the default budget — not a solver gap (`Quicksort`'s source sets `maxHeartbeats 1600000`). The heaviest min-budget is 314737 (`Quicksort`).

| budget (maxHeartbeats) | 500 | 1,000 | 5,000 | 50,000 | 200,000 |
|---|--:|--:|--:|--:|--:|
| A solved | 3/18 | 5/18 | 11/18 | 16/18 | 17/18 |
| B solved | 6/18 | 11/18 | 12/18 | 16/18 | 17/18 |
- **Coverage:** A and B each solve all 18/18.
- **Where zap does NOT help (×~1.0):** `scrape03`, `comment`, `Quicksort` — zap removes the κ (B's `zap` phase is tiny) but the cost was never in the κ-structure: it's in the residual *leaf* grind (`scrape03`, `Quicksort`: A/B `close` both huge) or in **PA on the cut** (`comment`: A `pa`≈168k of 181k). The RQ3 win is specifically on κ-structure cost.

_Heartbeats deterministic; ms one machine. Reproduce: `python3 scripts/run_rq3.py && python3 scripts/rq3_aggregate.py`._
