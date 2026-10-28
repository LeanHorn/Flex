#!/usr/bin/env python3
"""Aggregate RQ3 results (eval/rq3_results.json) into a Markdown report.

Computes per-benchmark totals + per-phase locus, geometric-mean heartbeat
speedup overall and per bucket (acyclic_only vs both), coverage, and the
proof-term shape / kernel-time characterization. Writes eval/rq3_results.md.

Usage: python3 scripts/rq3_aggregate.py [eval/rq3_results.json]
"""

from __future__ import annotations

import json
import math
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def geomean(xs: list[float]) -> float:
    xs = [x for x in xs if x and x > 0]
    return math.exp(sum(math.log(x) for x in xs) / len(xs)) if xs else float("nan")


def ph(d: dict, key: str):
    phases = d.get("phases", {})
    if key in phases:
        return phases[key]
    # Read phase labels recorded by earlier evaluations.
    if key.startswith("zap:"):
        return phases.get("fusion:" + key[4:], 0)
    return 0


def zap_total(B: dict) -> int:
    return sum(ph(B, f"zap:{p}") for p in ("sol", "build", "clean"))


def main() -> int:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else REPO / "eval" / "rq3_results.json"
    data = json.loads(path.read_text())

    rows = []
    for bench, cfgs in data.items():
        A, B = cfgs.get("A", {}), cfgs.get("B", {})
        nac, ncy = A.get("n_acyclic", 0), A.get("n_cyclic", 0)
        bucket = "both" if ncy > 0 else "acyclic_only"
        both_ok = A.get("status") == "ok" and B.get("status") == "ok"
        spd = (A["hb"] / B["hb"]) if both_ok and B.get("hb") else None
        grp = "FX" if cfgs.get("group") == "FluxRS" else "LF"
        rows.append(dict(bench=bench, grp=grp, nac=nac, ncy=ncy, bucket=bucket,
                         A=A, B=B, both_ok=both_ok, spd=spd))
    rows.sort(key=lambda r: (r["bucket"], -(r["spd"] or 0)))

    out = []
    W = out.append
    W("# RQ3: deterministic proof term (Zap) vs proof search (grind)\n")
    W("Liquid-fixpoint and FluxRS (real Rust VC) benchmarks with ≥1 **acyclic** κ "
      "(with none, `zap` is a no-op so A≡B). Two pipelines on the same VC, each in "
      "its own `lake env lean` run (`Elab.async false`, `maxHeartbeats 4000000`):\n")
    W("- **A** = `unfold; solve_fixpoint` — acyclic κ → σ̂-assign, body closed by "
      "**grind** (`tryClosers`).")
    W("- **B** = `unfold; zap; all_goals solve_fixpoint` — acyclic κ → "
      "**deterministic kernel-checked proof term** (Zap), then PA+close on the residual.\n")
    W("Heartbeats (`hb`, thousands) are deterministic; `ms` indicative. Per-phase "
      "heartbeats from the gated `flex.benchPhases` instrumentation.\n")

    # ── headline table ────────────────────────────────────────────────────
    W("## Totals & speedup\n")
    W("Source: **LF** = Liquid-fixpoint, **FX** = FluxRS (real Rust VCs).\n")
    W("| benchmark | src | bucket | #acy | #cyc | A hb | B hb | **× hb** | A ms | B ms | A | B |")
    W("|---|:-:|---|--:|--:|--:|--:|--:|--:|--:|:-:|:-:|")
    for r in rows:
        A, B = r["A"], r["B"]
        spd = f"**{r['spd']:.1f}×**" if r["spd"] else "—"
        W(f"| `{r['bench']}` | {r['grp']} | {r['bucket']} | {r['nac']} | {r['ncy']} | "
          f"{A.get('hb','—')} | {B.get('hb','—')} | {spd} | {A.get('ms','—')} | "
          f"{B.get('ms','—')} | {A.get('status','?')} | {B.get('status','?')} |")

    # ── per-phase locus ───────────────────────────────────────────────────
    W("\n## Per-phase heartbeats (where the cost goes)\n")
    W("A spends in `close` (grind); B moves that into deterministic `zap` "
      "(sol+build+clean) + a residual `close`. `pa` is predicate abstraction "
      "(Houdini) on the cut — independent of A/B.\n")
    W("| benchmark | A fuse | A pa | **A close** | B zap | B pa | B close |")
    W("|---|--:|--:|--:|--:|--:|--:|")
    for r in rows:
        A, B = r["A"], r["B"]
        W(f"| `{r['bench']}` | {ph(A,'solve_fixpoint:fuse')} | "
          f"{ph(A,'solve_fixpoint:pa')} | **{ph(A,'solve_fixpoint:close')}** | "
          f"{zap_total(B)} | {ph(B,'solve_fixpoint:pa')} | "
          f"{ph(B,'solve_fixpoint:close')} |")

    # ── proof-term shape / kernel ─────────────────────────────────────────
    W("\n## Proof-term shape & kernel re-check (foundational)\n")
    W("The constructive Zap term (B) is *larger* (explicit `Exists.intro`/`And.intro`/"
      "`Or.inl` chains) than grind's, but is built without search and the kernel "
      "re-checks it in well under a millisecond.\n")
    W("| benchmark | A depth | B depth | A nconst | B nconst | A kerµs | B kerµs |")
    W("|---|--:|--:|--:|--:|--:|--:|")
    for r in rows:
        A, B = r["A"], r["B"]
        W(f"| `{r['bench']}` | {A.get('depth','—')} | {B.get('depth','—')} | "
          f"{A.get('nconst','—')} | {B.get('nconst','—')} | {A.get('kerus','—')} | "
          f"{B.get('kerus','—')} |")

    # ── aggregates ────────────────────────────────────────────────────────
    ok = [r for r in rows if r["both_ok"]]
    acy = [r for r in ok if r["bucket"] == "acyclic_only"]
    bot = [r for r in ok if r["bucket"] == "both"]
    n_total = len(rows)
    n_bfail = sum(1 for r in rows if r["B"].get("status") != "ok")
    W("\n## Aggregate\n")
    W(f"- **Geomean heartbeat speedup (A/B): {geomean([r['spd'] for r in ok]):.1f}×** "
      f"over {len(ok)} benchmarks solved by both.")
    if acy:
        W(f"  - acyclic_only ({len(acy)}): **{geomean([r['spd'] for r in acy]):.1f}×** "
          f"(zap replaces the grind closer; the win is direct).")
    if bot:
        W(f"  - both ({len(bot)}): **{geomean([r['spd'] for r in bot]):.1f}×** "
          f"(PA on the cut dominates total cost, so the acyclic win is a small slice "
          f"— see the per-phase `A close` vs total).")
    a_sum = sum(r["A"]["hb"] for r in ok)
    b_sum = sum(r["B"]["hb"] for r in ok)
    W(f"- Aggregate heartbeats: {a_sum} → {b_sum} ({a_sum/b_sum:.1f}× less) over solved-by-both.")

    # ── min budget / headroom (M3) ────────────────────────────────────────
    # `hb` and `maxHeartbeats` share units (raw/1000); heartbeats consumed are
    # deterministic, so measured `hb` IS the minimum maxHeartbeats-to-succeed.
    budgets = [500, 1000, 5000, 50000, 200000]
    def covered(cfg: str, bud: int) -> int:
        return sum(1 for r in rows
                   if r[cfg].get("status") == "ok" and (r[cfg].get("hb") or 1e18) <= bud)
    maxmin = max((r[c].get("hb") or 0 for r in rows for c in ("A", "B")), default=0)
    maxbench = next((r["bench"] for r in rows
                     if (r["A"].get("hb") or 0) == maxmin or (r["B"].get("hb") or 0) == maxmin), "?")
    overdef = sorted({r["bench"] for r in rows
                      if (r["A"].get("hb") or 0) > 200000 or (r["B"].get("hb") or 0) > 200000})
    defA, defB = covered("A", 200000), covered("B", 200000)
    W("\n## Min budget / headroom (M3)\n")
    W("`hb` and `maxHeartbeats` share units, and heartbeats consumed are "
      "deterministic — so each config's measured `hb` is *exactly* its minimum "
      "`maxHeartbeats` to succeed. B needs a smaller budget on the κ-heavy "
      "benchmarks, so under a **tight** budget it covers strictly more (e.g. 1000: "
      f"B {covered('B',1000)}/{n_total} vs A {covered('A',1000)}/{n_total}). At/above "
      f"Lean's 200000 default they converge (A {defA}/{n_total}, B {defB}/{n_total}); "
      f"the only miss is the heaviest VC(s) "
      f"({', '.join('`' + b + '`' for b in overdef)}) exceeding the default budget — "
      "not a solver gap (`Quicksort`'s source sets `maxHeartbeats 1600000`). The "
      f"heaviest min-budget is {maxmin} (`{maxbench}`).\n")
    W("| budget (maxHeartbeats) | " + " | ".join(f"{b:,}" for b in budgets) + " |")
    W("|---|" + "|".join("--:" for _ in budgets) + "|")
    W("| A solved | " + " | ".join(f"{covered('A', b)}/{n_total}" for b in budgets) + " |")
    W("| B solved | " + " | ".join(f"{covered('B', b)}/{n_total}" for b in budgets) + " |")
    bfails = [r["bench"] for r in rows if r["B"].get("status") != "ok"]
    if bfails:
        W(f"- **Coverage:** B solves {n_total - n_bfail}/{n_total}; the "
          f"deterministic-proof path has robustness gaps grind does not: "
          f"{', '.join('`' + b + '`' for b in bfails)}.")
    else:
        W(f"- **Coverage:** A and B each solve all {n_total}/{n_total}.")
    W("- **Where zap does NOT help (×~1.0):** `scrape03`, `comment`, `Quicksort` — "
      "zap removes the κ (B's `zap` phase is tiny) but the cost was never in the "
      "κ-structure: it's in the residual *leaf* grind (`scrape03`, `Quicksort`: A/B "
      "`close` both huge) or in **PA on the cut** (`comment`: A `pa`≈168k of 181k). "
      "The RQ3 win is specifically on κ-structure cost.")
    W("\n_Heartbeats deterministic; ms one machine. Reproduce: "
      "`python3 scripts/run_rq3.py && python3 scripts/rq3_aggregate.py`._")

    report = REPO / "eval" / "rq3_results.md"
    report.write_text("\n".join(out) + "\n")
    print(f"wrote {report}")
    print(f"\nGeomean speedup: {geomean([r['spd'] for r in ok]):.1f}×  "
          f"(acyclic_only {geomean([r['spd'] for r in acy]):.1f}×, "
          f"both {geomean([r['spd'] for r in bot]):.1f}×)  | B coverage "
          f"{n_total-n_bfail}/{n_total}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
