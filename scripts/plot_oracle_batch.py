#!/usr/bin/env python3
"""Per-clause batching of `flex_auto` against per-query calls and the Lean oracle.

Reads `benchmark_oracles.py` output that includes the `auto_synth_per_query`
and `auto_synth` configurations and draws two panels:

* top: cost per synthesis query (median ms). A per-query `flex_auto` call is
  shown next to a per-clause batch divided by the queries it answers (the
  sat-guard plus each candidate), and the Lean oracle's proved and refuted
  calls;
* bottom: the whole synthesis phase of one run (median ms) per configuration,
  split into `flex_auto`, the Lean oracle, the one-time z3 spawn, and the rest
  (Houdini bookkeeping, building VCs).
"""
import argparse
import json
import statistics
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402

from plot_oracle_calls import COLORS, INK, SURFACE, draw_stacked, style_axis  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CASES: list[str] = ["loop01", "countdown"]
STAGES: list[str] = ["mono", "other", "solve"]
REST = "#bdbdbd"

Record = dict[str, Any]

CONFIG_LABELS: dict[str, str] = {
    "lean": "Lean only",
    "auto_synth_per_query": "synth := flex_auto, per query",
    "auto_synth": "synth := flex_auto, per clause",
    "lean_auto_fallback": "Lean first, flex_auto per clause",
}


def measured(records: list[Record], case: str, config: str) -> list[Record]:
    return [r for r in records
            if r["case"] == case and r["config"] == config and not r["warmup"] and r["success"]]


def synthesis_calls(run: Record, oracle_prefix: str) -> list[dict[str, float]]:
    return [c for c in run["calls"]
            if c.get("phase") == "synthesis" and c["oracle"].startswith(oracle_prefix)]


def stages(call: dict[str, float]) -> dict[str, float]:
    """mono / other / solve ms of one flex_auto call; the z3 spawn is excluded."""
    spawn = call.get("auto.spawn", 0.0)
    solve = call.get("auto.solver", 0.0) - spawn
    mono = call.get("auto.mono", 0.0)
    return {"mono": mono, "other": call["total_ms"] - spawn - solve - mono, "solve": solve}


def per_query_rows(records: list[Record]) -> list[tuple[str, dict[str, float], str]]:
    rows: list[tuple[str, dict[str, float], str]] = []
    for case in CASES:
        single = [stages(c) for r in measured(records, case, "auto_synth_per_query")
                  for c in synthesis_calls(r, "flex_auto") if c["oracle"] == "flex_auto"]
        if single:
            rows.append((f"{case} · flex_auto, one call per query",
                         {k: statistics.median(c[k] for c in single) for k in STAGES},
                         f"n = {len(single)} calls"))
        shares: list[dict[str, float]] = []
        sizes: list[int] = []
        for r in measured(records, case, "auto_synth"):
            for c in synthesis_calls(r, "flex_auto_clause"):
                # The driver scales every field by 1e-6; this one is a count.
                queries = round(c.get("batch.candidates", 0.0) * 1e6) + 1  # + sat-guard
                sizes.append(queries)
                shares.append({k: v / queries for k, v in stages(c).items()})
        if shares:
            rows.append((f"{case} · flex_auto, per clause ÷ queries",
                         {k: statistics.median(c[k] for c in shares) for k in STAGES},
                         f"n = {len(shares)} batches of {statistics.median(sizes):.1f} queries"))
        for outcome in ("proved", "refuted"):
            lean = [c["total_ms"] for r in measured(records, case, "lean")
                    for c in synthesis_calls(r, "lean") if c["outcome"] == outcome]
            if lean:
                rows.append((f"{case} · Lean oracle, {outcome}",
                             {"lean": statistics.median(lean)}, f"n = {len(lean)} calls"))
    return rows


def synthesis_rows(records: list[Record]) -> list[tuple[str, dict[str, float], float]]:
    rows: list[tuple[str, dict[str, float], float]] = []
    for case in CASES:
        for config, label in CONFIG_LABELS.items():
            runs = measured(records, case, config)
            if not runs:
                continue
            parts: list[dict[str, float]] = []
            for r in runs:
                auto = synthesis_calls(r, "flex_auto")
                spawn = sum(c.get("auto.spawn", 0.0) for c in auto)
                flex = sum(c["total_ms"] for c in auto) - spawn
                lean = sum(c["total_ms"] for c in synthesis_calls(r, "lean"))
                total = r["phases_ms"]["synthesis"]
                parts.append({"flex": flex, "lean": lean, "spawn": spawn,
                              "rest": max(total - flex - lean - spawn, 0.0), "total": total})
            med = {k: statistics.median(p[k] for p in parts) for k in parts[0]}
            rows.append((f"{case} · {label}", med, med.pop("total")))
    return rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=ROOT / "eval/oracle_results_batch.json")
    parser.add_argument("--output", type=Path, default=ROOT / "eval/fig_oracle_batch.png")
    args = parser.parse_args()
    records: list[Record] = json.loads(args.input.read_text())["records"]
    queries = per_query_rows(records)
    synth = synthesis_rows(records)

    fig, (ax_q, ax_s) = plt.subplots(
        2, 1, figsize=(16.4, 13.5), facecolor=SURFACE,
        gridspec_kw={"height_ratios": [len(queries), len(synth)], "hspace": 0.3})

    qmax = max(sum(m.values()) for _, m, _ in queries) * 1.3
    for y, (label, med, note) in enumerate(queries):
        order = ["lean"] if "lean" in med else STAGES
        end = draw_stacked(ax_q, y, [(k, med[k]) for k in order], 0.56)
        ax_q.text(end + qmax * 0.01, y, f"{end:.1f} ms   ({note})", va="center",
                  color=INK, fontsize=11)
    ax_q.set_yticks(range(len(queries)), [label for label, _, _ in queries])
    style_axis(ax_q, qmax, "median ms per synthesis query")
    ax_q.set_title("Per query: a per-clause batch shares one translation and one solver scope",
                   loc="left", color=INK, fontsize=13, pad=12)

    smax = max(total for *_, total in synth) * 1.25
    colors = {**COLORS, "flex": COLORS["solve"], "rest": REST}
    for y, (label, med, total) in enumerate(synth):
        draw_stacked(ax_s, y, [(k, med[k]) for k in ("flex", "lean", "spawn", "rest")], 0.56,
                     colors=colors)
        ax_s.text(total + smax * 0.01, y, f"{total:.0f} ms", va="center", color=INK, fontsize=11)
    ax_s.set_yticks(range(len(synth)), [label for label, _, _ in synth])
    style_axis(ax_s, smax, "median ms of the synthesis phase per run")
    ax_s.set_title("Whole synthesis phase: where the time goes", loc="left", color=INK,
                   fontsize=13, pad=12)

    legend = [
        Patch(color=COLORS["mono"], label="lean-auto: monomorphization"),
        Patch(color=COLORS["other"], label="lean-auto: other translation"),
        Patch(color=COLORS["solve"], label="Z3 solve (top) / all flex_auto time (bottom)"),
        Patch(color=COLORS["lean"], label="Lean oracle (pa_oracle)"),
        Patch(color=COLORS["spawn"], label="Spawning + starting Z3 (once)"),
        Patch(color=REST, label="Rest of synthesis (Houdini, building VCs)"),
    ]
    fig.legend(handles=legend, loc="upper center", ncol=3, frameon=False, fontsize=11,
               labelcolor=INK, bbox_to_anchor=(0.6, 0.995))
    fig.subplots_adjust(left=0.24, right=0.97, top=0.9, bottom=0.05)
    fig.savefig(args.output, dpi=100, facecolor=SURFACE)
    print(f"wrote {args.output}")
    for label, med, note in queries:
        print(f"{label:48} {note:32} " + " ".join(f"{k}={v:.2f}" for k, v in med.items()))
    for label, med, total in synth:
        print(f"{label:52} total={total:.0f} " + " ".join(f"{k}={v:.0f}" for k, v in med.items()))


if __name__ == "__main__":
    main()
