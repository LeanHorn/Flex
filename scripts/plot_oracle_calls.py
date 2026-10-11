#!/usr/bin/env python3
"""Per-call cost breakdown of the `flex_auto` oracle with a shared z3 process.

Reads the per-call `calls` records written by `benchmark_oracles.py` and draws
two panels:

* top: median cost of one oracle call, split into lean-auto stages and z3
  solving (the z3 process is reused, so no spawn cost per call), next to the
  Lean oracle (`pa_oracle`);
* bottom: per constraint (one `fix` run), the one-time z3 spawn + start-up
  against the per-query work of all `flex_auto` calls, as shares.
"""
import argparse
import json
import statistics
from collections import defaultdict
from pathlib import Path
from typing import Any

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.patches import Patch  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

# Same colours per stage as the pre-optimisation chart, so the two compare directly.
COLORS: dict[str, str] = {
    "mono": "#2a78d6",
    "other": "#eb6834",
    "spawn": "#1bb07a",
    "solve": "#eda200",
    "lean": "#008300",
}
INK = "#4a4a4a"
MUTED = "#8a8a8a"
GRID = "#e2e2e2"
SURFACE = "#fcfcfa"

CASES: list[str] = ["loop01", "countdown", "fib_scraped", "fib_fast"]
AUTO_CONFIG = "auto_synth"
LEAN_CONFIG = "lean"

Record = dict[str, Any]


def split_call(call: dict[str, float]) -> dict[str, float]:
    """Stage times (ms) of one `flex_auto` call; spawn is excluded from solve."""
    spawn = call.get("auto.spawn", 0.0)
    solve = call.get("auto.solver", 0.0) - spawn
    mono = call.get("auto.mono", 0.0)
    other = call["total_ms"] - spawn - solve - mono
    return {"mono": mono, "other": other, "solve": solve}


INCLUDE_WARMUP = False


def measured(records: list[Record], case: str, config: str) -> list[Record]:
    return [r for r in records
            if r["case"] == case and r["config"] == config and r["success"]
            and (INCLUDE_WARMUP or not r["warmup"])]


def per_call_rows(records: list[Record]) -> list[tuple[str, dict[str, float], int]]:
    """(label, median stage ms, call count) per bar, top to bottom."""
    rows: list[tuple[str, dict[str, float], int]] = []
    for case in CASES:
        by_outcome: dict[str, list[dict[str, float]]] = defaultdict(list)
        for r in measured(records, case, AUTO_CONFIG):
            for call in r["calls"]:
                if call["oracle"] == "flex_auto":
                    if "auto.mono_full" in call:
                        raise SystemExit(f"{case}: a call took the full monomorphization path")
                    by_outcome[call["outcome"]].append(split_call(call))
        for outcome in ("proved", "refuted"):
            calls = by_outcome.get(outcome, [])
            if calls:
                med = {k: statistics.median(c[k] for c in calls) for k in ("mono", "other", "solve")}
                rows.append((f"{case} · flex_auto, {outcome}", med, len(calls)))
        for outcome in ("proved", "refuted"):
            lean = [c["total_ms"] for r in measured(records, case, LEAN_CONFIG)
                    for c in r["calls"] if c["oracle"] == "lean" and c["outcome"] == outcome]
            if lean:
                rows.append((f"{case} · Lean oracle, {outcome}",
                             {"lean": statistics.median(lean)}, len(lean)))
    return rows


def per_constraint_rows(records: list[Record]) -> list[tuple[str, dict[str, float], float]]:
    """(case, median ms per part of all flex_auto work in one run, median calls per run)."""
    rows: list[tuple[str, dict[str, float], float]] = []
    for case in CASES:
        parts: list[dict[str, float]] = []
        counts: list[int] = []
        for r in measured(records, case, AUTO_CONFIG):
            calls = [c for c in r["calls"] if c["oracle"] == "flex_auto"]
            split = [split_call(c) for c in calls]
            parts.append({
                "spawn": sum(c.get("auto.spawn", 0.0) for c in calls),
                "mono": sum(c["mono"] for c in split),
                "other": sum(c["other"] for c in split),
                "solve": sum(c["solve"] for c in split),
            })
            counts.append(len(calls))
        if parts:
            rows.append((case, {k: statistics.median(p[k] for p in parts) for k in parts[0]},
                         statistics.median(counts)))
    return rows


def style_axis(ax: plt.Axes, xmax: float, xlabel: str) -> None:
    ax.set_facecolor(SURFACE)
    ax.set_xlim(0, xmax)
    ax.invert_yaxis()
    ax.grid(axis="x", color=GRID, linewidth=1)
    ax.set_axisbelow(True)
    for side in ("top", "right", "left"):
        ax.spines[side].set_visible(False)
    ax.spines["bottom"].set_color("#b5b5b5")
    ax.tick_params(axis="y", length=0, labelsize=11, labelcolor=INK)
    ax.tick_params(axis="x", colors=MUTED, labelsize=10)
    ax.set_xlabel(xlabel, color=INK, fontsize=11)


def draw_stacked(ax: plt.Axes, y: int, parts: list[tuple[str, float]], height: float) -> float:
    left = 0.0
    for key, width in parts:
        if width <= 0:
            continue
        ax.barh(y, width, left=left, height=height, color=COLORS[key],
                edgecolor=SURFACE, linewidth=1.5)
        left += width
    return left


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, default=ROOT / "eval/oracle_results_pushpop.json")
    parser.add_argument("--output", type=Path, default=ROOT / "eval/fig_oracle_calls_pushpop.png")
    parser.add_argument("--xmax", type=float, default=85,
                        help="x-axis limit of the per-call panel (match the earlier chart)")
    parser.add_argument("--scoping", default="(push)/(pop)",
                        help="how queries are isolated in the shared z3 process (title text)")
    parser.add_argument("--include-warmup", action="store_true",
                        help="also use warm-up runs (for previews of a partial run)")
    args = parser.parse_args()
    global INCLUDE_WARMUP
    INCLUDE_WARMUP = args.include_warmup
    records: list[Record] = json.loads(args.input.read_text())["records"]

    calls = per_call_rows(records)
    constraints = per_constraint_rows(records)

    fig, (ax_call, ax_once) = plt.subplots(
        2, 1, figsize=(16.4, 13), facecolor=SURFACE,
        gridspec_kw={"height_ratios": [len(calls), len(constraints) * 1.1], "hspace": 0.3})

    for y, (label, med, n) in enumerate(calls):
        order = ["lean"] if "lean" in med else ["mono", "other", "solve"]
        end = draw_stacked(ax_call, y, [(k, med[k]) for k in order], 0.56)
        text = f"{end:.0f} ms" if end >= 1 else f"{end:.1f} ms"
        if end > args.xmax:
            # Off-scale: z3 ran into its per-query timeout (`unknown`).
            text = f"→ {text}  (z3 timeout, auto.smt.timeout = 1 s)"
            ax_call.text(args.xmax * 0.985, y, text, va="center", ha="right",
                         color="white", fontsize=11, fontweight="bold")
        else:
            ax_call.text(end + args.xmax * 0.01, y, text, va="center", color=INK, fontsize=11)
    ax_call.set_yticks(range(len(calls)), [label for label, _, _ in calls])
    style_axis(ax_call, args.xmax, "median ms per call")
    ax_call.set_title(f"Per query: one z3 process, each query scoped by {args.scoping}",
                      loc="left", color=INK, fontsize=13, pad=12)

    for y, (case, parts, n) in enumerate(constraints):
        total = sum(parts.values())
        draw_stacked(ax_once, y, [(k, 100 * parts[k] / total)
                                  for k in ("spawn", "mono", "other", "solve")], 0.56)
        share = 100 * parts["spawn"] / total
        ax_once.text(101, y, f"{total / 1000:.2f} s over {n:.0f} calls; "
                     f"once: {parts['spawn']:.0f} ms ({share:.1f}%)",
                     va="center", color=INK, fontsize=11)
    ax_once.set_yticks(range(len(constraints)), [case for case, *_ in constraints])
    style_axis(ax_once, 100, "share of all flex_auto time in one constraint (%)")
    ax_once.set_xlim(0, 150)
    ax_once.set_xticks(range(0, 101, 20))
    ax_once.spines["bottom"].set_bounds(0, 100)
    ax_once.set_title("Per constraint: spawning + starting z3 (once) vs. per-query work",
                      loc="left", color=INK, fontsize=13, pad=12)

    legend = [
        Patch(color=COLORS["mono"], label="lean-auto: monomorphization (fast path)"),
        Patch(color=COLORS["other"], label="lean-auto: other translation"),
        Patch(color=COLORS["spawn"], label="Spawning + starting Z3 (once per constraint)"),
        Patch(color=COLORS["solve"], label="Z3 solve (shared process, per query)"),
        Patch(color=COLORS["lean"], label="Lean oracle (pa_oracle)"),
    ]
    fig.legend(handles=legend, loc="upper center", ncol=3, frameon=False, fontsize=11,
               labelcolor=INK, bbox_to_anchor=(0.6, 0.995))
    fig.subplots_adjust(left=0.2, right=0.97, top=0.9, bottom=0.05)
    fig.savefig(args.output, dpi=100, facecolor=SURFACE)
    print(f"wrote {args.output}")
    for label, med, n in calls:
        print(f"{label:40} n={n:4d} " + " ".join(f"{k}={v:.2f}" for k, v in med.items()))
    for case, parts, n in constraints:
        print(f"{case:12} calls={n:.0f} " + " ".join(f"{k}={v:.1f}ms" for k, v in parts.items()))

if __name__ == "__main__":
    main()
