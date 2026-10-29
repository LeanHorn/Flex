#!/usr/bin/env python3
"""Generate POPL-ready RQ3 figures + LaTeX table from eval/rq3_results.json.

Outputs (in eval/):
  fig_rq3_phases.pdf   — per-phase heartbeat locus, A vs B, normalised to A=1.0
                         (the hero figure: shows zap replaces grind's search)
  fig_rq3_speedup.pdf  — speedup scoreboard, sorted, coloured by bucket
  rq3_table.tex        — booktabs results table + foundational (term/kernel) table

Run: python3 scripts/rq3_plots.py
"""
from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

REPO = Path(__file__).resolve().parent.parent
DATA = REPO / "eval" / "rq3_results.json"

# Okabe–Ito colour-blind-safe palette.
C_ZAP = "#0072B2"   # blue   — zap / σ̂ acyclic-κ elimination
C_PA     = "#999999"   # grey   — predicate abstraction (Houdini) on the cut
C_GRIND  = "#D55E00"   # orange — grind closer (proof search)
C_OTHER  = "#E2E2E2"   # light  — un-instrumented overhead

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 8,
    "axes.linewidth": 0.6,
    "xtick.major.width": 0.6,
    "ytick.major.width": 0.6,
    "pdf.fonttype": 42,   # editable text in the PDF
})


def load() -> list[dict]:
    data = json.loads(DATA.read_text())
    rows = []
    for b, c in data.items():
        A, B = c.get("A", {}), c.get("B", {})
        if A.get("status") != "ok" or B.get("status") != "ok":
            continue
        def ph(d, key):
            phases = d.get("phases", {})
            if key in phases:
                return phases[key]
            # Read phase labels recorded by earlier evaluations.
            if key.startswith("zap:"):
                return phases.get("fusion:" + key[4:], 0)
            return 0
        a_fus, a_pa, a_cl = (ph(A, "solve_fixpoint:fuse"),
                             ph(A, "solve_fixpoint:pa"),
                             ph(A, "solve_fixpoint:close"))
        b_fus = sum(ph(B, f"zap:{p}") for p in ("sol", "build", "clean"))
        b_pa, b_cl = ph(B, "solve_fixpoint:pa"), ph(B, "solve_fixpoint:close")
        at, bt = A["hb"], B["hb"]
        rows.append(dict(
            bench=b, grp=("FX" if c.get("group") == "FluxRS" else "LF"),
            nac=A.get("n_acyclic", 0), ncy=A.get("n_cyclic", 0),
            bucket=("both" if A.get("n_cyclic", 0) > 0 else "acyclic_only"),
            a_fus=a_fus, a_pa=a_pa, a_cl=a_cl, a_other=max(0, at - a_fus - a_pa - a_cl),
            b_fus=b_fus, b_pa=b_pa, b_cl=b_cl, b_other=max(0, bt - b_fus - b_pa - b_cl),
            at=at, bt=bt, spd=at / bt,
            a_depth=A.get("depth"), b_depth=B.get("depth"),
            a_nconst=A.get("nconst"), b_nconst=B.get("nconst"),
            a_ker=A.get("kerus"), b_ker=B.get("kerus")))
    return rows


def geomean(xs):
    xs = [x for x in xs if x and x > 0]
    return math.exp(sum(map(math.log, xs)) / len(xs)) if xs else float("nan")


# ── Fig 1: per-phase locus (normalised stacked bars) ───────────────────────
def bound_tag(r):
    """For flat rows, name the phase that bounds BOTH configurations."""
    if r["spd"] >= 1.3:
        return None
    if min(r["a_pa"] / r["at"], r["b_pa"] / r["bt"]) > 0.5:
        return "PA-bound"
    if min(r["a_cl"] / r["at"], r["b_cl"] / r["bt"]) > 0.5:
        return "leaf-bound"
    return None


def fig_phases(rows):
    rows = sorted(rows, key=lambda r: (r["bucket"] != "acyclic_only", -r["spd"]))
    n = len(rows)
    fig, ax = plt.subplots(figsize=(7.0, 0.34 * n + 0.85))
    H = 0.36                      # bar height
    sep_after = None
    for i, r in enumerate(rows):
        cy = n - 1 - i            # top-to-bottom
        ya, yb = cy + 0.20, cy - 0.20
        s = r["at"]               # normalise both bars by A's total
        for y, segs in ((ya, [(r["a_fus"], C_ZAP), (r["a_pa"], C_PA),
                              (r["a_cl"], C_GRIND), (r["a_other"], C_OTHER)]),
                        (yb, [(r["b_fus"], C_ZAP), (r["b_pa"], C_PA),
                              (r["b_cl"], C_GRIND), (r["b_other"], C_OTHER)])):
            left = 0.0
            for val, col in segs:
                w = val / s
                ax.barh(y, w, height=H, left=left, color=col,
                        edgecolor="white", linewidth=0.3)
                left += w
        ax.text(-0.012, ya, "A", va="center", ha="right", fontsize=6.5, color="#444")
        ax.text(-0.012, yb, "B", va="center", ha="right", fontsize=6.5, color="#444")
        ax.text(1.03, cy, f"{r['spd']:.1f}×", va="center", ha="left",
                fontsize=7.2, fontweight="bold")
        tag = bound_tag(r)
        if tag:
            ax.text(1.10, cy, tag, va="center", ha="left", fontsize=6.5,
                    style="italic", color="#555")
        if r["bucket"] == "acyclic_only":
            sep_after = cy - 0.5
    # column header for the speedup annotations
    ax.text(1.03, n - 0.05, "speedup", va="bottom", ha="left", fontsize=6.5,
            style="italic", color="#444")
    # left-margin brackets naming the two blocks
    import matplotlib.transforms as mtransforms
    tr = mtransforms.blended_transform_factory(ax.transAxes, ax.transData)
    n_acy = sum(1 for r in rows if r["bucket"] == "acyclic_only")
    n_cut = sum(1 for r in rows if r["bucket"] == "both")
    for y0, y1, lbl in ((sep_after + 0.2, n - 0.3, f"acyclic-only ({n_acy} VCs)"),
                        (-0.5, sep_after - 0.2, f"acyclic + cut ({n_cut} VCs)")):
        ax.plot([-0.30, -0.30], [y0, y1], color="#888", lw=0.7,
                transform=tr, clip_on=False)
        ax.text(-0.315, (y0 + y1) / 2, lbl, va="center", ha="center",
                fontsize=6.5, color="#555", rotation=90, transform=tr)
    ax.set_yticks([n - 1 - i for i in range(n)])
    ax.set_yticklabels([f"{r['bench']} ({r['grp']})" for r in rows], fontsize=7)
    ax.set_ylim(-0.7, n + 0.25)
    ax.set_xlim(-0.05, 1.20)
    ax.set_xticks([0.0, 0.2, 0.4, 0.6, 0.8, 1.0])
    ax.set_xlabel("heartbeats, normalised to config A's total", fontsize=8)
    ax.axvline(1.0, color="#bbb", lw=0.6, ls=(0, (3, 3)), zorder=0)
    if sep_after is not None:
        ax.axhline(sep_after, color="#888", lw=0.7)
    for sp in ("top", "right"):
        ax.spines[sp].set_visible(False)
    ax.legend(handles=[
        Patch(fc=C_ZAP, label="acyclic-κ elimination"),
        Patch(fc=C_PA, label="predicate abstraction (cut)"),
        Patch(fc=C_GRIND, label="grind (proof search)"),
        Patch(fc=C_OTHER, label="other")],
        loc="lower center", bbox_to_anchor=(0.5, 1.0), ncol=4,
        frameon=False, fontsize=7, handlelength=1.1, columnspacing=1.2)
    fig.tight_layout()
    out = REPO / "eval" / "fig_rq3_phases.pdf"
    fig.savefig(out, bbox_inches="tight")
    fig.savefig(out.with_suffix(".png"), dpi=200, bbox_inches="tight")
    plt.close(fig)
    print(f"wrote {out}")


# ── Fig 2: speedup scoreboard ──────────────────────────────────────────────
def fig_speedup(rows):
    rows = sorted(rows, key=lambda r: r["spd"])
    n = len(rows)
    fig, ax = plt.subplots(figsize=(3.35, 0.26 * n + 0.6))
    ys = range(n)
    cols = [C_ZAP if r["bucket"] == "acyclic_only" else C_PA for r in rows]
    ax.barh(list(ys), [r["spd"] for r in rows], color=cols, height=0.66,
            edgecolor="white", linewidth=0.3)
    for y, r in zip(ys, rows):
        ax.text(r["spd"] + 0.07, y, f"{r['spd']:.1f}", va="center",
                ha="left", fontsize=6.6)
    ax.set_yticks(list(ys))
    ax.set_yticklabels([r["bench"] for r in rows], fontsize=6.6)
    ax.set_xlabel("speedup  (A hb / B hb)", fontsize=8)
    ax.axvline(1.0, color="#555", lw=0.8)
    gm = geomean([r["spd"] for r in rows if r["bucket"] == "acyclic_only"])
    ax.axvline(gm, color=C_GRIND, lw=0.9, ls=(0, (3, 2)))
    ax.text(gm, n - 0.2, f"  geomean\n  (acyclic) {gm:.1f}×", color=C_GRIND,
            fontsize=6.2, va="top", ha="left")
    ax.set_xlim(0, max(r["spd"] for r in rows) * 1.18)
    ax.set_ylim(-0.6, n - 0.4)
    for sp in ("top", "right"):
        ax.spines[sp].set_visible(False)
    ax.legend(handles=[Patch(fc=C_ZAP, label="acyclic-only"),
                       Patch(fc=C_PA, label="acyclic + cut")],
              loc="lower right", frameon=False, fontsize=6.6, handlelength=1.0)
    fig.tight_layout()
    out = REPO / "eval" / "fig_rq3_speedup.pdf"
    fig.savefig(out, bbox_inches="tight")
    plt.close(fig)
    print(f"wrote {out}")


# ── LaTeX table ────────────────────────────────────────────────────────────
def latex_table(rows):
    def fmt(x):
        return f"{x:,}".replace(",", "\\,")
    order = sorted(rows, key=lambda r: (r["bucket"] != "acyclic_only", -r["spd"]))
    acy = [r for r in order if r["bucket"] == "acyclic_only"]
    bot = [r for r in order if r["bucket"] == "both"]
    L = [
        r"% Auto-generated by scripts/rq3_plots.py — do not edit by hand.",
        r"\begin{table}[t]", r"\centering", r"\small",
        r"\caption{RQ3: deterministic proof term (Zap, \textbf{B}) vs.\ proof"
        r" search (grind, \textbf{A}) on benchmarks with $\geq 1$ acyclic $\kappa$"
        r" (LF: Liquid-fixpoint, FX: FluxRS). Heartbeat counts (in thousands)"
        r" are deterministic across runs.}",
        r"\label{tab:rq3}",
        r"\begin{tabular}{llrrrrr}", r"\toprule",
        r"Benchmark & Src & $\kappa_{\text{acy}}$ & $\kappa_{\text{cut}}$"
        r" & A (hb) & B (hb) & Speedup \\", r"\midrule",
        r"\multicolumn{7}{l}{\emph{acyclic-only}}\\",
    ]
    def esc(s):
        return s.replace("_", "\\_")
    def line(r):
        nm = esc(r["bench"])
        return (f"\\quad {nm} & {r['grp']} & {r['nac']}"
                f" & {r['ncy']} & {fmt(r['at'])} & {fmt(r['bt'])}"
                f" & ${r['spd']:.1f}" + r"\times$ \\")
    L += [line(r) for r in acy]
    L += [r"\midrule", r"\multicolumn{7}{l}{\emph{acyclic + cut}}\\"]
    L += [line(r) for r in bot]
    gm_all = geomean([r["spd"] for r in rows])
    gm_acy = geomean([r["spd"] for r in acy])
    gm_bot = geomean([r["spd"] for r in bot])
    L += [
        r"\midrule",
        f"\\multicolumn{{6}}{{r}}{{Geomean (acyclic-only / +cut / all)}}"
        f" & ${gm_acy:.1f}\\!/\\!{gm_bot:.1f}\\!/\\!{gm_all:.1f}\\times$ \\\\",
        r"\bottomrule", r"\end{tabular}", r"\end{table}", "",
        r"% Foundational: the constructive term (B) is larger but kernel-checks fast.",
        r"\begin{table}[t]", r"\centering", r"\small",
        r"\caption{Proof-term shape and kernel re-check time (foundational)."
        r" Depth is the elaborated proof term's expression-tree depth; \#consts"
        r" its number of distinct constants. The constructive Zap term (B) is"
        r" deeper than grind's on 15 of 18 VCs but is built without search, and"
        r" the kernel re-checks every term in under 25\,ms.}",
        r"\label{tab:rq3-term}",
        r"\begin{tabular}{lrrrrrr}", r"\toprule",
        r" & \multicolumn{2}{c}{depth} & \multicolumn{2}{c}{\#consts}"
        r" & \multicolumn{2}{c}{kernel ($\mu$s)} \\",
        r"\cmidrule(lr){2-3}\cmidrule(lr){4-5}\cmidrule(lr){6-7}",
        r"Benchmark & A & B & A & B & A & B \\", r"\midrule",
    ]
    for r in order:
        nm = esc(r["bench"])
        L.append(f"{nm} & {r['a_depth']} & {r['b_depth']}"
                 f" & {r['a_nconst']} & {r['b_nconst']} & {fmt(r['a_ker'])}"
                 f" & {fmt(r['b_ker'])} " + r"\\")
    L += [r"\bottomrule", r"\end{tabular}", r"\end{table}"]
    out = REPO / "eval" / "rq3_table.tex"
    out.write_text("\n".join(L) + "\n")
    print(f"wrote {out}")


def main():
    rows = load()
    fig_phases(rows)
    fig_speedup(rows)
    latex_table(rows)
    print(f"\n{len(rows)} benchmarks | geomean (acyclic) "
          f"{geomean([r['spd'] for r in rows if r['bucket']=='acyclic_only']):.1f}×"
          f" | overall {geomean([r['spd'] for r in rows]):.1f}×")


if __name__ == "__main__":
    main()
