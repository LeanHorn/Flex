#!/usr/bin/env python3
"""Aggregate rq2_results.json into a Markdown report + LaTeX tables.

Reads the output of run_fusion_experiments.py (rq2_results.json) and
optionally lean-fixpoint/eval/rq3_results.json for the liquid-fixpoint suite.

Headline metric: `elim_hb` = Σ of [phase] heartbeats for that config's
acyclic-κ elimination step (pure elimination cost, no residual).

Usage:
    python3 make_rq2_table.py
    python3 make_rq2_table.py --in my_results.json
    python3 make_rq2_table.py --format both
    python3 make_rq2_table.py --lf-results ../../eval/rq3_results.json
    python3 make_rq2_table.py --lf-results ../../eval/rq3_results.json --aggregate
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).parent.resolve()
LF_ROOT = ROOT.parent.parent
CFGS = ("zap", "grind", "aesop")

SUITE_ORDER = ["flux-medium", "wave", "Flux lean-bench", "liquid-fixpoint", "hashtable", "sorting"]
SUITE_DISPLAY = {
    "flux-medium":      "flux-medium",
    "liquid-fixpoint":  "liquid-fixpoint",
    "hashtable":        "hashtable",
    "sorting":          "sorting",
}

# LaTeX macro to use for each suite's display name in the aggregate table.
# Matches the \fluxmedium/\wavesuite/\fluxtests/\lfsuite/\flexbench macros
# used for the row names in lean-fixpoint-paper/sections/07-evaluation.tex
# (tab:rq2-flux-agg).
SUITE_MACROS_AGG = {
    "flux-medium":     r"\fluxmedium",
    "wave":            r"\wavesuite",
    "Flux lean-bench": r"\fluxtests",
    "liquid-fixpoint": r"\lfsuite",
}

# Suites merged into a single "\flexbench" (RQ1 case studies) row in the
# aggregate table, matching the paper.
CASE_STUDY_SUITES = {"hashtable", "sorting"}
CASE_STUDY_LABEL = r"\flexbench"


def geomean(xs: list[float]) -> float:
    xs = [x for x in xs if x and x > 0]
    return math.exp(sum(map(math.log, xs)) / len(xs)) if xs else float("nan")


def load(path: Path) -> list[dict]:
    data = json.loads(path.read_text())
    rows = []
    for key, c in data.items():
        r = dict(
            key=key,
            suite=c.get("suite", ""),
            proof_name=c.get("proof_name", key),
            vc_type=c.get("vc_type", ""),
        )
        for k in CFGS:
            d = c.get(k, {})
            ok = d.get("status") == "ok"
            r[k] = dict(
                ok=ok,
                elim=d.get("elim_hb"),
                hb=d.get("hb"),
                ms=d.get("ms"),
                depth=d.get("depth"),
                nconst=d.get("nconst"),
                kerus=d.get("kerus"),
            )
        rows.append(r)
    return rows


def load_lf(path: Path) -> list[dict]:
    """Load lean-fixpoint eval/rq3_results.json (scripts/run_rq3.py) into our row format.

    Only includes Liquid-fixpoint group entries (not FluxRS).
    """
    data = json.loads(path.read_text())
    rows = []
    for bench, c in data.items():
        if c.get("group") != "Liquid-fixpoint":
            continue
        r = dict(key=bench, suite="liquid-fixpoint", proof_name=bench, vc_type="")
        for k in CFGS:
            d = c.get(k, {})
            ok = d.get("status") == "ok"
            r[k] = dict(
                ok=ok,
                elim=d.get("elim_hb"),
                hb=d.get("hb"),
                ms=d.get("ms"),
                depth=d.get("depth"),
                nconst=d.get("nconst"),
                kerus=d.get("kerus"),
            )
        rows.append(r)
    return rows


def _suite_short(suite: str) -> str:
    return {
        "flux-medium":     "flux-med",
        "liquid-fixpoint": "lf",
        "hashtable":       "hash",
        "sorting":         "sort",
    }.get(suite, suite[:6])


# ── Markdown ──────────────────────────────────────────────────────────────────

def write_markdown(rows: list[dict], out_path: Path) -> None:
    def cell(c, base):
        if not c["ok"] or c["elim"] is None:
            return "FAIL"
        s = str(c["elim"])
        if base and c["elim"] and base != c["elim"]:
            s += f" ({c['elim'] / base:.0f}×)"
        return s

    suites: dict[str, list[dict]] = {}
    for r in sorted(rows, key=lambda r: (SUITE_ORDER.index(r["suite"])
                                         if r["suite"] in SUITE_ORDER else 99,
                                         r["proof_name"])):
        suites.setdefault(r["suite"], []).append(r)

    def n_ok(k: str) -> int:
        return sum(1 for r in rows if r[k]["ok"])

    def gm_slow(k: str) -> float:
        return geomean([r[k]["elim"] / r["zap"]["elim"] for r in rows
                        if r[k]["ok"] and r["zap"]["ok"] and r["zap"]["elim"]])

    lines: list[str] = []
    W = lines.append
    W("# RQ2: acyclic-κ elimination — zap vs grind vs aesop\n")
    W("Headline metric: `elim_hb` = heartbeats spent in the acyclic-κ elimination "
      "step only (residual VC left as `all_goals sorry`). Parenthesised `×` is "
      "slowdown relative to `zap` (fusion).\n")
    W("| VC | suite | zap | grind | aesop |")
    W("|---|---|--:|--:|--:|")
    for suite_name, suite_rows in suites.items():
        for r in suite_rows:
            base = r["zap"]["elim"] if r["zap"]["ok"] else None
            W(f"| `{r['proof_name']}` | {_suite_short(suite_name)}"
              f" | {cell(r['zap'], base)}"
              f" | {cell(r['grind'], base)}"
              f" | {cell(r['aesop'], base)} |")

    W(f"\n**Coverage:** zap {n_ok('zap')}/{len(rows)}  "
      f"grind {n_ok('grind')}/{len(rows)}  aesop {n_ok('aesop')}/{len(rows)}")
    W(f"\n**Geomean slowdown vs zap** (solved-by-both): "
      f"grind {gm_slow('grind'):.1f}×  aesop {gm_slow('aesop'):.1f}×\n")

    W("## Per-suite aggregate\n")
    W("| suite | VCs | zap ok | grind ok | aesop ok | gm grind/zap | gm aesop/zap |")
    W("|---|--:|--:|--:|--:|--:|--:|")
    for suite_name, suite_rows in suites.items():
        nok = lambda k: sum(1 for r in suite_rows if r[k]["ok"])
        gm = lambda k: geomean([r[k]["elim"] / r["zap"]["elim"] for r in suite_rows
                                 if r[k]["ok"] and r["zap"]["ok"] and r["zap"]["elim"]])
        W(f"| {suite_name} | {len(suite_rows)}"
          f" | {nok('zap')} | {nok('grind')} | {nok('aesop')}"
          f" | {gm('grind'):.1f}× | {gm('aesop'):.1f}× |")

    out_path.write_text("\n".join(lines) + "\n")
    print(f"wrote {out_path}")


# ── LaTeX ─────────────────────────────────────────────────────────────────────

def write_latex(rows: list[dict], out_path: Path) -> None:
    def esc(s: str) -> str:
        return s.replace("_", "\\_")

    def fmt(x) -> str:
        return f"{x:,}".replace(",", "\\,") if isinstance(x, int) else str(x)

    FAIL = r"\textit{fail}"

    def cell(c, base):
        if not c["ok"] or c["elim"] is None:
            return FAIL
        s = fmt(c["elim"])
        if base and c["elim"] and base != c["elim"]:
            s += f"\\,({c['elim'] / base:.0f}$\\times$)"
        return s

    def tcell(c, key):
        return fmt(c[key]) if c["ok"] and c[key] is not None else r"\textit{f}"

    order = sorted(rows, key=lambda r: (SUITE_ORDER.index(r["suite"])
                                        if r["suite"] in SUITE_ORDER else 99,
                                        r["proof_name"]))

    def n_ok(k):
        return sum(1 for r in rows if r[k]["ok"])

    def gm_slow(k):
        return geomean([r[k]["elim"] / r["zap"]["elim"] for r in rows
                        if r[k]["ok"] and r["zap"]["ok"] and r["zap"]["elim"]])

    L: list[str] = [
        r"% Auto-generated by make_rq2_table.py — do not edit by hand.",
        r"\begin{table}[t]", r"\centering", r"\small",
        r"\begin{tabular}{llrrr}", r"\toprule",
        r"VC & Suite & \textsc{Zap} & \fusiong & \fusiona \\",
        r"\midrule",
    ]

    prev_suite = None
    for r in order:
        if r["suite"] != prev_suite:
            if prev_suite is not None:
                L.append(r"\midrule")
            L.append(f"\\multicolumn{{5}}{{l}}{{\\emph{{{esc(SUITE_DISPLAY.get(r['suite'], r['suite']))}}}}} \\\\")
            prev_suite = r["suite"]
        base = r["zap"]["elim"] if r["zap"]["ok"] else None
        L.append(
            f"\\quad {esc(r['proof_name'])}"
            f" & {_suite_short(r['suite'])}"
            f" & {cell(r['zap'], base)}"
            f" & {cell(r['grind'], base)}"
            f" & {cell(r['aesop'], base)} \\\\")

    suites: dict[str, list[dict]] = {}
    for r in order:
        suites.setdefault(r["suite"], []).append(r)

    def suite_n_ok(rs, k):
        return sum(1 for r in rs if r[k]["ok"])

    def suite_gm(rs, k):
        return geomean([r[k]["elim"] / r["zap"]["elim"] for r in rs
                        if r[k]["ok"] and r["zap"]["ok"] and r["zap"]["elim"]])

    L.append(r"\midrule")
    for suite_name, suite_rows in suites.items():
        zok = suite_n_ok(suite_rows, "zap")
        gok = suite_n_ok(suite_rows, "grind")
        aok = suite_n_ok(suite_rows, "aesop")
        gg  = suite_gm(suite_rows, "grind")
        ag  = suite_gm(suite_rows, "aesop")
        gstr = f"{gg:.0f}$\\times$" if not math.isnan(gg) else "—"
        astr = f"{ag:.0f}$\\times$" if not math.isnan(ag) else "—"
        label = esc(SUITE_DISPLAY.get(suite_name, suite_name))
        L.append(
            f"\\emph{{{label}}} ({len(suite_rows)} VCs)"
            f" & & {zok}/{len(suite_rows)} & {gok}/{len(suite_rows)}"
            f" & {aok}/{len(suite_rows)} \\\\")
        L.append(
            f"\\quad geomean slowdown & & 1.0$\\times$"
            f" & {gstr} & {astr} \\\\")
    L += [
        r"\midrule",
        f"\\textbf{{All}} ({len(rows)} VCs)"
        f" & & {n_ok('zap')}/{len(rows)} & {n_ok('grind')}/{len(rows)}"
        f" & {n_ok('aesop')}/{len(rows)} \\\\",
        f"\\quad geomean slowdown & & 1.0$\\times$"
        f" & {gm_slow('grind'):.0f}$\\times$ & {gm_slow('aesop'):.0f}$\\times$ \\\\",
        r"\bottomrule", r"\end{tabular}",
        r"\caption{RQ2: cost of acyclic-$\kappa$ elimination only "
        r"(then \lean{sorry}), in thousands of Lean heartbeats (deterministic). "
        r"\textsc{Zap} (\zap) builds the proof term; \fusiong"
        r"/\fusiona~ discharge each $\kappa$-head clause by proof search. "
        r"\textit{fail} = search variant errored on a $\kappa$-head clause. "
        r"Parenthesised $\times$ is slowdown vs.\ \textsc{Zap}.}",
        r"\label{tab:rq2}",
        r"\end{table}", "",
        r"% Proof-term shape.",
        r"\begin{table}[t]", r"\centering", r"\small",
        r"\begin{tabular}{lrrrrrrrrr}", r"\toprule",
        r" & \multicolumn{3}{c}{depth} & \multicolumn{3}{c}{\#consts}"
        r" & \multicolumn{3}{c}{ker$\mu$s} \\",
        r"\cmidrule(lr){2-4}\cmidrule(lr){5-7}\cmidrule(lr){8-10}",
        r"VC & Z & g & a & Z & g & a & Z & g & a \\", r"\midrule",
    ]
    for r in order:
        L.append(
            f"{esc(r['proof_name'])}"
            f" & {tcell(r['zap'],'depth')} & {tcell(r['grind'],'depth')} & {tcell(r['aesop'],'depth')}"
            f" & {tcell(r['zap'],'nconst')} & {tcell(r['grind'],'nconst')} & {tcell(r['aesop'],'nconst')}"
            f" & {tcell(r['zap'],'kerus')} & {tcell(r['grind'],'kerus')} & {tcell(r['aesop'],'kerus')}"
            r" \\")
    L += [r"\bottomrule", r"\end{tabular}",
          r"\caption{Elimination proof-term shape: depth, \#distinct constants, "
          r"and kernel re-check time (ker$\mu$s). \textit{f} = variant failed.}",
          r"\label{tab:rq2-term}",
          r"\end{table}"]

    out_path.write_text("\n".join(L) + "\n")
    print(f"wrote {out_path}")


# ── LaTeX aggregate ───────────────────────────────────────────────────────────

def write_latex_aggregate(rows: list[dict], out_path: Path) -> None:
    def esc(s: str) -> str:
        return s.replace("_", "\\_")

    order = sorted(rows, key=lambda r: (SUITE_ORDER.index(r["suite"])
                                        if r["suite"] in SUITE_ORDER else 99,
                                        r["proof_name"]))
    suites: dict[str, list[dict]] = {}
    for r in order:
        suites.setdefault(r["suite"], []).append(r)

    def n_ok(k):
        return sum(1 for r in rows if r[k]["ok"])

    def suite_n_ok(rs, k):
        return sum(1 for r in rs if r[k]["ok"])

    def suite_gm_ratio(rs, k, field):
        return geomean([r[k][field] / r["zap"][field] for r in rs
                        if r[k]["ok"] and r["zap"]["ok"]
                        and r[k][field] and r["zap"][field]])

    def suite_gm_abs(rs, k, field):
        return geomean([r[k][field] for r in rs if r[k]["ok"] and r[k][field]])

    def gmstr_ratio(g: float) -> str:
        return f"{g:.0f}$\\times$" if not math.isnan(g) else "—"

    def gmstr_abs(g: float) -> str:
        return f"{g:,.0f}".replace(",", "\\,") if not math.isnan(g) else "—"

    def reduced_str(rs: list[dict], zok: int, k: str) -> str:
        ok = suite_n_ok(rs, k)
        pct = f"{100*ok/zok:.0f}\\%" if zok else "—"
        return f"{ok} ({pct})"

    def row(label: str, n: int, rs: list[dict]) -> str:
        zok = suite_n_ok(rs, "zap")
        return (f"{label} & {n}"
                f" & {gmstr_abs(suite_gm_abs(rs, 'zap', 'hb'))}"
                f" & {gmstr_abs(suite_gm_abs(rs, 'zap', 'ms'))}"
                f" & {reduced_str(rs, zok, 'grind')}"
                f" & {gmstr_ratio(suite_gm_ratio(rs, 'grind', 'hb'))}"
                f" & {gmstr_ratio(suite_gm_ratio(rs, 'grind', 'ms'))}"
                f" & {reduced_str(rs, zok, 'aesop')}"
                f" & {gmstr_ratio(suite_gm_ratio(rs, 'aesop', 'hb'))}"
                f" & {gmstr_ratio(suite_gm_ratio(rs, 'aesop', 'ms'))}"
                r" \\")

    L: list[str] = [
        r"% Auto-generated by make_rq2_table.py — do not edit by hand.",
        r"\begin{table}[t]", r"\centering", r"\small",
        r"\begin{tabular}{lrrrrrrrrr}", r"\toprule",
        r" & & \multicolumn{2}{c}{\zap}"
        r" & \multicolumn{3}{c}{\fusiong}"
        r" & \multicolumn{3}{c}{\fusiona} \\",
        r"\cmidrule(lr){3-4}\cmidrule(lr){5-7}\cmidrule(lr){8-10}",
        r"Suite & \#CHCs & hb & ms"
        r" & \#reduced & $\times$hb & $\times$ms"
        r" & \#reduced & $\times$hb & $\times$ms \\",
        r"\midrule",
    ]

    # Merge the hashtable/sorting case-study suites into one row.
    case_study_rows: list[dict] = []
    for suite_name in SUITE_ORDER + [s for s in suites if s not in SUITE_ORDER]:
        suite_rows = suites.get(suite_name)
        if suite_rows is None:
            continue
        if suite_name in CASE_STUDY_SUITES:
            case_study_rows.extend(suite_rows)
            continue
        label = SUITE_MACROS_AGG.get(suite_name, esc(SUITE_DISPLAY.get(suite_name, suite_name)))
        L.append(row(label, len(suite_rows), suite_rows))

    if case_study_rows:
        L.append(row(CASE_STUDY_LABEL, len(case_study_rows), case_study_rows))

    L += [
        r"\midrule",
        row(r"\textbf{All}", len(rows), rows),
        r"\bottomrule", r"\end{tabular}",
        r"\caption{RQ2: acyclic $\kappa$-variables reduction.",
        r"\#CHCs is the number of constraints in each suite; \zap~ can reduce all of them.",
        r"For \zap, hb and ms are average heartbeats and wall-clock time (ms).",
        r"For \fusiong~ and \fusiona, \#reduced is the number of constraints reduced,",
        r"and $\times$hb/$\times$ms report average cost relative to \zap.}",
        r"\label{tab:rq2-flux-agg}",
        r"\end{table}",
    ]

    out_path.write_text("\n".join(L) + "\n")
    print(f"wrote {out_path}")


# ── LaTeX term-shape aggregate ────────────────────────────────────────────────

# Suite labels for the term-shape aggregate table (tab:rq2-flux-agg-term),
# matching lean-fixpoint-paper/sections/E-evaluation.tex — plain lowercase
# names, not the \fluxmedium/\wavesuite/... macros used in tab:rq2-flux-agg.
SUITE_DISPLAY_TERM = {
    "flux-medium":     "flux-medium",
    "wave":            "wave",
    "Flux lean-bench": "flux-tests",
    "liquid-fixpoint": "liquid-fixpoint",
}


def write_latex_term_aggregate(rows: list[dict], out_path: Path) -> None:
    def esc(s: str) -> str:
        return s.replace("_", "\\_")

    order = sorted(rows, key=lambda r: (SUITE_ORDER.index(r["suite"])
                                        if r["suite"] in SUITE_ORDER else 99,
                                        r["proof_name"]))
    suites: dict[str, list[dict]] = {}
    for r in order:
        suites.setdefault(r["suite"], []).append(r)

    def gm_abs(rs, k, field):
        return geomean([r[k][field] for r in rs if r[k]["ok"] and r[k][field]])

    def gm_ratio(rs, k, field):
        return geomean([r[k][field] / r["zap"][field] for r in rs
                        if r[k]["ok"] and r["zap"]["ok"]
                        and r[k][field] and r["zap"][field]])

    def fmt_abs(g: float) -> str:
        return f"{g:,.0f}".replace(",", "\\,") if not math.isnan(g) else "—"

    def fmt_ratio(g: float) -> str:
        return f"{g:.1f}$\\times$" if not math.isnan(g) else "—"

    def row(label: str, rs: list[dict]) -> str:
        return (f"{label}"
                f" & {fmt_abs(gm_abs(rs, 'zap', 'depth'))}"
                f" & {fmt_abs(gm_abs(rs, 'zap', 'nconst'))}"
                f" & {fmt_abs(gm_abs(rs, 'zap', 'kerus'))}"
                f" & {fmt_ratio(gm_ratio(rs, 'grind', 'depth'))}"
                f" & {fmt_ratio(gm_ratio(rs, 'grind', 'nconst'))}"
                f" & {fmt_ratio(gm_ratio(rs, 'grind', 'kerus'))}"
                f" & {fmt_ratio(gm_ratio(rs, 'aesop', 'depth'))}"
                f" & {fmt_ratio(gm_ratio(rs, 'aesop', 'nconst'))}"
                f" & {fmt_ratio(gm_ratio(rs, 'aesop', 'kerus'))}"
                r" \\")

    L: list[str] = [
        r"% Auto-generated by make_rq2_table.py — do not edit by hand.",
        r"\begin{table}[t]", r"\centering", r"\small",
        r"\begin{tabular}{lrrrrrrrrr}", r"\toprule",
        r" & \multicolumn{3}{c}{\zap~ (baseline)} & \multicolumn{3}{c}{\fusiong/\zap~ ratio}"
        r" & \multicolumn{3}{c}{\fusiona/\zap~ ratio} \\",
        r"\cmidrule(lr){2-4}\cmidrule(lr){5-7}\cmidrule(lr){8-10}",
        r"Suite & depth & \#consts & ker$\mu$s & depth & \#consts & ker$\mu$s"
        r" & depth & \#consts & ker$\mu$s \\",
        r"\midrule",
    ]

    case_study_rows: list[dict] = []
    for suite_name in SUITE_ORDER + [s for s in suites if s not in SUITE_ORDER]:
        suite_rows = suites.get(suite_name)
        if suite_rows is None:
            continue
        if suite_name in CASE_STUDY_SUITES:
            case_study_rows.extend(suite_rows)
            continue
        label = SUITE_DISPLAY_TERM.get(suite_name, esc(SUITE_DISPLAY.get(suite_name, suite_name)))
        L.append(row(label, suite_rows))

    if case_study_rows:
        L.append(row(CASE_STUDY_LABEL, case_study_rows))

    L += [
        r"\midrule",
        row(r"\textbf{All}", rows),
        r"\bottomrule", r"\end{tabular}",
        r"\caption{Elimination proof-term shape (geomean per suite). \zap~ columns "
        r"show geomean raw values; grind/aesop columns show geomean ratio vs.\ \zap~ "
        r"over jointly-solved CHCs. depth = expression-tree depth; \#consts = distinct "
        r"constants; ker$\mu$s = kernel re-check time ($\mu$s).}",
        r"\label{tab:rq2-flux-agg-term}",
        r"\end{table}",
    ]

    out_path.write_text("\n".join(L) + "\n")
    print(f"wrote {out_path}")


# ── main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--in", dest="input",
                    default=str(ROOT / "rq2_results.json"),
                    help="input JSON (default: rq2_results.json)")
    ap.add_argument("--format", choices=("markdown", "latex", "both"),
                    default="both")
    ap.add_argument("--out-md",  default=str(ROOT / "rq2_table.md"))
    ap.add_argument("--out-tex", default=str(ROOT / "rq2_table.tex"))
    ap.add_argument("--out-tex-agg", default=str(ROOT / "rq2_table_agg.tex"))
    ap.add_argument("--out-tex-term-agg", default=str(ROOT / "rq2_table_term_agg.tex"))
    ap.add_argument("--aggregate", action="store_true",
                    help="also write per-suite aggregate LaTeX table")
    ap.add_argument("--term-aggregate", action="store_true",
                    help="also write per-suite proof-term-shape aggregate LaTeX table")
    ap.add_argument("--lf-results", default=None, metavar="PATH",
                    help="path to lean-fixpoint eval/rq3_results.json "
                         "(from scripts/run_rq3.py); adds the liquid-fixpoint suite")
    args = ap.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"error: {input_path} not found — run run_fusion_experiments.py first",
              file=sys.stderr)
        return 1

    rows = load(input_path)
    print(f"loaded {len(rows)} VCs from {input_path}")

    lf_rows: list[dict] = []
    if args.lf_results:
        lf_path = Path(args.lf_results)
        if not lf_path.exists():
            print(f"error: {lf_path} not found — run scripts/run_rq3.py first",
                  file=sys.stderr)
            return 1
        lf_rows = load_lf(lf_path)
        print(f"loaded {len(lf_rows)} liquid-fixpoint benchmarks from {lf_path}")

    all_rows = rows + lf_rows

    if args.format in ("markdown", "both"):
        write_markdown(all_rows, Path(args.out_md))
    if args.format in ("latex", "both"):
        write_latex(all_rows, Path(args.out_tex))
    if args.aggregate:
        write_latex_aggregate(all_rows, Path(args.out_tex_agg))
    if args.term_aggregate:
        write_latex_term_aggregate(all_rows, Path(args.out_tex_term_agg))

    def n_ok(k):
        return sum(1 for r in all_rows if r[k]["ok"])

    def gm_slow(k):
        return geomean([r[k]["elim"] / r["zap"]["elim"] for r in all_rows
                        if r[k]["ok"] and r["zap"]["ok"] and r["zap"]["elim"]])

    print(f"\nCoverage: zap {n_ok('zap')}/{len(all_rows)}  "
          f"grind {n_ok('grind')}/{len(all_rows)}  aesop {n_ok('aesop')}/{len(all_rows)}")
    print(f"Geomean slowdown vs zap: "
          f"grind {gm_slow('grind'):.1f}×  aesop {gm_slow('aesop'):.1f}×")
    return 0


if __name__ == "__main__":
    sys.exit(main())
