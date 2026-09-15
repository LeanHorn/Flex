#!/usr/bin/env python3
"""RQ3 proof-time phase breakdown: zap / simp / PA (fixpoint) / discharge.

Every RQ3 VC is proved by the same combinator (flux-derived suites) or by
`solve_fixpoint` directly (Liquid-fixpoint) — see `scripts/rq3_instrument_phases.py`,
which turns on the (default-off) `flex.benchPhases` option and swaps the
standalone `simp [*]` step for a timed `benchSimpStar`, so that every phase
`benchPhase` (`Flex/Tactic/Utils.lean`) already times internally
(`zap`'s `sol`/`build`/`clean`, `solve_fixpoint`'s `fuse`/`pa`/`close`) shows
up in the build logs as `[phase] <tac>:<phase>=<hb> ms=<ms>` lines.

This script sums those lines per suite into four buckets:
    zap   = fusion:sol + fusion:build + fusion:clean + solve_fixpoint:fuse
    simp  = top:simp
    pa    = solve_fixpoint:pa
    close = solve_fixpoint:close

Three exclusions/splits, all reusing this repo's existing conventions rather
than inventing new ones (see make_table.py's Table 1/2 and
export_lean_bench_stats.py, which already do this for the VC-count tables):

  - A VC whose proof errors partway through (e.g. `maxRecDepth` deep inside
    PA) never reaches later `benchPhase` prints, so its record is PARTIAL.
    Every VC with an `error:` line for its own proof is dropped entirely,
    never summed in as a partial record.
  - A trivial VC (its VC-file's final `def` body is literally `True`) is
    dropped from every total, matching the non-trivial-VC convention
    `make_table.py`'s Table 1/tables.md already uses — the paper's own
    tables count non-trivial constraints, not the full generated set.
  - Non-trivial, solved VCs are further split by whether they have any
    cyclic κ (`kappa` classification: cyclic_only/both = "cyclic", none/
    acyclic_only = "acyclic") — most VCs are pure acyclic-elimination, and
    averaging them together with the (much more expensive) cyclic ones
    would hide the PA cost concentration reported elsewhere on this page.

Renders Markdown + LaTeX: a combined sum table, a combined mean-per-VC table,
and mean-per-VC tables split by κ-structure — one row per suite, matching the
existing Table 1/2 convention in `make_table.py`'s `tables.md`/`tables.tex`,
which this script does NOT modify.

Reuses `make_table.py`'s suite list / flux-medium merge membership, trivial-
VC detection, and failure detection (so these tables can't silently drift
from Table 1/2's own counts), and both `kappa_classify.py` modules' tagged/
bare-line attribution + κ-classification conventions, rather than
re-deriving any of it.

Usage:
    python3 eval_benchmarks/rq3_table/rq3_phase_table.py
    python3 eval_benchmarks/rq3_table/rq3_phase_table.py --dirs pldi_lean_proofs,Liquid-fixpoint
"""

from __future__ import annotations

import argparse
import importlib.util
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from types import ModuleType

HERE = Path(__file__).resolve().parent          # eval_benchmarks/rq3_table
EVAL_BENCH = HERE.parent                        # eval_benchmarks
REPO = EVAL_BENCH.parent

sys.path.insert(0, str(HERE))
from make_table import (  # noqa: E402
    WICK_SUITES, MERGED_SUITE_NAME, MERGED_SUITE_MEMBERS, DEFAULT_LF_ROOT,
    parse_log_failures, is_trivially_true,
)

sys.path.insert(0, str(EVAL_BENCH))
import kappa_classify as kappa_flux  # noqa: E402  (eval_benchmarks/kappa_classify.py)


def _load_module(path: Path, name: str) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


# scripts/kappa_classify.py — a DIFFERENT module from eval_benchmarks/kappa_classify.py
# despite the same filename; loaded under a distinct name to avoid clobbering
# the `kappa_flux` import above in `sys.modules['kappa_classify']`.
kappa_lf = _load_module(REPO / "scripts" / "kappa_classify.py", "_kappa_classify_lf")

# Mirrors scripts/export_stats.py's own BUILDING_RE — duplicated rather than
# imported because that module's top-level `from kappa_classify import ...`
# would resolve against whichever `kappa_classify` is already cached in
# `sys.modules` at import time, which is fragile given the two same-named
# modules above.
BUILDING_RE = re.compile(r"^\[(\d+)/(\d+)\] Building: (.+?) \.\.\. (OK|ERROR)$")

# A VC whose proof errors partway through never reaches later `benchPhase`
# prints — the exception escapes before they run — so it's dropped entirely
# (see module docstring). Mirrors `export_lean_bench_stats.py`'s own
# path-qualified error-line detection for the merged suite (verified to
# agree exactly with its "✖ Building" Lake-status lines).
MERGED_ERROR_RE = re.compile(r"^error: (\S+)/User/Proof/(\w+)Proof\.lean:\d+:\d+:", re.MULTILINE)

BUCKETS: dict[str, list[str]] = {
    "zap":   ["fusion:sol", "fusion:build", "fusion:clean", "solve_fixpoint:fuse"],
    "simp":  ["top:simp"],
    "pa":    ["solve_fixpoint:pa"],
    "close": ["solve_fixpoint:close"],
}
BUCKET_ORDER = ["zap", "simp", "pa", "close"]

Totals = dict[str, dict[str, int]]  # bucket -> {"hb": N, "ms": N}

# κ classification (none/acyclic_only/cyclic_only/both, from kappa_classify.py)
# collapses to whether the VC has ANY cyclic κ to solve at all.
KAPPA_GROUP = {"none": "acyclic", "acyclic_only": "acyclic",
               "cyclic_only": "cyclic", "both": "cyclic"}


@dataclass
class VCRecord:
    raw: dict[str, dict[str, int]]
    trivial: bool
    kgroup: str  # "acyclic" | "cyclic"


@dataclass
class SuiteRecords:
    vcs: dict[str, VCRecord] = field(default_factory=dict)
    n_failed: int = 0


def _empty_totals() -> Totals:
    return {b: {"hb": 0, "ms": 0} for b in BUCKET_ORDER}


def _add_totals(acc: Totals, other: Totals) -> None:
    for b in BUCKET_ORDER:
        acc[b]["hb"] += other[b]["hb"]
        acc[b]["ms"] += other[b]["ms"]


def _bucketize(raw: dict[str, dict[str, int]]) -> Totals:
    out = _empty_totals()
    for bucket, keys in BUCKETS.items():
        for k in keys:
            e = raw.get(k)
            if e:
                out[bucket]["hb"] += e["hb"]
                out[bucket]["ms"] += e["ms"]
    return out


def _mean_totals(totals: Totals, count: int) -> dict[str, dict[str, float]]:
    if count == 0:
        return {b: {"hb": 0.0, "ms": 0.0} for b in BUCKET_ORDER}
    return {b: {"hb": totals[b]["hb"] / count, "ms": totals[b]["ms"] / count} for b in BUCKET_ORDER}


def aggregate(recs: SuiteRecords, kgroup: str | None = None) -> tuple[Totals, int]:
    """Sum over non-trivial VCs (failed ones are never in `recs` at all),
    optionally restricted to one κ-group ("acyclic" or "cyclic")."""
    acc = _empty_totals()
    n = 0
    for rec in recs.vcs.values():
        if rec.trivial:
            continue
        if kgroup is not None and rec.kgroup != kgroup:
            continue
        _add_totals(acc, _bucketize(rec.raw))
        n += 1
    return acc, n


def n_trivial(recs: SuiteRecords) -> int:
    return sum(1 for rec in recs.vcs.values() if rec.trivial)


# ── κ-classification for the Liquid-fixpoint suite ──────────────────────────
# LF benchmarks call `solve_fixpoint` directly (occasionally after a plain
# `fusion`), reporting via `[solve_fixpoint] Acyclic/Cyclic κ:` rather than
# `[fusion] Start/End κ:` — a different pair of lines needs a different
# parser (`kappa_lf`, not `kappa_flux`). Mirrors scripts/export_stats.py's
# own `parse_log` reduction (most-complex-invocation-wins) rather than
# importing that module (see the `kappa_lf` load above for why).
def _lf_chunk_kgroup(chunk: str) -> str:
    label = "none"
    for acyclic, cyclic in kappa_lf.parse_invocations(chunk):
        l = kappa_lf.classify(acyclic, cyclic)
        if l == "both":
            return "cyclic"
        if l == "cyclic_only" and label != "both":
            label = "cyclic_only"
        elif l == "acyclic_only" and label not in ("both", "cyclic_only"):
            label = "acyclic_only"
    return KAPPA_GROUP[label]


# ── per-suite loaders ────────────────────────────────────────────────────────

def load_wick_suite_records(dir_name: str) -> SuiteRecords | None:
    log_path = HERE / f"{dir_name}.log"
    vc_dir = EVAL_BENCH / dir_name / "LeanProofs" / "Flux" / "VC"
    if not log_path.exists() or not vc_dir.is_dir():
        return None
    text = log_path.read_text(encoding="utf-8", errors="replace")

    phases_by_vc = kappa_flux.parse_phases(text)
    kappa_by_vc = kappa_flux.parse_log_kappa(text)
    failed = parse_log_failures(text)
    trivial_names = {f.stem for f in vc_dir.glob("*.lean") if is_trivially_true(f)}

    recs = SuiteRecords(n_failed=len(failed & phases_by_vc.keys()))
    for vc, raw in phases_by_vc.items():
        if vc in failed:
            continue
        recs.vcs[vc] = VCRecord(
            raw=raw, trivial=vc in trivial_names,
            kgroup=KAPPA_GROUP[kappa_by_vc.get(vc, "none")],
        )
    return recs


def load_merged_suite_records() -> SuiteRecords | None:
    log_path = HERE / "lean_bench_log.txt"
    merged_dir = EVAL_BENCH / "lean_bench_merged"
    if not log_path.exists() or not merged_dir.is_dir():
        return None
    text = log_path.read_text(encoding="utf-8", errors="replace")

    phases_by_vc = kappa_flux.parse_phases_pathed(text)
    kappa_by_vc = kappa_flux.parse_log_kappa_pathed(text)
    failed = {f"{m.group(1)}/{m.group(2)}" for m in MERGED_ERROR_RE.finditer(text)}

    trivial_keys: set[str] = set()
    for vc_path in merged_dir.rglob("Flux/VC/*.lean"):
        if not is_trivially_true(vc_path):
            continue
        rel_parts = vc_path.relative_to(merged_dir).parts
        if "Flux" not in rel_parts:
            continue
        test_id = "/".join(rel_parts[: rel_parts.index("Flux")])
        trivial_keys.add(f"{test_id}/{vc_path.stem}")

    recs = SuiteRecords(n_failed=len(failed & phases_by_vc.keys()))
    for vc, raw in phases_by_vc.items():
        if vc in failed:
            continue
        recs.vcs[vc] = VCRecord(
            raw=raw, trivial=vc in trivial_keys,
            kgroup=KAPPA_GROUP[kappa_by_vc.get(vc, "none")],
        )
    return recs


def load_lf_suite_records(lf_root: Path) -> SuiteRecords | None:
    log_path = lf_root / "lf_bench.log"
    if not log_path.exists():
        return None
    text = log_path.read_text(encoding="utf-8", errors="replace")

    recs = SuiteRecords()
    name = None
    current_lines: list[str] = []
    current_ok = True

    def _flush() -> None:
        nonlocal recs
        if name is None:
            return
        chunk = "\n".join(current_lines)
        if current_ok:
            # No trivial-VC concept for the hand-written Liquid-fixpoint suite.
            recs.vcs[name] = VCRecord(
                raw=kappa_lf.sum_phases(chunk), trivial=False,
                kgroup=_lf_chunk_kgroup(chunk),
            )
        else:
            recs.n_failed += 1

    for line in text.splitlines():
        m = BUILDING_RE.match(line)
        if m:
            _flush()
            name = m.group(3)
            current_lines = []
            current_ok = m.group(4) == "OK"
        else:
            current_lines.append(line)
    _flush()
    return recs


# ── suite assembly (mirrors make_table.py's suite list / flux-medium merge) ──

def _merge(into: SuiteRecords, other: SuiteRecords, prefix: str) -> None:
    into.n_failed += other.n_failed
    for k, v in other.vcs.items():
        into.vcs[f"{prefix}::{k}"] = v  # prefix avoids cross-suite key collisions


def build_suite_records(selected: set[str] | None) -> list[tuple[str, SuiteRecords]]:
    """One (suite_name, SuiteRecords) pair per suite, flux-medium merged."""
    out: list[tuple[str, SuiteRecords]] = []

    merged = SuiteRecords()
    have_any_merged_member = False
    for display, dir_name in WICK_SUITES:
        if selected is not None and dir_name not in selected:
            continue
        recs = load_wick_suite_records(dir_name)
        if recs is None:
            print(f"  [warning] missing data for {display} ({dir_name})", file=sys.stderr)
            continue
        if display in MERGED_SUITE_MEMBERS:
            _merge(merged, recs, display)
            have_any_merged_member = True
        else:
            out.append((display, recs))

    if have_any_merged_member:
        out.append((MERGED_SUITE_NAME, merged))

    if selected is None or "lean_bench_merged" in selected:
        recs = load_merged_suite_records()
        if recs is None:
            print("  [warning] missing lean_bench_log.txt (Flux lean-bench)", file=sys.stderr)
        else:
            out.append(("Flux lean-bench", recs))

    if selected is None or "Liquid-fixpoint" in selected:
        recs = load_lf_suite_records(DEFAULT_LF_ROOT)
        if recs is None:
            print("  [warning] missing lf_bench.log (Liquid-fixpoint)", file=sys.stderr)
        else:
            out.append(("Liquid-fixpoint", recs))

    return out


# ── rendering ────────────────────────────────────────────────────────────────

def _cell(hb: float, ms: float, mean: bool) -> str:
    if mean:
        return f"{hb:,.1f} ({ms:,.1f}ms)"
    return f"{hb:,.0f} ({ms:,.0f}ms)"


def _row_cells(totals: Totals, mean: bool) -> list[str]:
    return [_cell(totals[b]["hb"], totals[b]["ms"], mean) for b in BUCKET_ORDER]


def _row_total_cell(totals: Totals, mean: bool) -> str:
    hb = sum(totals[b]["hb"] for b in BUCKET_ORDER)
    ms = sum(totals[b]["ms"] for b in BUCKET_ORDER)
    return _cell(hb, ms, mean)


def _rows_for(suites: list[tuple[str, SuiteRecords]], mean: bool, kgroup: str | None):
    """Yield (name, n, cells[6]) per suite, plus a trailing Total row."""
    total_acc = _empty_totals()
    total_n = 0
    body = []
    for name, recs in suites:
        totals, n = aggregate(recs, kgroup)
        t = totals if not mean else _mean_totals(totals, n)
        _add_totals(total_acc, totals)
        total_n += n
        body.append((name, n, [*_row_cells(t, mean), _row_total_cell(t, mean)]))
    total_t = total_acc if not mean else _mean_totals(total_acc, total_n)
    total_row = ("Total", total_n, [*_row_cells(total_t, mean), _row_total_cell(total_t, mean)])
    return body, total_row


def render_md(suites: list[tuple[str, SuiteRecords]]) -> str:
    lines: list[str] = []

    lines += ["## Sum over all VCs (non-trivial, solved)\n",
              "| Benchmark | #VCs | triv. | fail. | zap | simp | PA (fixpoint) | "
              "discharge VC | Total |",
              "|---|--:|--:|--:|--:|--:|--:|--:|--:|"]
    body, total_row = _rows_for(suites, mean=False, kgroup=None)
    for name, n, cells in body:
        recs = dict(suites)[name]
        lines.append(f"| {name} | {n} | {n_trivial(recs)} | {recs.n_failed} | "
                     + " | ".join(cells) + " |")
    n_triv_tot = sum(n_trivial(r) for _, r in suites)
    n_fail_tot = sum(r.n_failed for _, r in suites)
    lines.append(f"| **{total_row[0]}** | {total_row[1]} | {n_triv_tot} | {n_fail_tot} | "
                 + " | ".join(f"**{c}**" for c in total_row[2]) + " |")
    lines.append("\n_Cells: heartbeats/1000 (wall-clock ms). \"triv.\" = trivial VCs "
                 "(final `def` body is `True`) excluded from every total here, matching "
                 "Table 1's non-trivial-VC convention. \"fail.\" = VCs whose proof errored, "
                 "dropped entirely rather than contributing a partial record._\n")

    lines += ["## Mean per VC (non-trivial, solved; both κ-structures)\n",
              "| Benchmark | #VCs | zap | simp | PA (fixpoint) | discharge VC | Total |",
              "|---|--:|--:|--:|--:|--:|--:|"]
    body, total_row = _rows_for(suites, mean=True, kgroup=None)
    for name, n, cells in body:
        lines.append(f"| {name} | {n} | " + " | ".join(cells) + " |")
    lines.append(f"| **{total_row[0]}** | {total_row[1]} | "
                 + " | ".join(f"**{c}**" for c in total_row[2]) + " |")
    lines.append("\n_Sum ÷ #VCs, weighted across all non-trivial solved VCs in the suite._\n")

    for kgroup, title, desc in [
        ("acyclic", "no cyclic κ (none / acyclic-only)",
         "VCs with nothing for predicate abstraction to do — `solve`'s own PA phase, if it "
         "runs at all, sees an empty cyclic set."),
        ("cyclic", "has cyclic κ (cyclic-only / both)",
         "VCs that need real fixpoint computation on at least one cyclic κ."),
    ]:
        lines += [f"## Mean per VC — {title}\n", f"_{desc}_\n",
                  "| Benchmark | #VCs | zap | simp | PA (fixpoint) | discharge VC | Total |",
                  "|---|--:|--:|--:|--:|--:|--:|"]
        body, total_row = _rows_for(suites, mean=True, kgroup=kgroup)
        for name, n, cells in body:
            lines.append(f"| {name} | {n} | " + " | ".join(cells) + " |")
        lines.append(f"| **{total_row[0]}** | {total_row[1]} | "
                     + " | ".join(f"**{c}**" for c in total_row[2]) + " |")
        lines.append("")

    return "\n".join(lines)


def render_latex(suites: list[tuple[str, SuiteRecords]]) -> str:
    def esc(s: str) -> str:
        return s.replace("_", r"\_")

    def sum_table() -> list[str]:
        lines = [
            r"\begin{table}[t]", r"\centering", r"\small",
            r"\caption{RQ3 proof-time phase breakdown, summed over non-trivial, solved VCs: "
            r"\textsc{zap} (acyclic-$\kappa$ elimination), \lean{simp}, predicate abstraction "
            r"(fixpoint computation on cyclic $\kappa$'s), and discharging the residual VC. "
            r"Cells are heartbeats/1000 (wall-clock ms). Trivial VCs and VCs whose proof "
            r"errored are excluded.}",
            r"\label{tab:rq3-phases-sum}",
            r"\begin{tabular}{lrrrrrrr}", r"\toprule",
            r"Benchmark & \#VCs & triv. & fail. & zap & simp & PA & discharge & Total \\",
            r"\midrule",
        ]
        body, total_row = _rows_for(suites, mean=False, kgroup=None)
        for name, n, cells in body:
            recs = dict(suites)[name]
            lines.append(f"{esc(name)} & {n} & {n_trivial(recs)} & {recs.n_failed} & "
                          + " & ".join(cells) + r" \\")
        n_triv_tot = sum(n_trivial(r) for _, r in suites)
        n_fail_tot = sum(r.n_failed for _, r in suites)
        lines += [
            r"\midrule",
            f"\\textbf{{{total_row[0]}}} & {total_row[1]} & {n_triv_tot} & {n_fail_tot} & "
            + " & ".join(f"\\textbf{{{c}}}" for c in total_row[2]) + r" \\",
            r"\bottomrule", r"\end{tabular}", r"\end{table}",
        ]
        return lines

    def mean_table(caption: str, label: str, kgroup: str | None) -> list[str]:
        lines = [
            r"\begin{table}[t]", r"\centering", r"\small",
            f"\\caption{{{caption}}}", f"\\label{{{label}}}",
            r"\begin{tabular}{lrrrrrr}", r"\toprule",
            r"Benchmark & \#VCs & zap & simp & PA & discharge & Total \\", r"\midrule",
        ]
        body, total_row = _rows_for(suites, mean=True, kgroup=kgroup)
        for name, n, cells in body:
            lines.append(f"{esc(name)} & {n} & " + " & ".join(cells) + r" \\")
        lines += [
            r"\midrule",
            f"\\textbf{{{total_row[0]}}} & {total_row[1]} & "
            + " & ".join(f"\\textbf{{{c}}}" for c in total_row[2]) + r" \\",
            r"\bottomrule", r"\end{tabular}", r"\end{table}",
        ]
        return lines

    lines = [r"% Auto-generated by eval_benchmarks/rq3_table/rq3_phase_table.py — do not edit by hand."]
    lines += sum_table()
    lines.append("")
    lines += mean_table(
        r"RQ3 proof-time phase breakdown, mean per non-trivial solved VC (sum $\div$ \#VCs), "
        r"both $\kappa$-structures.",
        "tab:rq3-phases-mean", kgroup=None)
    lines.append("")
    lines += mean_table(
        r"RQ3 proof-time phase breakdown, mean per VC with no cyclic $\kappa$ "
        r"(none / acyclic-only).",
        "tab:rq3-phases-mean-acyclic", kgroup="acyclic")
    lines.append("")
    lines += mean_table(
        r"RQ3 proof-time phase breakdown, mean per VC with a cyclic $\kappa$ "
        r"(cyclic-only / both).",
        "tab:rq3-phases-mean-cyclic", kgroup="cyclic")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dirs", default=None,
                     help="comma-separated subset of directory names "
                          "(flux_demo_lean_proofs,vecdeque_lean_proofs,pldi_lean_proofs,"
                          "wave_lean_proofs,lean_bench_merged,Liquid-fixpoint); default: all")
    args = ap.parse_args()
    selected = set(args.dirs.split(",")) if args.dirs else None

    suites = build_suite_records(selected)
    if not suites:
        print("No data available.", file=sys.stderr)
        return 1

    md = render_md(suites)
    tex = render_latex(suites)
    (HERE / "phase_table.md").write_text(md + "\n")
    (HERE / "phase_table.tex").write_text(tex + "\n")
    print(f"wrote {HERE / 'phase_table.md'}")
    print(f"wrote {HERE / 'phase_table.tex'}")
    print()
    print(md)
    return 0


if __name__ == "__main__":
    sys.exit(main())
