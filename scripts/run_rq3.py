#!/usr/bin/env python3
"""RQ2 driver: acyclic-κ elimination — deterministic (fusion/Zap) vs proof search.

For each benchmark with ≥1 acyclic κ, run THREE configs on the SAME VC. Each runs
*only* the acyclic-κ elimination tactic and then leaves the rest of the VC as
`sorry`, so the measurement is purely the elimination step:

  zap   = `unfold VC; fusion;       all_goals sorry`   (deterministic proof term)
  grind = `unfold VC; fusion_grind; all_goals sorry`   (κ-head clauses via grind)
  aesop = `unfold VC; fusion_aesop; all_goals sorry`   (κ-head clauses via aesop)

`fusion_grind`/`fusion_aesop` are the isolated, eval-only tactics in
`Flex/Eval/FusionSearch.lean` (a copy of the `fusion` pipeline whose
κ-head leaves are discharged by search instead of `emitKLeaf`). If a search
variant cannot discharge a κ-head clause it ERRORS — that failure (status=FAIL)
is itself a data point.

Each config runs in its OWN `lake env lean` invocation (so the per-phase
`[phase]` lines belong unambiguously to that config). Metrics per config:
  hb, ms, depth, nconst, kerus  (from `BENCHLINE2`, see eval/Rq3Bench.lean)
  elim_hb                       (Σ of the variant's `[phase]` heartbeats =
                                 the pure acyclic-κ elimination cost)

Output: eval/rq3_results.json (consumed by rq3_plots.py) + a console table.

Usage:
    python3 scripts/run_rq3.py [--jobs 4] [--filter icfp]
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PRELUDE = REPO / "eval" / "Rq3Bench.lean"

# Subset with ≥1 acyclic κ (acyclic_only ∪ both), per benchmark_kappa_report.py.
SUBSET = (
    [("Liquid-fixpoint", b) for b in [
        "arbitrary-kvar-arg", "exists_oddity", "icfp17-ex1", "icfp17-ex2",
        "icfp17-ex3", "kut00", "mod00", "scrape03", "test02",  # acyclic_only
        "comment", "scrape02"]]                                # both
    + [("FluxRS", b) for b in [
        "Fix-Test4", "Fix-Test5", "Fix-Test7",                 # acyclic_only
        "FibMemoBoth", "Fix-Test1", "Fix-Test6",               # both
        "Quicksort"]]                                          # large, fusion-first
)

# The three configs: (key, elimination tactic). All share `all_goals sorry`.
CONFIGS = [
    ("zap",   "fusion"),
    ("grind", "fusion_grind"),
    ("aesop", "fusion_aesop"),
]

# κ-partition per benchmark (#acyclic, #cyclic). Stable benchmark facts, carried
# over so the table keeps its κ_acy/κ_cut columns without a heavy solve_fixpoint
# probe; regenerate with `scripts/benchmark_kappa_report.py` if benchmarks change.
KCOUNTS = {
    "arbitrary-kvar-arg": (2, 0), "exists_oddity": (1, 0), "icfp17-ex1": (1, 0),
    "icfp17-ex2": (2, 0), "icfp17-ex3": (3, 0), "kut00": (1, 0), "mod00": (1, 0),
    "scrape03": (1, 0), "test02": (1, 0), "comment": (5, 1), "scrape02": (2, 4),
    "Fix-Test4": (10, 0), "Fix-Test5": (4, 0), "Fix-Test7": (2, 0),
    "FibMemoBoth": (1, 1), "Fix-Test1": (1, 2), "Fix-Test6": (3, 1),
    "Quicksort": (2, 0),
}

THM_RE = re.compile(r"(?m)^theorem\s+(\w+)\s*:\s*([\w'.]+)\s*:=\s*by\b")
BL2_RE = re.compile(
    r"BENCHLINE2\s+(\S+)\s+status=(\S+)\s+hb=(\d+)\s+ms=(\d+)\s+"
    r"depth=(\d+)\s+nconst=(\d+)\s+kerus=(\d+)")
PHASE_RE = re.compile(r"\[phase\]\s+(\w+):(\w+)=(\d+)")


def prelude_body() -> str:
    # Everything below the leading `import` line (driver re-supplies imports).
    lines = PRELUDE.read_text().splitlines()
    return "\n".join(l for l in lines if not l.startswith("import"))


def sanitize(name: str) -> str:
    return re.sub(r"\W", "_", name)


def find_solver_theorem(text: str):
    """The VC theorem is the one whose proof uses the solver (not a helper
    lemma). Pick the first `theorem _ : _ := by` whose body mentions
    `solve_fixpoint`/`fusion`; this keeps any preceding helper lemmas in `head`."""
    matches = list(THM_RE.finditer(text))
    if not matches:
        return None
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        window = text[m.end(): min(end, m.end() + 400)]
        if "solve_fixpoint" in window or re.search(r"\bfusion\b", window):
            return m
    return matches[0]


def build_file(group: str, bench: str, config: str, tac: str) -> tuple[str, str]:
    """Return (lean source, theorem-name) for one config of one benchmark.

    The generated file imports the isolated eval tactics and proves the VC by
    running `tac` (the elimination) then `all_goals sorry` for the residual."""
    text = (REPO / "Benchmarks" / group / f"{bench}.lean").read_text()
    m = find_solver_theorem(text)
    if not m:
        raise RuntimeError(f"{bench}: no solver theorem found")
    vc = m.group(2)
    head = text[: m.start()]
    # Drop trailing scoped modifiers (`@[...]`, `set_option … in`) that belonged
    # to the now-removed VC theorem — else a dangling `set_option … in` swallows
    # the injected prelude's first command (e.g. its `open`).
    hlines = head.rstrip().split("\n")
    while hlines and re.match(r"^\s*(@\[.*\]|set_option .*\bin)\s*$", hlines[-1]):
        hlines.pop()
    head = "\n".join(hlines) + "\n"
    thm = f"{sanitize(bench)}_{config}"
    proof = f"by unfold {vc}; {tac}; all_goals sorry"
    src = (
        f"import Flex.Tactic.Tactics.Eval\n"   # fusion_grind / fusion_aesop
        f"{head}\n{prelude_body()}\n\n"
        f'benchx "{thm}" in\n'
        f"theorem {thm} : {vc} := {proof}\n"
    )
    return src, thm


def run_config(group: str, bench: str, config: str, tac: str) -> dict:
    src, thm = build_file(group, bench, config, tac)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=str(REPO),
                                     delete=False) as f:
        f.write(src)
        tmp = f.name
    try:
        proc = subprocess.run(["lake", "env", "lean", tmp], cwd=REPO,
                              capture_output=True, text=True)
        out = proc.stdout + proc.stderr
    finally:
        os.unlink(tmp)

    res: dict = {"config": config, "tactic": tac, "status": "FAIL",
                 "hb": None, "ms": None, "depth": None, "nconst": None,
                 "kerus": None, "phases": {}}
    bl = BL2_RE.search(out)
    if bl:
        res.update(status=bl.group(2), hb=int(bl.group(3)), ms=int(bl.group(4)),
                   depth=int(bl.group(5)), nconst=int(bl.group(6)),
                   kerus=int(bl.group(7)))
    for ptac, phase, hb in PHASE_RE.findall(out):
        k = f"{ptac}:{phase}"
        res["phases"][k] = res["phases"].get(k, 0) + int(hb)
    # Pure elimination cost = Σ of this variant's phase heartbeats (sol+build+clean).
    res["elim_hb"] = sum(res["phases"].values()) if res["phases"] else None
    if not bl and "error" in out.lower():
        res["error_excerpt"] = next(
            (l for l in out.splitlines() if "error" in l.lower()), "")[:200]
    return res


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    ap.add_argument("--filter", default=None)
    ap.add_argument("--out", default=str(REPO / "eval" / "rq3_results.json"))
    args = ap.parse_args()

    benches = [(g, b) for g, b in SUBSET if not args.filter or args.filter in b]
    tasks = [(g, b, key, tac) for g, b in benches for key, tac in CONFIGS]
    print(f"RQ2: {len(benches)} benchmarks × {len(CONFIGS)} configs "
          f"= {len(tasks)} runs ({args.jobs} parallel)\n")

    out: dict[str, dict] = {}
    for g, b in benches:
        nacy, ncyc = KCOUNTS.get(b, (None, None))
        out[b] = {"group": g, "n_acyclic": nacy, "n_cyclic": ncyc}

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(run_config, g, b, key, tac): (b, key)
                for g, b, key, tac in tasks}
        for fut in as_completed(futs):
            b, key = futs[fut]
            r = fut.result()
            out[b][key] = r
            print(f"  {b:<22} {key:<6} status={r['status']:<4} "
                  f"hb={r['hb']} elim={r['elim_hb']}", flush=True)

    Path(args.out).write_text(json.dumps(out, indent=2, ensure_ascii=False))
    print(f"\nwrote {args.out}")

    # quick console table: elimination heartbeats per variant
    print(f"\n{'benchmark':<22} {'#acy':>4} {'#cyc':>4} "
          f"{'zap':>8} {'grind':>8} {'aesop':>8}   status(z/g/a)")
    for _g, b in benches:
        row = out[b]
        def cell(k):
            c = row.get(k, {})
            e = c.get("elim_hb")
            return str(e) if e is not None else ("FAIL" if c.get("status") == "FAIL" else "—")
        st = "/".join((row.get(k, {}).get("status", "?") or "?")[0] for k in ("zap", "grind", "aesop"))
        print(f"{b:<22} {str(row['n_acyclic']):>4} {str(row['n_cyclic']):>4} "
              f"{cell('zap'):>8} {cell('grind'):>8} {cell('aesop'):>8}   {st}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
