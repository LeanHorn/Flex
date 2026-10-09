#!/usr/bin/env python3
"""Run all Liquid-fixpoint benchmarks and classify kappa usage in each.

For every .lean file in Benchmarks/Liquid-fixpoint/ (and optionally
Benchmarks/FluxRS/ and Demo/) this script:
  1. Runs `lake env lean -Dflex.benchPhases=true <file>` (the option makes
     solve_fixpoint print its κ lines) and captures stdout+stderr.
  2. Passes the output through the kappa classifier.
  3. Prints a summary table.

Usage:
    python3 scripts/benchmark_kappa_report.py
    python3 scripts/benchmark_kappa_report.py --jobs 8
    python3 scripts/benchmark_kappa_report.py --filter icfp
    python3 scripts/benchmark_kappa_report.py --all-groups
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

# Allow importing kappa_classify from the same directory.
sys.path.insert(0, str(Path(__file__).resolve().parent))
from kappa_classify import parse_invocations, classify  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parent.parent

GROUPS = {
    "Liquid-fixpoint": REPO_ROOT / "Benchmarks" / "Liquid-fixpoint",
    "FluxRS":          REPO_ROOT / "Benchmarks" / "FluxRS",
    "Demo":            REPO_ROOT / "Demo",
}

# ── ANSI helpers ────────────────────────────────────────────────────────────
_TTY = sys.stdout.isatty()


def c(code: str, s: str) -> str:
    return f"\033[{code}m{s}\033[0m" if _TTY else s


GREEN  = lambda s: c("32", s)
YELLOW = lambda s: c("33", s)
CYAN   = lambda s: c("36", s)
DIM    = lambda s: c("2",  s)
BOLD   = lambda s: c("1",  s)

LABEL_COLOR = {
    "none":          DIM,
    "acyclic_only":  GREEN,
    "cyclic_only":   YELLOW,
    "both":          lambda s: c("35", s),  # magenta
    "error":         lambda s: c("31", s),  # red
}

# ── per-file work ────────────────────────────────────────────────────────────

def run_file(path: Path) -> dict:
    start = time.monotonic()
    proc = subprocess.run(
        ["lake", "env", "lean", "-Dflex.benchPhases=true", str(path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    elapsed = time.monotonic() - start
    output = proc.stdout + proc.stderr

    # Lean exits non-zero on any error; a crash may print no `error:` at all.
    error = proc.returncode != 0
    invocations = [] if error else parse_invocations(output)

    # per-category tally across all invocations in this file
    tally: dict[str, int] = {"none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0}
    for acyclic, cyclic in invocations:
        tally[classify(acyclic, cyclic)] += 1

    return {
        "path":        path,
        "error":       error,
        "invocations": invocations,
        "tally":       tally,
        "elapsed":     elapsed,
    }


# ── main ────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description="Benchmark kappa classification report")
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2),
                    help="parallel lean processes (default: cpu/2)")
    ap.add_argument("--filter", default=None,
                    help="only check files whose path contains this substring")
    ap.add_argument("--all-groups", action="store_true",
                    help="also check FluxRS and Demo groups (default: Liquid-fixpoint only)")
    args = ap.parse_args()

    selected_groups = list(GROUPS.items()) if args.all_groups else [
        ("Liquid-fixpoint", GROUPS["Liquid-fixpoint"])
    ]

    jobs: list[tuple[str, Path]] = []
    for group, directory in selected_groups:
        if not directory.is_dir():
            print(YELLOW(f"! {group}: directory not found ({directory})"))
            continue
        for f in sorted(directory.glob("*.lean")):
            if args.filter and args.filter not in str(f):
                continue
            jobs.append((group, f))

    if not jobs:
        print(YELLOW("No files found."))
        return 0

    print(BOLD(f"Running {len(jobs)} benchmark(s) with {args.jobs} parallel job(s)...\n"))

    results: dict[Path, dict] = {}
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futures = {ex.submit(run_file, path): path for _, path in jobs}
        done = 0
        for fut in as_completed(futures):
            res = fut.result()
            results[res["path"]] = res
            done += 1
            n = len(res["invocations"])
            tag = "error" if res["error"] else f"{n} invocation{'s' if n != 1 else ''}"
            print(f"  [{done}/{len(jobs)}] {res['path'].name} → {tag}", flush=True)

    print()

    # ── summary table ────────────────────────────────────────────────────────
    # global tally across all invocations in all files
    global_tally: dict[str, int] = {"none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0}
    total_errors = 0

    for group, directory in selected_groups:
        group_paths = [p for g, p in jobs if g == group]
        if not group_paths:
            continue
        print(BOLD(f"{group}/"))
        col_w = max(len(p.name) for p in group_paths) + 2
        for path in group_paths:
            res = results[path]
            timing = DIM(f"{res['elapsed']:5.1f}s")
            if res["error"]:
                total_errors += 1
                color = LABEL_COLOR["error"]
                print(f"  {path.name:<{col_w}} {color(f'error         ')}{timing}")
                continue

            tally = res["tally"]
            n_inv = len(res["invocations"])
            for label, cnt in tally.items():
                global_tally[label] += cnt

            # build a compact per-file tally string, e.g. "3× none  1× acyclic_only"
            parts = [
                f"{cnt}× {label}"
                for label, cnt in tally.items()
                if cnt > 0
            ]
            # "none" is a category (a call with no κs), so say so when there is no call.
            tally_str = "  ".join(parts) if parts else "no solve_fixpoint call"

            # color by the "most interesting" category present
            dominant = next(
                (label for label in ("both", "cyclic_only", "acyclic_only", "none")
                 if tally.get(label, 0) > 0),
                "none",
            )
            color = LABEL_COLOR.get(dominant, str)
            inv_tag = DIM(f"({n_inv} inv)")
            print(f"  {path.name:<{col_w}} {color(f'{tally_str:<30}')}{timing} {inv_tag}")
        print()

    # ── totals ───────────────────────────────────────────────────────────────
    total_inv = sum(global_tally.values())
    print(BOLD(f"Summary  ({total_inv} total solve_fixpoint invocation(s)):"))
    for label in ("none", "acyclic_only", "cyclic_only", "both"):
        n = global_tally[label]
        if n == 0:
            continue
        color = LABEL_COLOR.get(label, str)
        pct = 100 * n / total_inv if total_inv else 0
        print(f"  {color(f'{label:<14}')} {n:>4}  ({pct:.0f}%)")
    if total_errors:
        color = LABEL_COLOR["error"]
        print(f"  {color(f'error         ')} {total_errors:>4}  (files that failed to compile)")

    return min(total_errors, 255)  # exit status wraps mod 256: 256 errors would read as 0


if __name__ == "__main__":
    sys.exit(main())
