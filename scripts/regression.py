#!/usr/bin/env python3
"""Regression anchor for Flex.

Compiles every benchmark / demo file individually with `lake env lean` and
reports a green ✓ (pass) or red ✗ (fail) per file. A file passes iff Lean
exits 0 and emits no `error:` diagnostics. `sorry` warnings are surfaced but
do not by themselves fail a file (use --strict-sorry to treat them as fails).

Usage:
    python3 scripts/regression.py                # check all groups
    python3 scripts/regression.py --jobs 8       # parallelism (default: cpu/2)
    python3 scripts/regression.py --filter fib   # only files whose path matches
    python3 scripts/regression.py --strict-sorry # fail files that use `sorry`
    python3 scripts/regression.py --verbose       # print first error per failure

Exit code is the number of failing files (0 = all green), so it doubles as a
CI gate.
"""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

# Resolve repo root as the parent of this script's directory.
REPO_ROOT = Path(__file__).resolve().parent.parent

GROUPS = {
    "Liquid-fixpoint": REPO_ROOT / "Benchmarks" / "Liquid-fixpoint",
    "FluxRS": REPO_ROOT / "Benchmarks" / "FluxRS",
    "Demo": REPO_ROOT / "Demo",
}

# ANSI colors; disabled when stdout is not a TTY.
_TTY = sys.stdout.isatty()


def c(code: str, s: str) -> str:
    return f"\033[{code}m{s}\033[0m" if _TTY else s


GREEN = lambda s: c("32", s)
RED = lambda s: c("31", s)
YELLOW = lambda s: c("33", s)
DIM = lambda s: c("2", s)
BOLD = lambda s: c("1", s)

TICK = GREEN("✓")
CROSS = RED("✗")

ERROR_RE = re.compile(r"^error:", re.MULTILINE)
SORRY_RE = re.compile(r"declaration uses `sorry`")


class Result:
    __slots__ = ("path", "ok", "has_sorry", "first_error", "elapsed")

    def __init__(self, path: Path, ok: bool, has_sorry: bool,
                 first_error: str | None, elapsed: float):
        self.path = path
        self.ok = ok
        self.has_sorry = has_sorry
        self.first_error = first_error
        self.elapsed = elapsed


def check_file(path: Path, strict_sorry: bool) -> Result:
    start = time.monotonic()
    # Flex is mathlib-free: every file compiles with plain `lake env lean`.
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    elapsed = time.monotonic() - start
    out = proc.stdout + proc.stderr

    has_sorry = bool(SORRY_RE.search(out))
    error_match = ERROR_RE.search(out)
    has_error = proc.returncode != 0 or error_match is not None

    first_error = None
    if has_error:
        # Grab the first error line + a little context for --verbose.
        for line in out.splitlines():
            if line.startswith("error:") or ": error:" in line:
                first_error = line.strip()
                break
        if first_error is None:
            first_error = f"exit code {proc.returncode}"
    elif strict_sorry and has_sorry:
        first_error = "uses `sorry` (--strict-sorry)"  # so --verbose shows why

    ok = not has_error and not (strict_sorry and has_sorry)
    return Result(path, ok, has_sorry, first_error, elapsed)


def main() -> int:
    ap = argparse.ArgumentParser(description="Flex regression anchor")
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2),
                    help="parallel lean processes (default: cpu/2)")
    ap.add_argument("--filter", default=None,
                    help="only check files whose path contains this substring")
    ap.add_argument("--strict-sorry", action="store_true",
                    help="treat `sorry` usage as a failure")
    ap.add_argument("--verbose", action="store_true",
                    help="print the first error line for each failing file")
    args = ap.parse_args()

    # Collect files per group, sorted for stable output.
    jobs: list[tuple[str, Path]] = []
    for group, directory in GROUPS.items():
        if not directory.is_dir():
            print(YELLOW(f"! {group}: directory not found ({directory})"))
            continue
        for f in sorted(directory.glob("*.lean")):
            if args.filter and args.filter not in str(f):
                continue
            jobs.append((group, f))

    if not jobs:
        print(YELLOW("No files to check."))
        return 0

    print(BOLD(f"Running {len(jobs)} file(s) with {args.jobs} parallel job(s)...\n"))

    results: dict[Path, Result] = {}
    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futures = {
            ex.submit(check_file, path, args.strict_sorry): (group, path)
            for group, path in jobs
        }
        for fut in as_completed(futures):
            res = fut.result()
            results[res.path] = res

    total_fail = 0
    total_sorry = 0
    for group, directory in GROUPS.items():
        group_jobs = [p for g, p in jobs if g == group]
        if not group_jobs:
            continue
        print(BOLD(f"{group}/"))
        for path in group_jobs:
            res = results[path]
            name = path.name
            timing = DIM(f"{res.elapsed:5.1f}s")
            if res.ok:
                tag = ""
                if res.has_sorry:
                    tag = YELLOW(" (sorry)")
                    total_sorry += 1
                print(f"  {TICK} {name:<40} {timing}{tag}")
            else:
                total_fail += 1
                if res.has_sorry:
                    total_sorry += 1
                print(f"  {CROSS} {name:<40} {timing}")
                if args.verbose and res.first_error:
                    print(DIM(f"      {res.first_error}"))
        print()

    passed = len(jobs) - total_fail
    summary = f"{passed}/{len(jobs)} passed"
    if total_fail:
        print(BOLD(RED(f"{CROSS} {summary} — {total_fail} failing")))
    else:
        print(BOLD(GREEN(f"{TICK} {summary} — all green")))
    if total_sorry:
        print(YELLOW(f"  ({total_sorry} file(s) use `sorry`)"))

    return min(total_fail, 255)  # exit status wraps mod 256: 256 failures would read as 0


if __name__ == "__main__":
    sys.exit(main())
