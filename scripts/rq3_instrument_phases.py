#!/usr/bin/env python3
"""Bulk-instrument RQ3 benchmark fixtures to emit per-phase timing.

Two independent proof shapes get patched:

  1. Flux-derived suites (`eval_benchmarks/{lean_bench_merged,flux_demo_lean_proofs,
     vecdeque_lean_proofs,pldi_lean_proofs,wave_lean_proofs}`): every generated
     `*Proof.lean` proves its VC with the identical combinator

         (try zap) ; (try simp [*]) ; (try solve)

     `zap` and `solve` are already instrumented via `benchPhase` (see
     `Flex/Tactic/Utils.lean`); only the standalone `simp [*]` step is not. This
     script swaps it for `benchSimpStar` (a `benchPhase`-timed `simp [*]`,
     `Flex/Tactic/Tactics/Zap.lean`) and turns on the (default-off)
     `flex.benchPhases` option for that file.

  2. The Liquid-fixpoint suite (`Benchmarks/Liquid-fixpoint/*.lean`) calls
     `solve_fixpoint` directly with no separate top-level zap/simp step — it
     only needs `flex.benchPhases` turned on.

Idempotent: files already patched (option already present / tactic already
swapped) are left alone and reported as "skipped (already patched)". A file
that contains neither the expected pattern nor evidence of already being
patched is reported as "unrecognized" rather than silently skipped, so an
unexpected variant surfaces instead of being missed.

Usage:
    python3 scripts/rq3_instrument_phases.py --dirs pldi_lean_proofs,Liquid-fixpoint
    python3 scripts/rq3_instrument_phases.py --dry-run
    python3 scripts/rq3_instrument_phases.py            # all suites
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

FLUX_TACTIC_OLD = "(try zap) ; (try simp [*]) ; (try solve)"
FLUX_TACTIC_NEW = "(try zap) ; (try benchSimpStar) ; (try solve)"
BENCH_OPTION = "set_option flex.benchPhases true"

# name -> (root dir, glob, kind)
FLUX_SUITES = {
    name: (REPO / "eval_benchmarks" / name, "**/*.lean")
    for name in (
        "lean_bench_merged",
        "flux_demo_lean_proofs",
        "vecdeque_lean_proofs",
        "pldi_lean_proofs",
        "wave_lean_proofs",
    )
}
LF_SUITE = ("Liquid-fixpoint", REPO / "Benchmarks" / "Liquid-fixpoint", "*.lean")

ALL_SUITE_NAMES = list(FLUX_SUITES) + [LF_SUITE[0]]


def patch_flux_file(text: str) -> tuple[str, str]:
    """Return (new_text, status) for a flux-suite Proof.lean."""
    if FLUX_TACTIC_NEW in text and BENCH_OPTION in text:
        return text, "skipped (already patched)"
    if FLUX_TACTIC_OLD not in text:
        return text, "unrecognized (tactic pattern not found)"

    lines = text.splitlines(keepends=True)
    out: list[str] = []
    inserted_option = BENCH_OPTION in text
    patched_tactic = False
    for line in lines:
        if not inserted_option and line.lstrip().startswith("#time def "):
            indent = line[: len(line) - len(line.lstrip())]
            out.append(f"{indent}{BENCH_OPTION}\n")
            inserted_option = True
        if FLUX_TACTIC_OLD in line:
            line = line.replace(FLUX_TACTIC_OLD, FLUX_TACTIC_NEW)
            patched_tactic = True
        out.append(line)

    if not patched_tactic:
        return text, "unrecognized (tactic pattern not found)"
    return "".join(out), "patched"


def patch_lf_file(text: str) -> tuple[str, str]:
    """Return (new_text, status) for a Liquid-fixpoint benchmark file."""
    if BENCH_OPTION in text:
        return text, "skipped (already patched)"

    lines = text.splitlines(keepends=True)
    out: list[str] = []
    inserted = False
    for line in lines:
        if not inserted and line.lstrip().startswith("theorem "):
            indent = line[: len(line) - len(line.lstrip())]
            out.append(f"{indent}{BENCH_OPTION}\n")
            inserted = True
        out.append(line)

    if not inserted:
        return text, "unrecognized (no `theorem` line found)"
    return "".join(out), "patched"


def run(name: str, root: Path, glob: str, patch_fn, dry_run: bool) -> dict[str, int]:
    counts: dict[str, int] = {}
    if not root.is_dir():
        print(f"  [warning] {name}: missing dir {root}", file=sys.stderr)
        return counts
    for f in sorted(root.glob(glob)):
        if not f.is_file():
            continue
        text = f.read_text(encoding="utf-8", errors="replace")
        new_text, status = patch_fn(text)
        counts[status] = counts.get(status, 0) + 1
        if status == "patched" and not dry_run:
            f.write_text(new_text, encoding="utf-8")
    return counts


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dirs", default=None,
                     help=f"comma-separated subset of {ALL_SUITE_NAMES} (default: all)")
    ap.add_argument("--dry-run", action="store_true",
                     help="report what would change without writing files")
    args = ap.parse_args()

    selected = set(args.dirs.split(",")) if args.dirs else set(ALL_SUITE_NAMES)
    unknown = selected - set(ALL_SUITE_NAMES)
    if unknown:
        print(f"error: unknown suite(s) {sorted(unknown)}; choose from {ALL_SUITE_NAMES}",
              file=sys.stderr)
        return 1

    total_patched = 0
    for name, (root, glob) in FLUX_SUITES.items():
        if name not in selected:
            continue
        counts = run(name, root, glob, patch_flux_file, args.dry_run)
        total_patched += counts.get("patched", 0)
        print(f"{name}: " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))

    if LF_SUITE[0] in selected:
        name, root, glob = LF_SUITE
        counts = run(name, root, glob, patch_lf_file, args.dry_run)
        total_patched += counts.get("patched", 0)
        print(f"{name}: " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))

    verb = "would be" if args.dry_run else "were"
    print(f"\n{total_patched} file(s) {verb} patched.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
