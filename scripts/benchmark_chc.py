#!/usr/bin/env python3
"""Benchmark CHC-generated witnesses on demo goals or a translated CHC corpus.

Corpus parity: benchmark_chc.py --corpus PATH --output /tmp/chc-parity
Use --corpus PATH --help for corpus selection, budgets, and solver options.

Demo mode runs serially after building dependencies. Each case/backend has an unreported
warm-up, followed by shuffled measured repetitions. Lean imports and builds are
outside the timers; each solver call includes starting a fresh process.
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import shutil
import signal
import statistics
import subprocess
import sys
import tempfile
import threading


ROOT = Path(__file__).resolve().parents[1]
BASIC = [f"ex{i}" for i in range(1, 15)] + [
    "ex_nat", "ex_bool", "ex_pair", "ex_prod", "ex_userfn", "ex_stress"]
CYCLIC = ["cyc0"] + [f"Mixed.{name}" for name in [
    "seededCountdown", "mergingSeeds", "strideTwo", "independentLoops",
    "chainedSeed", "counterAndAccumulator", "cyclicBeforeSeed"]]
BACKENDS = ["fix", "spacer", "eldarica"]
PHASES = ["prepare", "export", "solver", "import", "certificate", "kernel", "fix"]
OBLIGATION_COUNTS = ["remaining_heads", "remaining_queries", "proved_heads", "proved_queries"]


def version(command: list[str]) -> str:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True,
                            timeout=30, check=True)
    return (result.stdout or result.stderr).splitlines()[0]


def run_fields(record: dict) -> dict:
    phases = record["phases_ns"]
    return {
        "group": "Basic" if record["case"] in BASIC else "Cyclic",
        "case": record["case"], "backend": record["backend"],
        "repetition": record["repetition"], "warmup": record["repetition"] == 0,
        "success": record["success"],
        "status": ("proved" if record["success"] else
                   "partial_vcs" if record.get("result_kind") == "partial" else
                   record["stage"] + "_failed"),
        "solver_status": record.get("solver_status", ""),
        "pipeline_ms": (record["total_ns"] - phases.get("describe", 0)) / 1e6,
        "process_ms": record.get("process_elapsed_ms") if record.get("solver_status") != "not_run" else None,
        **{phase + "_ms": phases[phase] / 1e6 for phase in PHASES if phase in phases},
        "relations": record["relations"], "clauses": record["clauses"],
        **{name: record.get(name) for name in OBLIGATION_COUNTS},
        "axioms": ";".join(record["axioms"]),
        "error": " ".join(record["error"].split())[:1000],
    }


def summarize(records: list[dict], expected_runs: int | None = None) -> list[dict]:
    result = []
    measured = [run_fields(r) for r in records if r["repetition"] > 0]
    for case, backend in sorted({(r["case"], r["backend"]) for r in measured}):
        runs = [r for r in measured if (r["case"], r["backend"]) == (case, backend)]
        row = {key: runs[0][key] for key in
               ["group", "case", "backend", "relations", "clauses"]}
        row.update(runs=len(runs), successes=sum(r["success"] for r in runs),
                   status=";".join(sorted({r["status"] for r in runs})),
                   solver_status=";".join(sorted({r["solver_status"] for r in runs})),
                   error=next((r["error"] for r in runs if r["error"]), ""))
        # Report the largest residual across repetitions, so nondeterministic
        # partial results never appear more complete than an observed run.
        for name in OBLIGATION_COUNTS:
            values = [r[name] for r in runs if r[name] is not None]
            if values:
                row[name] = max(values) if name.startswith("remaining_") else min(values)
        # Failed/unsupported cases have no successful runtime or speedup.
        if all(r["success"] for r in runs) and (expected_runs is None or len(runs) == expected_runs):
            times = [r["pipeline_ms"] for r in runs]
            row.update(median_ms=statistics.median(times), min_ms=min(times), max_ms=max(times))
            if all(r["process_ms"] is not None for r in runs):
                row["process_ms"] = statistics.median(r["process_ms"] for r in runs)
            for phase in PHASES:
                key = phase + "_ms"
                if all(key in r for r in runs):
                    row[key] = statistics.median(r[key] for r in runs)
        result.append(row)
    baselines = {r["case"]: r["median_ms"] for r in result
                 if r["backend"] == "fix" and "median_ms" in r}
    for row in result:
        if row["case"] in baselines and "median_ms" in row:
            row["speedup_vs_fix"] = baselines[row["case"]] / row["median_ms"]
    return result


def write_csv(path: Path, rows: list[dict], fields: list[str]) -> None:
    with path.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def save_results(output: Path, records: list[dict], metadata: dict) -> None:
    summary_fields = ["group", "case", "backend", "runs", "successes", "status",
                      "solver_status", "relations", "clauses", "median_ms", "min_ms",
                      "max_ms", "process_ms"] + [p + "_ms" for p in PHASES] + OBLIGATION_COUNTS + ["speedup_vs_fix", "error"]
    write_csv(output, summarize(records, metadata["repeats"]), summary_fields)
    run_columns = ["group", "case", "backend", "repetition", "warmup", "success",
                   "status", "solver_status", "pipeline_ms", "process_ms"] + [p + "_ms" for p in PHASES]
    run_columns += ["relations", "clauses"] + OBLIGATION_COUNTS + ["axioms", "error"]
    write_csv(output.with_name(output.stem + "_runs.csv"),
              [run_fields(r) for r in records], run_columns)
    # Keep only three illustrative models instead of retaining every transcript.
    witnesses = {}
    for record in records:
        if record["success"] and record["case"] in ["cyc0", "Mixed.counterAndAccumulator", "ex_stress"]:
            if record["witnesses"]:
                witnesses.setdefault(record["case"] + "/" + record["backend"], record["witnesses"])
    metadata["example_witnesses"] = witnesses
    output.with_suffix(".metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")


def main() -> int:
    if any(arg == "--corpus" or arg.startswith("--corpus=") for arg in sys.argv[1:]):
        from chc_parity import main as parity_main
        return parity_main()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases", nargs="+", choices=BASIC + CYCLIC, default=BASIC + CYCLIC)
    parser.add_argument("--backends", nargs="+", choices=BACKENDS, default=BACKENDS)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--seed", type=int, default=20261011)
    parser.add_argument("--timeout", type=float, default=600, help="whole batch deadline, seconds")
    parser.add_argument("--eldarica", default=os.environ.get("CHC_ELDARICA", "eld"))
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--output", type=Path, default=ROOT / "eval/chc_results.csv")
    args = parser.parse_args()
    if args.repeats < 1 or args.timeout <= 0:
        parser.error("--repeats and --timeout must be positive")
    if len(set(args.cases)) != len(args.cases) or len(set(args.backends)) != len(args.backends):
        parser.error("--cases and --backends must not contain duplicates")
    if "eldarica" in args.backends and not shutil.which(args.eldarica):
        parser.error("Eldarica not found; provide --eldarica /path/to/eld or select --backends fix spacer")
    if not args.skip_build:
        subprocess.run(["lake", "--log-level=error", "build", "Flex.CHC", "Demo.Basic", "Demo.Fix"],
                       cwd=ROOT, check=True)
    metadata = {
        "started_at": datetime.now(timezone.utc).isoformat(),
        "platform": platform.platform(), "lean": version(["lake", "env", "lean", "--version"]),
        "z3": version(["z3", "--version"]) if "spacer" in args.backends else None,
        "eldarica": version([args.eldarica, "-h"]) if "eldarica" in args.backends else None,
        "eldarica_executable": args.eldarica, "repeats": args.repeats, "warmups": 1,
        "seed": args.seed, "cases": args.cases, "backends": args.backends,
        "solver_timeout_ms": 10000, "batch_timeout_seconds": args.timeout,
        "timing": "serial in-process Lean wall time, including fresh solver startup and kernel audit; excludes imports, builds, witness pretty printing",
        "chc_pipeline": "Flex.CHC.solveGoal with proof oracle first | omega | grind; partial VCs are not counted as proofs",
        "obligation_summary": "maximum remaining and minimum proved obligations across measured repetitions",
        "baseline": "zap followed by fix with the standard qualifier bank, then grind for residual goals; imports Demo.Basic and Demo.Fix",
        "sources_sha256": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                           for name in ["Demo/Basic.lean", "Demo/Fix.lean", "eval/CHCCases.lean",
                                        "scripts/benchmark_chc.py", "lake-manifest.json", "lakefile.lean",
                                        "Flex/CHC/Process.lean", "Flex/CHC/Native.lean",
                                        "Flex/CHC/Backend.lean", "Flex/CHC/Goal.lean",
                                        "Flex/CHC/Certificate.lean", "Flex/CHC/Normalize.lean",
                                        "Flex/CHC/Export.lean",
                                        "Flex/CHC/Witness.lean",
                                        "native/chc_process.cpp"]},
        "complete": False,
    }
    rng = random.Random(args.seed)
    commands = []
    for repetition in range(args.repeats + 1):
        tasks = [(case, backend) for case in args.cases for backend in args.backends]
        rng.shuffle(tasks)
        commands.extend(f'chc_case {case} "{backend}" {repetition}' for case, backend in tasks)
    source = (ROOT / "eval/CHCCases.lean").read_text() + "\n" + "\n".join(commands) + "\n"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    records = []
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", prefix="chc_bench_",
                                     dir=ROOT / "eval", delete=False) as handle:
        handle.write(source)
        path = Path(handle.name)
    timed_out = threading.Event()
    try:
        proc = subprocess.Popen(["lake", "--log-level=error", "lean", str(path)], cwd=ROOT,
                                env={**os.environ, "CHC_ELDARICA": args.eldarica}, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)

        def terminate() -> None:
            timed_out.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

        timer = threading.Timer(args.timeout, terminate)
        timer.start()
        try:
            for line in proc.stdout:
                if not line.startswith("CHC_RESULT "):
                    print(line, end="", flush=True)
                    continue
                record = json.loads(line.removeprefix("CHC_RESULT "))
                records.append(record)
                row = run_fields(record)
                label = "warmup" if row["warmup"] else f"run {row['repetition']}"
                print(f"{label:6} {row['case']:10} {row['backend']:8} {row['status']:14} "
                      f"{row['pipeline_ms']:9.2f} ms", flush=True)
            code = proc.wait()
        finally:
            timer.cancel()
            if proc.poll() is None:
                terminate()
                proc.wait()
        metadata.update(complete=code == 0 and len(records) == len(commands),
                        exit_code=code, timed_out=timed_out.is_set(), received=len(records),
                        expected=len(commands))
        save_results(args.output, records, metadata)
        for backend in args.backends:
            rows = [r for r in summarize(records, args.repeats) if r["backend"] == backend]
            proved = sum(r["successes"] == args.repeats and r["runs"] == args.repeats for r in rows)
            print(f"{backend}: {proved}/{len(args.cases)} cases proved in every measured repetition")
        print(f"Results: {args.output}")
        return 0 if metadata["complete"] else 1
    finally:
        path.unlink()


if __name__ == "__main__":
    raise SystemExit(main())
