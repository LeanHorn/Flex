#!/usr/bin/env python3
"""Evaluate the main flex tactic, with optional Zap and deep Fix synthesis."""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import csv
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys

import chc_parity as common

ROOT = common.ROOT

CONFIGURATIONS = {
    "zap_se": {"label": "Zap + S/E", "zap": True, "fix": False, "se": True},
    "se": {"label": "S/E only", "zap": False, "fix": False, "se": True},
    "zap_fix": {"label": "Zap + Fix", "zap": True, "fix": True, "se": False},
    "flex": {"label": "Full Flex", "zap": True, "fix": True, "se": True},
    "fix_se": {"label": "Fix + S/E", "zap": False, "fix": True, "se": True},
}


def result_row(record: dict) -> dict:
    terminal = next((e for e in reversed(record["events"]) if e["stage"] == "result"), {})
    row = {key: record.get(key) for key in
           ("case", "configuration", "status", "wall_ms", "startup_ms", "error")}
    for field in ("flex_ms", "heartbeats", "original_predicates", "remaining_predicates",
                  "predicate_count_reduction", "goals", "all_predicates_instantiated",
                  "kernel_checked", "fully_proved", "recursion_limit", "peak_recursion_depth"):
        row[field] = terminal.get(field)
    events = record["events"]
    imports = [e for e in events if e["stage"] == "chc/import" and e["status"] == "ok"]
    certificates = [e for e in events if e["stage"] == "chc/certificate" and e["status"] == "ok"]
    row["model_obtained"] = any(e["stage"] == "chc/solver" and e["status"] == "sat" for e in events)
    row["invariants_imported"] = bool(imports)
    row["max_imported_predicates"] = max((e["predicates"] for e in imports), default=0)
    row["attempt_heads_eliminated"] = any(e.get("remaining_heads") == 0 for e in certificates)
    return row


def save(output: Path, cases: list[dict], records: list[dict],
         configurations: list[str]) -> None:
    ordered = sorted(records, key=lambda record: (record["case"], record["configuration"]))
    common.write_text(output / "results.jsonl", "".join(json.dumps(r) + "\n" for r in ordered))
    rows = [result_row(record) for record in ordered]
    if rows:
        temporary = output / "results.csv.tmp"
        with temporary.open("w", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
        temporary.replace(output / "results.csv")
    groups = {name: [row for row in rows if row["configuration"] == name]
              for name in configurations}
    common.write_json(output / "summary.json", {
        "selected_files": len(cases), "completed_runs": len(rows),
        "planned_runs": len(cases) * len(configurations),
        "by_configuration": {name: {
            "label": CONFIGURATIONS[name]["label"],
            "completed": len(group),
            "outcomes": dict(Counter(r["status"] for r in group)),
            "fully_proved": sum(r["fully_proved"] is True for r in group),
            "all_predicates_instantiated": sum(r["all_predicates_instantiated"] is True for r in group),
            "invariants_imported": sum(r["invariants_imported"] for r in group),
            "attempt_heads_eliminated": sum(r["attempt_heads_eliminated"] for r in group),
        } for name, group in groups.items()},
        "outcomes": dict(Counter(row["status"] for row in rows)),
        "fully_proved": sum(row["fully_proved"] is True for row in rows),
        "all_predicates_instantiated": sum(row["all_predicates_instantiated"] is True for row in rows),
        "predicates_removed_from_frontier": sum(row["predicate_count_reduction"] or 0 for row in rows),
        "total_wall_ms": sum(row["wall_ms"] or 0 for row in rows),
        "timing_note": "Concurrent jobs share the machine; these are not isolated latency measurements.",
    })


def freeze(output: Path, command: list[str], environment: dict) -> tuple[list[str], dict]:
    """Pin this checkout's imported artifacts so subsequent builds cannot change a run."""
    setup = json.loads((output / "lean-setup.json").read_text())
    build = ROOT / ".lake/build"
    copied = {}

    def remap(value):
        if isinstance(value, dict):
            return {key: remap(item) for key, item in value.items()}
        if isinstance(value, list):
            return [remap(item) for item in value]
        if isinstance(value, str) and value.startswith(str(build) + os.sep):
            source = Path(value)
            target = output / "compiled" / source.relative_to(build)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
            copied[str(source.relative_to(ROOT))] = common.digest(target)
            return str(target)
        return value

    common.write_json(output / "lean-setup.json", remap(setup))
    allowed = {"PATH", "LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH",
               "DYLD_LIBRARY_PATH", "DYLD_FALLBACK_LIBRARY_PATH"}
    pinned = {key: value.replace(str(build), str(output / "compiled"))
              for key, value in environment.items() if key in allowed}
    common.write_json(output / "frozen-environment.json", pinned)
    common.write_json(output / "frozen-command.json", command)
    common.write_json(output / "compiled-hashes.json", copied)
    sources = [*sorted((ROOT / "Flex").rglob("*.lean")),
               ROOT / "scripts/CHCFlex.lean", Path(__file__).resolve(),
               ROOT / "scripts/chc_parity.py", ROOT / "lean-toolchain",
               ROOT / "lake-manifest.json", ROOT / "lakefile.lean",
               *sorted((ROOT / "native").glob("chc_process.*"))]
    for source in sources:
        target = output / "source" / source.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    return command, {**environment, **pinned}


def progress(output: Path) -> None:
    summary = json.loads((output / "summary.json").read_text())
    metadata = json.loads((output / "metadata.json").read_text())
    print(f"{summary['completed_runs']}/{summary.get('planned_runs', summary['selected_files'])} completed; "
          f"complete={metadata['complete']}")
    if "by_configuration" in summary:
        for row in summary["by_configuration"].values():
            print(f"{row['label']}: {row['completed']}/{summary['selected_files']}; "
                  f"proved={row['fully_proved']}; all predicates instantiated="
                  f"{row['all_predicates_instantiated']}; outcomes={row['outcomes']}")
    else:
        print(f"Fully proved={summary['fully_proved']}; all predicates instantiated="
              f"{summary['all_predicates_instantiated']}; outcomes={summary['outcomes']}")
    for path in sorted((output / "cases").glob("**/events.jsonl")):
        if not (path.parent / "result.json").exists():
            events, _ = common.read_events(path)
            if events:
                event = events[-1]
                print(f"Active: {path.parent.relative_to(output / 'cases')}: "
                      f"{event['stage']} {event['status']}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=ROOT / "evaluation/CHC-COMP/generated")
    parser.add_argument("--manifest", type=Path,
                        help="inventory of statement-only Lean cases, instead of SMT translation manifests")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--progress", type=Path)
    parser.add_argument("--cases", nargs="+")
    parser.add_argument("--preserve-case-order", action="store_true",
                        help="Use the supplied case order for targeted diagnostics")
    parser.add_argument("--no-zap", action="store_true", help="disable only Zap; keep all other phases")
    parser.add_argument("--full-flex", action="store_true",
                        help="enable Fix with deep scraping before Spacer/Eldarica")
    parser.add_argument("--configurations", nargs="+", choices=CONFIGURATIONS,
                        help="Interleave these configurations on the same selected inputs")
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--case-timeout", type=int, default=120)
    parser.add_argument("--flex-timeout", type=int, default=30,
                        help="Shared internal Flex budget in seconds (default: 30)")
    parser.add_argument("--solver-timeout", type=int, default=30,
                        help="CHC solver cap within the shared Flex budget (default: 30)")
    parser.add_argument("--heartbeats", type=int, default=2000000)
    parser.add_argument("--proof-heartbeats", type=int, default=20000)
    parser.add_argument("--seed", type=int, default=20261101)
    parser.add_argument("--z3", default=os.environ.get("CHC_Z3", "z3"))
    parser.add_argument("--eldarica", default=os.environ.get("CHC_ELDARICA", "eld"))
    parser.add_argument("--skip-build", action="store_true")
    args = parser.parse_args()
    if args.progress:
        progress(args.progress.resolve())
        return 0
    if not args.output:
        parser.error("--output is required")
    if min(args.workers, args.case_timeout, args.heartbeats,
           args.flex_timeout, args.solver_timeout) <= 0 or args.proof_heartbeats < 0:
        parser.error("budgets and workers must be positive")
    if args.flex_timeout > args.case_timeout:
        parser.error("--flex-timeout must not exceed --case-timeout")
    if args.configurations and (args.no_zap or args.full_flex):
        parser.error("use --configurations or the legacy --no-zap/--full-flex flags, not both")
    configurations = args.configurations or [
        ("fix_se" if args.no_zap else "flex") if args.full_flex else
        ("se" if args.no_zap else "zap_se")]
    if len(set(configurations)) != len(configurations):
        parser.error("configurations must be distinct")
    args.output = args.output.resolve()
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("--output must be empty")
    if args.manifest:
        manifest_path = args.manifest.resolve()
        data = json.loads(manifest_path.read_text())
        cases = data["cases"] if isinstance(data, dict) else data
        manifests = [{"path": str(manifest_path), "sha256": common.digest(manifest_path)}]
        if not cases or len({case["case"] for case in cases}) != len(cases):
            parser.error("case manifest must contain nonempty, distinct case IDs")
        for case in cases:
            if case.get("format") != "lean_statement":
                parser.error("case manifest entries must have format=lean_statement")
            if common.digest(Path(case["generated"])) != case["generated_sha256"]:
                parser.error(f"statement hash mismatch: {case['case']}")
    else:
        cases, manifests = common.inventory(args.corpus.resolve())
    if args.cases:
        unknown = set(args.cases) - {case["case"] for case in cases}
        if unknown:
            parser.error("unknown cases: " + ", ".join(sorted(unknown)))
        cases = [case for case in cases if case["case"] in args.cases]
    if args.preserve_case_order:
        if not args.cases:
            parser.error("--preserve-case-order requires --cases")
        position = {name: i for i, name in enumerate(args.cases)}
        cases.sort(key=lambda case: position[case["case"]])
    else:
        random.Random(args.seed).shuffle(cases)
    args.output.mkdir(parents=True, exist_ok=True)
    args.mode, args.proof_timeout = "flex", 0
    # Common process-runner fields; Flex itself passes the remaining shared budget.
    args.smt_timeout = args.flex_timeout
    metadata = {
        "started_at": datetime.now(timezone.utc).isoformat(), "complete": False,
        "git_head": common.capture(["git", "rev-parse", "HEAD"]),
        "arguments": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
        "configurations": {name: CONFIGURATIONS[name] for name in configurations},
        "pipeline": "main flex; True/False preprocessing and residual automation; no nesting or postprocessing",
        "scrape": "deep when Fix is enabled",
        "candidate_policy": "Unvalidated candidates rejected by the actual flex defaults.",
        "metrics_note": "Predicate counts describe the retained frontier, including Zap. "
                        "Import and head-elimination events describe individual attempts, which "
                        "may later be rejected; only final kernel-checked results count as proofs.",
        "comparison_note": "Compare matched inputs, compiled artifacts, budgets and automation. "
                           "Concurrent timings are contended.",
    }
    common.write_json(args.output / "metadata.json", metadata)
    common.write_json(args.output / "inventory.json", {"manifests": manifests, "cases": cases})
    save(args.output, cases, [], configurations)
    header = (ROOT / "scripts/CHCFlex.lean").read_text()
    if not args.skip_build:
        subprocess.run(["lake", "--log-level=error", "build", "Flex.Tactic.Tactics.Flex"],
                       cwd=ROOT, check=True)
    setup_header = common.with_imports(header, [
        module for case in cases if case.get("generated")
        for module in re.findall(
            r"^import (.*)$", Path(case["generated"]).read_text(), re.MULTILINE)])
    command, environment = common.lean_setup(args.output, True, setup_header)
    command, environment = freeze(args.output, command, environment)
    environment["FLEX_PARITY_CASE_SECONDS"] = str(args.case_timeout)
    environment["FLEX_PARITY_FLEX_SECONDS"] = str(args.flex_timeout)
    environment["FLEX_PARITY_SOLVER_SECONDS"] = str(args.solver_timeout)
    metadata["lean_command"] = command
    metadata["lean_version"] = common.capture([command[0], "--version"])
    common.write_json(args.output / "metadata.json", metadata)
    jobs = []
    for index, case in enumerate(cases):
        offset = index % len(configurations)
        for name in configurations[offset:] + configurations[:offset]:
            jobs.append((case, name))
    common.write_json(args.output / "schedule.json", [
        {"case": case["case"], "configuration": name} for case, name in jobs])
    records, pending = [], iter(jobs)

    def run(case: dict, name: str) -> dict:
        config = CONFIGURATIONS[name]
        env = {**environment, "FLEX_PARITY_ZAP": "1" if config["zap"] else "0",
               "FLEX_PARITY_FULL": "1" if config["fix"] else "0",
               "FLEX_PARITY_SE": "1" if config["se"] else "0"}
        record = common.run_case(case, name, args, command, env, header)
        record["configuration"] = name
        common.write_json(Path(record["artifacts"]) / "result.json", record)
        return record

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        active = set()

        def submit():
            job = None if (args.output / "STOP").exists() else next(pending, None)
            if job:
                active.add(pool.submit(run, *job))

        for _ in range(args.workers):
            submit()
        while active:
            done, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in done:
                active.remove(future)
                record = future.result()
                records.append(record)
                save(args.output, cases, records, configurations)
                print(f"{len(records)}/{len(jobs)} {record['configuration']} {record['case']}: "
                      f"{record['status']} {record['wall_ms']} ms", flush=True)
                submit()
    metadata.update(complete=len(records) == len(jobs),
                    finished_at=datetime.now(timezone.utc).isoformat())
    common.write_json(args.output / "metadata.json", metadata)
    return 1 if any(r["status"] in {"runner_failed", "invalid_events", "lean_failed", "kernel_failed"}
                    for r in records) else 0


if __name__ == "__main__":
    raise SystemExit(main())
