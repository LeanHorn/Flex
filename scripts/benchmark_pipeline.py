#!/usr/bin/env python3
"""Compare end-to-end Flex pipelines or scraping modes on a frozen CHC-COMP directory.

Example: python3 scripts/benchmark_pipeline.py --suite hopv/lia/fpice \
    --output /tmp/flex-pipeline-pilot

Each case/repetition loads Lean once and runs all requested variants. Lean's
pipeline timers exclude imports and harness elaboration; startup and wall time are separate.
If a variant exceeds its hard deadline, only unstarted variants are relaunched.
No generated proof containing sorry is imported or copied into the harness.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import random
import re
import signal
import statistics
import subprocess
import time

from chc_parity import (ROOT, binary_info, capture, case_source, digest, inventory,
                        lean_setup, with_imports, write_json)


VARIANTS = ["nest_fix", "flat_fix", "nest_no_fix", "flat_no_fix", "solver_only"]
SCRAPING_MODES = {"scrape_no": "no", "scrape_basic": "basic",
                  "scrape_standard": "standard", "scrape_deep": "deep"}
COMPARISONS = {"pipeline": VARIANTS, "scraping": list(SCRAPING_MODES)}
HARNESS = ROOT / "scripts/CHCPipeline.lean"
PREFIXES = ("FLEX_PILOT_START ", "FLEX_PILOT_PHASE ", "FLEX_PILOT ")
SUCCESS = {"success", "proved", "closed", "complete"}
INFRASTRUCTURE_FAILURES = {"runner_failed", "lean_failed", "invalid_records",
                           "startup_timeout", "missing_record"}


def lean_string(value: str) -> str:
    # JSON's Unicode escape syntax differs from Lean's; preserve Unicode text.
    return json.dumps(value, ensure_ascii=False)


def assemble(case: dict, variants: list[str], header: str) -> tuple[str, str]:
    """Reuse the parity harness's manifest validation and proof-section removal."""
    source, unavailable = case_source(case, header)
    if unavailable:
        return "", unavailable
    goal = case["queries"][0]["goal_name"]
    commands = []
    for variant in variants:
        commands.append(
            f"run_elab FlexPilot.run ``{goal} {lean_string(variant)} {lean_string(case['case'])}\n")
    invocation = f"run_elab FlexParity.run (some ``{goal})"
    if source.count(invocation) != 1:
        raise ValueError("expected one generated benchmark invocation")
    return source.replace(invocation, "\n".join(commands)), ""


def kill_case(process: subprocess.Popen) -> None:
    """Kill this case's group and its own detached solver descendants only."""
    descendants = set()
    try:
        table = subprocess.run(["ps", "-axo", "pid=,ppid="], capture_output=True,
                               text=True, timeout=2, check=True).stdout
        parents = [tuple(map(int, line.split())) for line in table.splitlines()]
        descendants = {process.pid}
        while True:
            children = {pid for pid, parent in parents if parent in descendants}
            if children <= descendants:
                break
            descendants.update(children)
    except (OSError, ValueError, subprocess.SubprocessError):
        pass
    # Popen(start_new_session=True) gives this process an isolated group. Never
    # signal another group discovered in ps: it may contain unrelated processes.
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    for pid in descendants - {process.pid}:
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    process.wait()


def finite_time(value: object) -> bool:
    return (isinstance(value, (float, int)) and not isinstance(value, bool)
            and math.isfinite(value) and value >= 0)


def outcome(record: dict) -> str:
    status = record.get("status", "")
    if record.get("runner", {}).get("errors"):
        return "failure"
    if status in SUCCESS and record.get("remaining_goals") == 0:
        return "success"
    if status.startswith("partial"):
        return "partial"
    return "failure"


def failure(case: dict, variant: str, repetition: int, status: str,
            error: str, events: list[dict], **extra: object) -> dict:
    return {"case": case["case"], "variant": variant, "repetition": repetition,
            "inventory_status": case["inventory_status"], "status": status,
            "elapsed_ms": None, "remaining_goals": None, "phases": events,
            "closed_by": "", "error": error, "timing_source": "unavailable", **extra}


def monitor(command: list[str], environment: dict, path: Path,
            case: dict, variants: list[str], args: argparse.Namespace) -> dict:
    """Read the explicit progress file; Lean stdout can remain libc-buffered."""
    log_path = path.parent / "lean.log"
    progress_path = path.parent / "progress.jsonl"
    progress_path.touch()
    completed, events, starts, errors = {}, defaultdict(list), {}, []
    active, deadline_status, active_at_deadline = None, "", None
    started = time.perf_counter()
    first_start = None
    last_result = started
    received = []

    def consume(line: str) -> None:
        nonlocal active, first_start, last_result
        prefix = next((p for p in PREFIXES if line.startswith(p)), None)
        if prefix is None:
            return
        try:
            item = json.loads(line[len(prefix):])
            if not isinstance(item, dict):
                raise ValueError("JSON record must be an object")
            variant = item.get("variant")
            if item.get("case") != case["case"] or variant not in variants:
                raise ValueError("record case/variant does not match the running batch")
            received.append({"kind": prefix.strip(), "record": item})
            now = time.perf_counter()
            if prefix == "FLEX_PILOT_START ":
                if variant in starts:
                    raise ValueError(f"duplicate start marker: {variant}")
                if active is not None:
                    raise ValueError(f"new start before result for {active}")
                starts[variant] = now
                active = variant
                if first_start is None:
                    first_start = now
            elif prefix == "FLEX_PILOT_PHASE ":
                events[variant].append(item)
            else:
                if variant in completed:
                    raise ValueError(f"duplicate result: {variant}")
                if active != variant:
                    raise ValueError(f"result has no matching active start: {variant}")
                required = {"status", "elapsed_ms", "remaining_goals", "phases", "closed_by"}
                if not required <= set(item):
                    raise ValueError("result lacks required fields: " +
                                     ", ".join(sorted(required - set(item))))
                if not finite_time(item["elapsed_ms"]) or not isinstance(item["phases"], list):
                    raise ValueError("result has invalid elapsed_ms or phases")
                completed[variant] = item
                active = None
                last_result = now
        except (ValueError, TypeError) as exc:
            errors.append(str(exc))

    with log_path.open("w") as log, progress_path.open("r") as reader:
        process = subprocess.Popen([*command, str(path)], cwd=ROOT, env=environment,
                                   stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        partial = ""

        def drain() -> None:
            nonlocal partial
            partial += reader.read()
            lines = partial.split("\n")
            partial = lines.pop()
            for line in lines:
                consume(line)

        try:
            while True:
                drain()
                if process.poll() is not None:
                    drain()
                    if partial:
                        consume(partial)
                    break
                now = time.perf_counter()
                if active is not None and now - starts[active] >= args.case_timeout:
                    deadline_status, active_at_deadline = "case_timeout", active
                elif first_start is None and now - started >= args.startup_timeout:
                    deadline_status = "startup_timeout"
                elif active is None and first_start is not None and now - last_result >= args.startup_timeout:
                    deadline_status = "startup_timeout"
                if deadline_status:
                    kill_case(process)
                    drain()
                    if partial:
                        consume(partial)
                    break
                time.sleep(0.02)
        except BaseException:
            if process.poll() is None:
                kill_case(process)
            raise
    finished = time.perf_counter()
    write_json(path.parent / "emitted.json", received)
    return {"completed": completed, "events": dict(events), "errors": errors,
            "started_variants": list(starts), "active": active_at_deadline or active,
            "deadline_status": deadline_status, "exit_code": process.returncode,
            "process_wall_ms": round((finished - started) * 1000, 3),
            "startup_ms": None if first_start is None else round((first_start - started) * 1000, 3),
            "active_wall_ms": (round((finished - starts[active_at_deadline or active]) * 1000, 3)
                               if active_at_deadline or active else None),
            "artifacts": str(path.parent), "log": str(log_path)}


def run_case(case: dict, repetition: int, variants: list[str], args: argparse.Namespace,
             command: list[str], environment: dict, header: str) -> list[dict]:
    pending, records, attempt = list(variants), [], 0
    while pending:
        attempt += 1
        directory = args.output / "cases" / Path(case["case"]).with_suffix("") / f"repeat-{repetition}" / f"attempt-{attempt}"
        directory.mkdir(parents=True)
        try:
            source, unavailable = assemble(case, pending, header)
            if unavailable:
                records.extend(failure(case, v, repetition, unavailable,
                                       case.get("error") or unavailable, []) for v in pending)
                break
            path = directory / "Case.lean"
            path.write_text(source)
            env = {**environment, "FLEX_PILOT_OUTPUT": str(directory),
                   "FLEX_PILOT_CASE_SECONDS": str(math.ceil(args.case_timeout)),
                   "FLEX_PILOT_SOLVER_MS": str(round(args.solver_timeout * 1000)),
                   "FLEX_PILOT_PA_SECONDS": str(math.ceil(args.pa_timeout))}
            result = monitor(command, env, path, case, pending, args)
            write_json(directory / "process.json", result)
            runner = {k: result[k] for k in ("artifacts", "log", "process_wall_ms", "startup_ms",
                                            "exit_code", "deadline_status", "errors")}
            runner["attempt"] = attempt
            for variant in pending:
                if variant in result["completed"]:
                    record = dict(result["completed"][variant])
                    record.update(repetition=repetition, inventory_status=case["inventory_status"],
                                  timing_source="lean", phase_events=result["events"].get(variant, []),
                                  runner=runner)
                    record.setdefault("error", "")
                    records.append(record)
            remaining = [v for v in pending if v not in result["completed"]]
            if result["errors"]:
                for variant in remaining:
                    records.append(failure(case, variant, repetition, "invalid_records",
                                           "; ".join(result["errors"]),
                                           result["events"].get(variant, []), runner=runner))
                break
            active = result["active"]
            if active in remaining:
                status = result["deadline_status"] or "lean_failed"
                error = (f"hard wall-clock deadline ({args.case_timeout:g}s) exceeded" if
                         status == "case_timeout" else Path(result["log"]).read_text()[-4000:])
                extra = {"runner": runner}
                if status == "case_timeout":
                    extra.update(elapsed_ms=result["active_wall_ms"], timing_source="runner_deadline",
                                 censored=True, timeout_budget_ms=args.case_timeout * 1000)
                records.append(failure(case, active, repetition, status, error,
                                       result["events"].get(active, []), **extra))
                remaining.remove(active)
                # A timeout/crash belongs only to the active variant. Fresh Lean
                # processes give the remaining variants their full budgets.
                pending = remaining
                continue
            if remaining:
                status = result["deadline_status"] or ("lean_failed" if result["exit_code"] else "missing_record")
                error = Path(result["log"]).read_text()[-4000:] or status
                records.extend(failure(case, v, repetition, status, error,
                                       result["events"].get(v, []), runner=runner) for v in remaining)
            break
        except (OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
            finished = {r["variant"] for r in records}
            records.extend(failure(case, v, repetition, "runner_failed", str(exc), [],
                                   runner={"artifacts": str(directory)})
                           for v in pending if v not in finished)
            break
    write_json(directory.parent / "results.json", records)
    return records


def pa_diagnostics(record: dict) -> dict:
    """Keep PA measurements separate from cases closed before PA was entered."""
    phases = record.get("phases") or record.get("phase_events", [])
    phases = [p for p in phases if isinstance(p, dict)]
    named = lambda p: p.get("phase", p.get("stage", p.get("name", "")))
    fix = [p for p in phases if named(p) == "fix"]
    setups = [p for p in phases if named(p) == "fix_setup"]
    rounds = [p for p in phases if named(p) == "fix_round"]
    converged = [p for p in phases if named(p) == "fix_converged"]
    queries = [p for p in phases if named(p) == "fix_queries"]
    entered = bool(fix or setups or rounds or converged or queries)
    terminal = [p for p in fix if p.get("status") not in {"running", "started"}]
    timeout = any("timeout" in str(p.get("status", "")).lower() or
                  "timed_out" in str(p.get("status", "")).lower() or
                  "budget exhausted" in str(p.get("error", "")).lower() for p in fix)
    # A hard deadline during PA may prevent its terminal phase from being emitted.
    timeout = timeout or (entered and not terminal and record.get("status") == "case_timeout")

    def total(events: list[dict], field: str) -> int | float | None:
        values = [p[field] for p in events if finite_time(p.get(field))]
        return sum(values) if values else None

    return {
        "entered": entered, "excluded_zap_only": not entered and record.get("closed_by") == "zap",
        "converged": bool(converged), "timed_out": timeout,
        "finished": any(p.get("status") in SUCCESS | {"partial", "finished"} for p in terminal),
        "proved": any(p.get("status") in {"proved", "closed"} for p in terminal),
        "pipeline_proved_after_pa": entered and outcome(record) == "success",
        "setups": setups, "rounds": rounds,
        "initial_candidates": total(setups, "initial_candidates"),
        "surviving_candidates": total(converged, "surviving_candidates"),
        "scraped_templates": total(setups, "scraped_templates"),
        "standard_templates": total(setups, "standard_templates"),
        "tagged_templates": total(setups, "tagged_templates"),
        "queries": total(queries, "queries"), "accepted": total(queries, "accepted"),
        "oracle_ms": total(queries, "oracle_ms"),
        "warnings": [warning for p in queries for warning in p.get("warnings", [])],
    }


def summarize(records: list[dict], selected: list[dict], args: argparse.Namespace) -> dict:
    variants = {}
    by_case = defaultdict(list)
    for record in records:
        by_case[record["case"], record["variant"]].append(record)
    common_measured, common_success = [], []
    for case in selected:
        groups = [by_case[case["case"], v] for v in args.variants]
        if all(len(g) == args.repeats and all(finite_time(r.get("elapsed_ms")) and
                   not r.get("censored", False) for r in g) for g in groups):
            common_measured.append(case["case"])
            if all(outcome(r) == "success" for g in groups for r in g):
                common_success.append(case["case"])
    for variant in args.variants:
        subset = [r for r in records if r["variant"] == variant]
        times = [r["elapsed_ms"] for r in subset if finite_time(r.get("elapsed_ms"))]
        measured = [r["elapsed_ms"] for r in subset if finite_time(r.get("elapsed_ms"))
                    and not r.get("censored", False)]
        case_medians = {}
        for case in selected:
            group = by_case[case["case"], variant]
            if len(group) == args.repeats and all(finite_time(r.get("elapsed_ms")) for r in group):
                case_medians[case["case"]] = statistics.median(r["elapsed_ms"] for r in group)
        stages = defaultdict(Counter)
        for record in subset:
            # A result's phase array is authoritative. Incremental events supply
            # the last started phase when a process dies before emitting it.
            phases = record.get("phases") or record.get("phase_events", [])
            for phase in phases:
                if isinstance(phase, dict):
                    name = phase.get("phase", phase.get("stage", phase.get("name", "unknown")))
                    stages[str(name)][str(phase.get("status", "unknown"))] += 1
        counts = Counter(outcome(r) for r in subset)
        variants[variant] = {
            "runs": len(subset), "success": counts["success"], "partial": counts["partial"],
            "failure": counts["failure"], "statuses": dict(Counter(r["status"] for r in subset)),
            "closed_by": dict(Counter(r.get("closed_by") or "unclosed" for r in subset)),
            "timed_runs": len(times), "missing_times": len(subset) - len(times),
            "censored_runs": sum(bool(r.get("censored")) for r in subset),
            "median_elapsed_ms_all_timed_runs": statistics.median(times) if times else None,
            "median_elapsed_ms_uncensored_runs": statistics.median(measured) if measured else None,
            "timed_cases": len(case_medians),
            "median_case_ms": statistics.median(case_medians.values()) if case_medians else None,
            "total_case_median_ms": sum(case_medians.values()) if len(case_medians) == len(selected) else None,
            "paired_measured_total_ms": sum(case_medians[c] for c in common_measured) if common_measured else None,
            "paired_success_total_ms": sum(case_medians[c] for c in common_success) if common_success else None,
            "phases": {stage: dict(counts) for stage, counts in sorted(stages.items())},
        }
        if getattr(args, "comparison", "pipeline") == "scraping":
            diagnostics = [pa_diagnostics(r) for r in subset]
            entered = [d for d in diagnostics if d["entered"]]
            measurements = {}
            for field in ("initial_candidates", "surviving_candidates", "scraped_templates",
                          "standard_templates", "tagged_templates", "queries", "accepted", "oracle_ms"):
                values = [d[field] for d in entered if d[field] is not None]
                measurements[field] = {"measured_runs": len(values),
                                       "total": sum(values) if values else None,
                                       "median": statistics.median(values) if values else None}
            variants[variant]["pa"] = {
                **{key: sum(bool(d[key]) for d in diagnostics) for key in
                   ("entered", "excluded_zap_only", "converged", "timed_out", "finished", "proved",
                    "pipeline_proved_after_pa")},
                "measurements": measurements,
                "runs": [{"case": r["case"], "repetition": r["repetition"], **d}
                         for r, d in zip(subset, diagnostics)],
                "notes": "PA counts and candidate/query measurements exclude Zap-only runs. "
                         "Converged means a fix_converged event was observed; finished means the fix phase returned "
                         "normally (partial or proved); proved counts only proofs closed by fix. "
                         "Missing measurements remain null; surviving candidates are measured only at convergence.",
            }
    return {"selected_cases": len(selected), "expected_runs": len(selected) * len(args.variants) * args.repeats,
            "completed_runs": len(records), "variants": variants,
            "paired_measured_cases": common_measured, "paired_success_cases": common_success,
            "timing_notes": "All timed outcomes contribute to all-run medians, including failures and partials. "
                            "Hard-deadline observations are censored and marked separately. Missing times are null, never zero. "
                            "Case medians pool repetitions. Paired totals use identical case sets across all selected variants; "
                            "paired measured cases exclude censored/missing repetitions and paired success cases additionally require all proofs."}


def save_results(args: argparse.Namespace, selected: list[dict], records: list[dict]) -> None:
    ordered = sorted(records, key=lambda r: (r["case"], r["repetition"], r["variant"]))
    (args.output / "results.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in ordered))
    columns = ["case", "variant", "repetition", "status", "outcome", "elapsed_ms", "timing_source",
               "censored", "remaining_goals", "closed_by", "error", "inventory_status", "artifacts",
               "startup_ms", "process_wall_ms", "phases", "phase_events", "metrics"]
    with (args.output / "results.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=columns)
        writer.writeheader()
        for record in ordered:
            row = {key: record.get(key) for key in columns}
            row.update(outcome=outcome(record), **{k: record.get("runner", {}).get(k)
                       for k in ("artifacts", "startup_ms", "process_wall_ms")})
            for key in ("phases", "phase_events", "metrics"):
                row[key] = json.dumps(row[key], ensure_ascii=False)
            writer.writerow(row)
    write_json(args.output / "summary.json", summarize(ordered, selected, args))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--suite", required=True, help="one directory prefix, e.g. hopv/lia/fpice")
    parser.add_argument("--corpus", type=Path, default=ROOT / "evaluation/CHC-COMP/generated")
    parser.add_argument("--cases", nargs="+", help="optional exact full case IDs within --suite")
    parser.add_argument("--comparison", choices=COMPARISONS, default="pipeline")
    parser.add_argument("--variants", nargs="+", choices=VARIANTS + list(SCRAPING_MODES),
                        help="defaults to all variants in the selected comparison")
    parser.add_argument("--output", type=Path, required=True, help="fresh or empty result directory")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--repeats", type=int, default=1)
    parser.add_argument("--seed", type=int, default=20261021)
    parser.add_argument("--case-timeout", type=float, default=180, help="hard seconds per variant, excluding imports")
    parser.add_argument("--solver-timeout", type=float, default=30, help="seconds per solver call")
    parser.add_argument("--pa-timeout", type=float, default=30, help="seconds per proof-assistant stage")
    parser.add_argument("--startup-timeout", type=float, default=120, help="hard seconds for imports/harness/statements or between variants")
    parser.add_argument("--skip-build", action="store_true", help="reuse already compiled Flex dependencies")
    parser.add_argument("--inventory-only", action="store_true", help="save selection and metadata without running Lean")
    args = parser.parse_args()
    if args.variants is None:
        args.variants = list(COMPARISONS[args.comparison])
    if any(v not in COMPARISONS[args.comparison] for v in args.variants):
        parser.error("--variants must belong to the selected --comparison")
    if min(args.workers, args.repeats) < 1 or not all(math.isfinite(x) and x > 0 for x in
                (args.case_timeout, args.solver_timeout, args.pa_timeout, args.startup_timeout)):
        parser.error("workers/repeats must be positive integers and timeouts finite positive seconds")
    if round(args.solver_timeout * 1000) < 1:
        parser.error("--solver-timeout must round to at least one millisecond")
    if len(set(args.variants)) != len(args.variants) or (args.cases and len(set(args.cases)) != len(args.cases)):
        parser.error("duplicate variants or case IDs")
    suite = args.suite.strip("/")
    if not suite or args.suite.startswith("/") or any(p in {".", "..", ""} for p in suite.split("/")):
        parser.error("--suite must be one relative directory prefix")
    args.suite = suite
    args.corpus, args.output = args.corpus.resolve(), args.output.resolve()
    if args.output == args.corpus or args.corpus in args.output.parents:
        parser.error("--output must be outside the frozen corpus")
    if args.output.exists() and (not args.output.is_dir() or any(args.output.iterdir())):
        parser.error("--output must be fresh or empty; existing measurements are never overwritten")
    try:
        cases, manifests = inventory(args.corpus)
        selected = [c for c in cases if c["case"].startswith(suite + "/")]
        if args.cases:
            missing = set(args.cases) - {c["case"] for c in selected}
            if missing:
                parser.error("case IDs missing or outside --suite: " + ", ".join(sorted(missing)))
            selected = [c for c in selected if c["case"] in set(args.cases)]
        if not selected:
            parser.error("--suite selects no manifest entries")
    except (OSError, ValueError, KeyError) as exc:
        parser.error(str(exc))
    args.output.mkdir(parents=True, exist_ok=True)
    subset = [{key: c[key] for key in ("case", "source_sha256", "generated_sha256", "inventory_status")}
              for c in selected]
    rng = random.Random(args.seed)
    jobs = [(case, repetition) for repetition in range(1, args.repeats + 1) for case in selected]
    rng.shuffle(jobs)
    schedule = []
    for case, repetition in jobs:
        order = list(args.variants)
        rng.shuffle(order)
        schedule.append((case, repetition, order))
    write_json(args.output / "inventory.json", {"manifests": manifests, "selected": selected,
                                               "total_inventory_cases": len(cases)})
    write_json(args.output / "schedule.json", [{"case": c["case"], "repetition": r, "variants": v}
                                               for c, r, v in schedule])
    metadata = {
        "started_at": datetime.now(timezone.utc).isoformat(), "complete": False,
        "platform": platform.platform(), "python": platform.python_version(),
        "arguments": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
        "subset_sha256": hashlib.sha256(json.dumps(subset, sort_keys=True, separators=(",", ":")).encode()).hexdigest(),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "dependencies": json.loads((ROOT / "lake-manifest.json").read_text()),
        "git_head": capture(["git", "rev-parse", "HEAD"]),
        "git_status": capture(["git", "status", "--porcelain"]),
        "source_hashes": {str(p.relative_to(ROOT)): digest(p) for p in [Path(__file__).resolve(),
            ROOT / "scripts/chc_parity.py", HARNESS, ROOT / "scripts/CHCParity.lean",
            ROOT / "lakefile.lean", ROOT / "lake-manifest.json", ROOT / "native/chc_process.cpp",
            *sorted((ROOT / "Flex").rglob("*.lean"))]},
        "timing": "Lean reports full pipeline wall time, including each fresh solver startup. Imports, harness elaboration, and builds are excluded. "
                  "Python separately records process wall time and startup observed at the first progress.jsonl start marker (20ms polling). "
                  "The same process duration/startup is attached to each variant in that attempt and must not be summed per variant.",
        "ordering": "Seeded case/repetition and variant shuffling, no warmups. workers=1 avoids concurrent timed cases.",
        "deadline": "Each variant has its own hard case timeout; Lean and its solver descendants are terminated. "
                    "Unstarted variants are relaunched, without rerunning completed or timed-out variants.",
    }
    if args.comparison == "scraping":
        metadata["scraping_comparison"] = {
            "variant_modes": {v: SCRAPING_MODES[v] for v in args.variants},
            "pipeline": ["zap", "fix", "spacer", "eldarica", "strong_discharge"],
            "nesting": False, "oracle": "lean-auto query", "oracle_query_timeout_ms": 2000,
            "pa_timeout_seconds": args.pa_timeout,
            "cooperative_case_timeout_seconds": math.ceil(args.case_timeout),
            "hard_case_timeout_seconds": args.case_timeout,
            "solver_timeout_ms": round(args.solver_timeout * 1000),
            "candidate_measurements": "Setup and round counts are retained in phases; counts from multiple "
                                      "predicate goals are summed per run. Null round endpoints are unobserved, "
                                      "not zero. Zap-only runs are excluded from PA statistics.",
        }
    write_json(args.output / "metadata.json", metadata)
    records = []
    save_results(args, selected, records)
    print(f"Selected {len(selected)} cases from {suite}; {len(args.variants)} variants; {args.repeats} repetitions", flush=True)
    if args.inventory_only:
        return 0
    try:
        setup_started = time.perf_counter()
        if not args.skip_build:
            with (args.output / "build.log").open("w") as log:
                subprocess.run(["lake", "--log-level=error", "build", "Flex.Tactic", "Flex.CHC"],
                               cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
        imports = [module for c in selected if c["generated"] for module in
                   re.findall(r"^import (.*)$", Path(c["generated"]).read_text(), re.MULTILINE)]
        header = with_imports(HARNESS.read_text(), imports)
        command, environment = lean_setup(args.output, True, header)
        metadata.update(setup_wall_ms=round((time.perf_counter() - setup_started) * 1000, 3),
                        lean_command=command, lean_version=capture([command[0], "--version"]),
                        binaries={name: binary_info(name, ["--version"]) for name in ("z3", "cvc5")})
        write_json(args.output / "metadata.json", metadata)
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = [pool.submit(run_case, c, r, v, args, command, environment, header)
                       for c, r, v in schedule]
            for future in as_completed(futures):
                batch = future.result()
                records.extend(batch)
                save_results(args, selected, records)
                counts = dict(Counter(outcome(r) for r in batch))
                print(f"{len(records)}/{len(selected) * len(args.variants) * args.repeats} "
                      f"{batch[0]['case']} repeat={batch[0]['repetition']}: {counts}", flush=True)
        metadata["complete"] = len(records) == len(selected) * len(args.variants) * args.repeats
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        metadata["runner_error"] = str(exc)
        print(f"Runner setup/execution failed: {exc}; see {args.output}", flush=True)
    finally:
        metadata["finished_at"] = datetime.now(timezone.utc).isoformat()
        write_json(args.output / "metadata.json", metadata)
    print(f"Results: {args.output}", flush=True)
    return 1 if not metadata["complete"] or any(r["status"] in INFRASTRUCTURE_FAILURES or
                                               r.get("runner", {}).get("errors") for r in records) else 0


if __name__ == "__main__":
    raise SystemExit(main())
