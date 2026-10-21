#!/usr/bin/env python3
"""Compare native CHC solving, Flex export, and Lean certification on a corpus.

Invoked through benchmark_chc.py --corpus PATH. Results and solver transcripts
go into a fresh --output directory; the generated corpus is never modified.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
STAGES = ("native_prepare", "native_solver", "prepare", "export", "solver", "import",
          "certificate", "kernel")
DEFINITE = {"sat", "unsat"}


def digest(path: Path) -> str | None:
    return hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def retry_unproved(path: Path) -> tuple[set[str], dict]:
    """Retry inputs without a checked proof or a native/exported unsat answer."""
    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        required = {"case", "backend", "status", "kernel_status", "native_status", "flex_status"}
        if not required <= set(reader.fieldnames or []):
            raise ValueError("retry results are missing required columns")
        rows = list(reader)
    seen, cases, proved, sat, unsat = set(), set(), set(), set(), set()
    for row in rows:
        case, backend = row["case"], row["backend"]
        if not case or backend not in {"spacer", "eldarica"} or (case, backend) in seen:
            raise ValueError(f"invalid or duplicate retry result: {case!r}, {backend!r}")
        seen.add((case, backend))
        cases.add(case)
        if row["status"] == "proved" and row["kernel_status"] == "ok":
            proved.add(case)
        if "sat" in {row["native_status"], row["flex_status"]}:
            sat.add(case)
        if "unsat" in {row["native_status"], row["flex_status"]}:
            unsat.add(case)
    if proved & unsat:
        raise ValueError("retry results contain both a checked proof and an unsat answer: " +
                         ", ".join(sorted(proved & unsat)))
    if sat & unsat:
        raise ValueError("retry results contain conflicting sat/unsat answers: " +
                         ", ".join(sorted(sat & unsat)))
    selected = cases - proved - unsat
    return selected, {"results": str(path.resolve()), "sha256": digest(path),
                      "previous_inputs": len(cases), "excluded_proved": len(proved),
                      "excluded_unsat": len(unsat), "selected_inputs": len(selected)}


def inventory(corpus: Path) -> tuple[list[dict], list[dict]]:
    """Retain manifest failures and absent artifacts instead of shrinking coverage."""
    cases, manifests, seen = [], [], set()
    for path in sorted(corpus.glob("*-manifest.json")):
        manifest = json.loads(path.read_text())
        files = manifest["files"]
        if len(files) != manifest["total"]:
            raise ValueError(f"{path.name}: total differs from file inventory")
        manifests.append({"path": str(path), "sha256": digest(path),
                          "total": manifest["total"], "mode": manifest.get("mode"),
                          "layout": manifest.get("layout")})
        suite = manifest["project"]
        source_root = Path(manifest["input_root"])
        if not source_root.is_absolute():
            source_root = path.parent / source_root
        for entry in files:
            relative = Path(entry["input"])
            case_id = (Path(suite) / relative.with_suffix(".lean")).as_posix()
            if case_id in seen:
                raise ValueError(f"duplicate case: {case_id}")
            seen.add(case_id)
            # Older manifests contain paths to a previous output location.
            generated = corpus / case_id
            source = source_root / relative
            queries = entry.get("queries", [])
            status = "translated" if entry["status"] == "translated" else "translation_failed"
            error = entry.get("error") or ""
            if status == "translated" and not generated.is_file():
                status, error = "generated_missing", str(generated)
            if not source.is_file():
                status, error = "source_missing", str(source)
            cases.append({
                "case": case_id, "suite": suite, "source": str(source),
                "generated": str(generated) if generated.is_file() else None,
                "source_sha256": digest(source), "generated_sha256": digest(generated),
                "translation_status": entry["status"], "inventory_status": status,
                "translation_error": entry.get("error") or "", "error": error,
                "namespace": entry.get("namespace"), "queries": queries,
            })
    if not manifests:
        raise ValueError(f"no *-manifest.json files in {corpus}")
    return sorted(cases, key=lambda c: c["case"]), manifests


def case_source(case: dict, header: str) -> tuple[str, str]:
    """Copy statements only; template theorems containing sorry are never loaded."""
    if case["inventory_status"] != "translated":
        return header + "\nrun_elab FlexParity.run\n", case["inventory_status"]
    queries = case["queries"]
    if len(queries) != 1:
        return header + "\nrun_elab FlexParity.run\n", "unsupported_query_count"
    if queries[0]["target_kind"] != "model_existence":
        return header + "\nrun_elab FlexParity.run\n", "unsupported_target"
    text = Path(case["generated"]).read_text()
    if "\n-- Proofs\n" not in text:
        raise ValueError(f"{case['case']}: missing generated proof-section boundary")
    statements = text.split("\n-- Proofs\n", 1)[0]
    header = with_imports(header, re.findall(r"^import (.*)$", statements, re.MULTILINE))
    statements = re.sub(r"^import .*\n", "", statements, flags=re.MULTILINE)
    goal = queries[0]["goal_name"]
    namespace = case["namespace"]
    return (header + "\n" + statements +
            f"\nrun_elab FlexParity.run (some ``{goal})\nend {namespace}\n", "")


def with_imports(header: str, extra: list[str]) -> str:
    imports = re.findall(r"^import (.*)$", header, re.MULTILINE)
    imports = list(dict.fromkeys([*imports, *extra]))
    body = re.sub(r"^import .*\n", "", header, flags=re.MULTILINE)
    return "".join(f"import {module}\n" for module in imports) + body


def capture(command: list[str], *, timeout: float = 60) -> str:
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True,
                            check=True, timeout=timeout)
    return result.stdout.strip()


def binary_info(executable: str, version_args: list[str]) -> dict:
    resolved = shutil.which(executable)
    if resolved is None:
        return {"requested": executable, "available": False}
    path = Path(resolved).resolve()
    try:
        result = subprocess.run([str(path), *version_args], cwd=ROOT, text=True,
                                capture_output=True, timeout=15)
        version = (result.stdout + result.stderr).strip()[:4000]
    except (OSError, subprocess.TimeoutExpired) as exc:
        version = str(exc)
    return {"requested": executable, "available": True, "path": str(path),
            "sha256": digest(path), "version": version}


def lean_setup(output: Path, skip_build: bool, header: str) -> tuple[list[str], dict]:
    if not skip_build:
        subprocess.run(["lake", "--log-level=error", "build", "Flex.CHC"],
                       cwd=ROOT, check=True)
    setup_source = output / "Setup.lean"
    setup_source.write_text(header)
    setup = capture(["lake", "--log-level=error", *(["--no-build"] if skip_build else []), "setup-file",
                     str(setup_source)], timeout=120)
    setup_json = json.loads(setup)
    setup_path = output / "lean-setup.json"
    write_json(setup_path, setup_json)
    env_code = (
        "import json,os,shutil; print(json.dumps({'lean':shutil.which('lean'),"
        "'env':{k:v for k,v in os.environ.items() if k in "
        "('PATH','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH',"
        "'DYLD_LIBRARY_PATH','DYLD_FALLBACK_LIBRARY_PATH')}}))"
    )
    environment = json.loads(capture(["lake", "env", sys.executable, "-c", env_code]))
    write_json(output / "lean-environment.json", environment)
    return [environment["lean"], "--setup", str(setup_path)], {
        **os.environ, **environment["env"]}


def read_events(path: Path) -> tuple[list[dict], str]:
    events, error = [], ""
    if path.exists():
        for line in path.read_text().splitlines():
            try:
                event = json.loads(line)
                if not isinstance(event, dict) or "stage" not in event:
                    raise ValueError("event has no stage")
                events.append(event)
            except (ValueError, TypeError) as exc:
                error = f"invalid event: {exc}"
    return events, error


def terminate_case(process: subprocess.Popen) -> None:
    """The native runner gives solvers their own process groups."""
    groups = {process.pid}
    try:
        table = subprocess.check_output(["ps", "-axo", "pid=,ppid=,pgid="], text=True)
        rows = [tuple(map(int, line.split())) for line in table.splitlines()]
        descendants = {process.pid}
        while True:
            children = {pid for pid, parent, _ in rows if parent in descendants}
            if children <= descendants:
                break
            descendants |= children
        groups.update(group for pid, _, group in rows if pid in descendants)
    except (OSError, ValueError, subprocess.SubprocessError):
        pass
    for group in groups - {process.pid}:
        try:
            os.killpg(group, signal.SIGKILL)
        except ProcessLookupError:
            pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def deadline_cleanup(process: subprocess.Popen, events_path: Path, solver_timeout: float) -> bool:
    """Let an active native request reap its solver before killing Lean."""
    grace = time.monotonic() + 2 * solver_timeout + 1
    while process.poll() is None:
        try:
            os.kill(process.pid, signal.SIGSTOP)
        except ProcessLookupError:
            break
        events, _ = read_events(events_path)
        active_solver = bool(events and events[-1]["stage"] in {"native_solver", "solver"}
                             and events[-1].get("status") == "running")
        if not active_solver:
            terminate_case(process)
            return True
        os.kill(process.pid, signal.SIGCONT)
        if time.monotonic() >= grace:
            terminate_case(process)
            return False
        time.sleep(0.02)
    process.wait()
    return True


def result_row(record: dict) -> dict:
    events = {e["stage"]: e for e in record["events"]}
    native_event, solver_event = events.get("native_solver", {}), events.get("solver", {})
    native = native_event.get("solver_status", native_event.get("status", ""))
    solver = solver_event.get("solver_status", solver_event.get("status", ""))
    agree = native == solver if native in DEFINITE and solver in DEFINITE else None
    row = {key: record[key] for key in ("case", "backend", "inventory_status",
                                       "status", "wall_ms", "error")}
    row.update(native_status=native, flex_status=solver, answer_agreement=agree,
               import_status=events.get("import", {}).get("status", ""),
               certificate_status=events.get("certificate", {}).get("status", ""),
               kernel_status=events.get("kernel", {}).get("status", ""),
               startup_ms=record.get("startup_ms"),
               flex_unavailable=record.get("flex_unavailable", ""),
               last_stage=record["events"][-1]["stage"] if record["events"] else "",
               relations=events.get("export", {}).get("relations"),
               clauses=events.get("export", {}).get("clauses"),
               remaining_goals=events.get("result", {}).get("goals"),
               native_outcome=native_event.get("status", ""),
               flex_outcome=solver_event.get("status", ""),
               native_process_ms=native_event.get("process_ms"),
               flex_process_ms=solver_event.get("process_ms"))
    for stage in STAGES:
        row[stage + "_ms"] = events.get(stage, {}).get("elapsed_ms")
    return row


def run_case(case: dict, backend: str, args: argparse.Namespace,
             command: list[str], environment: dict, header: str) -> dict:
    case_dir = args.output / "cases" / backend / case["case"].removesuffix(".lean")
    case_dir.mkdir(parents=True)
    record = {key: case[key] for key in ("case", "inventory_status")}
    record.update(backend=backend, events=[], wall_ms=0, error="", status="not_run",
                  artifacts=str(case_dir))
    started = time.perf_counter()
    try:
        source, unavailable = case_source(case, header)
        source_path = case_dir / "Case.lean"
        source_path.write_text(source)
        executable = args.z3 if backend == "spacer" else args.eldarica
        env = {**environment, "FLEX_PARITY_INPUT": case["source"],
               "FLEX_PARITY_OUTPUT": str(case_dir), "FLEX_PARITY_BACKEND": backend,
               "FLEX_PARITY_EXECUTABLE": executable,
               "FLEX_PARITY_SOLVER_MS": str(round(args.solver_timeout * 1000)),
               "FLEX_PARITY_HEARTBEATS": str(args.heartbeats),
               "FLEX_PARITY_PROOF_HEARTBEATS": str(args.proof_heartbeats)}
        with (case_dir / "lean.log").open("w") as log:
            record["process_unix_ms"] = time.time_ns() // 1_000_000
            process = subprocess.Popen([*command, str(source_path)], cwd=ROOT, env=env,
                                       stdout=log, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            try:
                process.wait(timeout=args.case_timeout)
                record["status"] = "complete" if process.returncode == 0 else "lean_failed"
            except subprocess.TimeoutExpired:
                record["status"] = "case_timeout"
                record["solver_cleanup_completed"] = deadline_cleanup(
                    process, case_dir / "events.jsonl", args.solver_timeout)
            record["exit_code"] = process.returncode
        record["events"], record["error"] = read_events(case_dir / "events.jsonl")
        if record["error"]:
            record["status"] = "invalid_events"
        if record["status"] == "complete":
            result = next((e for e in reversed(record["events"]) if e["stage"] == "result"), None)
            if result is None:
                record.update(status="invalid_events", error="Lean exited without a result event")
            else:
                record.update(status=result["status"], error=result.get("error", ""))
        if unavailable:
            record["flex_unavailable"] = unavailable
        # Lean records elapsed startup at its first event, before either solver.
        start_event = next((e for e in record["events"] if e["stage"] == "start"), None)
        if start_event and "unix_ms" in start_event:
            record["startup_ms"] = max(0, start_event["unix_ms"] - record["process_unix_ms"])
        if record["status"] == "lean_failed":
            record["error"] = (case_dir / "lean.log").read_text()[-4000:]
    except (OSError, ValueError) as exc:
        record.update(status="runner_failed", error=str(exc))
    record["wall_ms"] = round((time.perf_counter() - started) * 1000, 3)
    write_json(case_dir / "result.json", record)
    return record


def summarize(cases: list[dict], selected: list[dict], records: list[dict],
              backends: list[str]) -> dict:
    rows = [result_row(record) for record in records]
    result = {
        "inventory_files": len(cases), "selected_files": len(selected),
        "unselected_files": len(cases) - len(selected),
        "inventory": dict(Counter(c["inventory_status"] for c in cases)),
        "expected_runs": len(selected) * len(backends), "completed_runs": len(records),
        "backends": {},
    }
    for backend in backends:
        subset = [r for r in rows if r["backend"] == backend]
        result["backends"][backend] = {
            "runs": len(subset), "outcomes": dict(Counter(r["status"] for r in subset)),
            "native_answers": dict(Counter(r["native_status"] or "not_run" for r in subset)),
            "flex_answers": dict(Counter(r["flex_status"] or "not_run" for r in subset)),
            "definite_agreements": sum(r["answer_agreement"] is True for r in subset),
            "definite_disagreements": sum(r["answer_agreement"] is False for r in subset),
            "fully_proved": sum(r["status"] == "proved" and r["kernel_status"] == "ok"
                                for r in subset),
            "certified_partial": sum(r["status"] == "partial" and r["kernel_status"] == "ok"
                                     for r in subset),
            "imported": sum(r["import_status"] == "ok" for r in subset),
            "stages": {
                stage: dict(Counter(e.get("status", "unknown") for rec in records
                                    if rec["backend"] == backend for e in rec["events"]
                                    if e["stage"] == stage and e.get("status") != "running"))
                for stage in STAGES},
        }
    return result


def save_results(args: argparse.Namespace, cases: list[dict],
                 selected: list[dict], records: list[dict]) -> None:
    records = sorted(records, key=lambda r: (r["case"], r["backend"]))
    (args.output / "results.jsonl").write_text("".join(json.dumps(r) + "\n" for r in records))
    rows = [result_row(record) for record in records]
    if rows:
        with (args.output / "results.csv").open("w", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
    write_json(args.output / "summary.json", summarize(cases, selected, records, args.backends))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--backends", nargs="+", choices=["spacer", "eldarica"],
                        default=["spacer", "eldarica"])
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--cases", nargs="+", help="exact suite/path.lean names from inventory")
    selection.add_argument("--retry-unproved", type=Path, metavar="RESULTS_CSV",
                           help="retry previous inputs without a checked proof or any unsat answer")
    parser.add_argument("--solver-timeout", type=float, default=30,
                        help="seconds per native/exported solver call (default: 30)")
    parser.add_argument("--case-timeout", type=float, default=180,
                        help="whole-case seconds, including both solver calls and certification "
                             "(default: 180); active solvers get bounded cleanup grace")
    parser.add_argument("--heartbeats", type=int, default=200000)
    parser.add_argument("--proof-heartbeats", type=int, default=20000)
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--z3", default=os.environ.get("CHC_Z3", "z3"))
    parser.add_argument("--eldarica", default=os.environ.get("CHC_ELDARICA", "eld"))
    parser.add_argument("--skip-build", action="store_true")
    parser.add_argument("--inventory-only", action="store_true")
    args = parser.parse_args()
    if min(args.solver_timeout, args.case_timeout, args.heartbeats,
           args.proof_heartbeats, args.workers) <= 0:
        parser.error("budgets and worker count must be positive")
    if round(args.solver_timeout * 1000) < 1:
        parser.error("--solver-timeout must round to at least one millisecond")
    if len(set(args.backends)) != len(args.backends):
        parser.error("duplicate backends")
    args.corpus, args.output = args.corpus.resolve(), args.output.resolve()
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("--output must be empty; previous measurements are never overwritten")
    try:
        cases, manifests = inventory(args.corpus)
    except (OSError, ValueError, KeyError) as exc:
        parser.error(str(exc))
    retry = None
    try:
        if args.retry_unproved:
            wanted, retry = retry_unproved(args.retry_unproved)
        else:
            wanted = set(args.cases) if args.cases else {case["case"] for case in cases}
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    missing = wanted - {case["case"] for case in cases}
    if missing:
        parser.error("unknown cases: " + ", ".join(sorted(missing)))
    selected = [case for case in cases if case["case"] in wanted]
    args.output.mkdir(parents=True, exist_ok=True)
    write_json(args.output / "inventory.json", {
        "manifests": manifests, "cases": [{**case, "selected": case["case"] in wanted}
                                       for case in cases]})
    metadata = {
        "started_at": datetime.now(timezone.utc).isoformat(), "platform": platform.platform(),
        "corpus": str(args.corpus), "git_head": capture(["git", "rev-parse", "HEAD"]),
        "git_status": capture(["git", "status", "--porcelain"]),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "dependencies": json.loads((ROOT / "lake-manifest.json").read_text()),
        "arguments": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
        "retry": retry,
        "source_hashes": {str(p.relative_to(ROOT)): digest(p) for p in [
            ROOT / "lake-manifest.json", ROOT / "lakefile.lean",
            ROOT / "scripts/CHCParity.lean", Path(__file__), ROOT / "scripts/benchmark_chc.py",
            *sorted((ROOT / "Flex/CHC").glob("*.lean")), ROOT / "native/chc_process.cpp"]},
        "method": "Native and Flex-exported scripts use the same backend runner, executable, "
                  "options, timeout, and model request. Partial certificates are not full proofs.",
        "complete": False,
    }
    write_json(args.output / "metadata.json", metadata)
    save_results(args, cases, selected, [])
    print(f"Inventory: {len(cases)} files; {len(selected)} selected; "
          f"{dict(Counter(c['inventory_status'] for c in cases))}", flush=True)
    if args.inventory_only:
        return 0
    metadata["binaries"] = {
        b: binary_info(args.z3 if b == "spacer" else args.eldarica,
                       ["--version"] if b == "spacer" else ["-h"]) for b in args.backends}
    write_json(args.output / "metadata.json", metadata)
    header = (ROOT / "scripts/CHCParity.lean").read_text()
    imports = [module for case in selected if case["generated"]
               for module in re.findall(r"^import (.*)$", Path(case["generated"]).read_text(),
                                        re.MULTILINE)]
    setup_header = with_imports(header, imports)
    command, environment = lean_setup(args.output, args.skip_build, setup_header)
    metadata["lean_command"] = command
    metadata["lean_version"] = capture([command[0], "--version"])
    write_json(args.output / "metadata.json", metadata)
    records = []
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(run_case, case, backend, args, command, environment, header)
                   for case in selected for backend in args.backends]
        for future in as_completed(futures):
            record = future.result()
            records.append(record)
            save_results(args, cases, selected, records)
            row = result_row(record)
            print(f"{len(records)}/{len(futures)} {row['backend']} {row['case']}: "
                  f"native={row['native_status'] or '-'} flex={row['flex_status'] or '-'} "
                  f"kernel={row['kernel_status'] or '-'} {row['status']}", flush=True)
    metadata.update(complete=len(records) == len(selected) * len(args.backends),
                    finished_at=datetime.now(timezone.utc).isoformat())
    write_json(args.output / "metadata.json", metadata)
    print(f"Results: {args.output}")
    return 1 if any(r["status"] in {"runner_failed", "invalid_events", "lean_failed"}
                    for r in records) else 0


if __name__ == "__main__":
    raise SystemExit(main())
