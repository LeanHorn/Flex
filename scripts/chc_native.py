#!/usr/bin/env python3
"""Run original CHC SMT inputs directly; retain solver models and per-task results."""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import csv
import json
import os
from pathlib import Path
import random
import signal
import subprocess
import sys
import threading
import time

from chc_parity import ROOT, binary_info, capture, git_info, digest, inventory, write_json, write_text

ARGUMENTS = {
    "spacer": ["-in", "-smt2", "-model", "fp.engine=spacer",
               "fp.xform.inline_eager=false", "fp.xform.inline_linear=false"],
    "eldarica": ["-in", "-hsmt", "-ssol"],
}


def sexps(text: str) -> list:
    """Read complete SMT forms, ignoring comments without rewriting input."""
    roots, stack, i = [], [], 0
    while i < len(text):
        c = text[i]
        if c.isspace():
            i += 1
            continue
        if c == ";":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end + 1
            continue
        if c == "(":
            value = []
            (stack[-1] if stack else roots).append(value)
            stack.append(value)
            i += 1
            continue
        if c == ")":
            if not stack:
                raise ValueError("unbalanced SMT close parenthesis")
            stack.pop()
            i += 1
            continue
        start = i
        if c in {'"', '|'}:
            delimiter = c
            i += 1
            while i < len(text):
                if text[i] == delimiter:
                    i += 1
                    if delimiter == '"' and i < len(text) and text[i] == '"':
                        i += 1
                        continue
                    break
                i += 1
            else:
                raise ValueError("unterminated SMT string or quoted symbol")
        else:
            while i < len(text) and not text[i].isspace() and text[i] not in "();":
                i += 1
        (stack[-1] if stack else roots).append(text[start:i])
    if stack:
        raise ValueError("unbalanced SMT open parenthesis")
    return roots


def inspect_input(text: str) -> None:
    commands = sexps(text)
    heads = [command[0] if isinstance(command, list) and command else None
             for command in commands]
    if heads.count("check-sat") != 1:
        raise ValueError("expected one check-sat command")
    allowed = {"set-logic", "set-info", "declare-fun", "declare-const", "define-fun",
               "declare-sort", "define-sort", "assert", "check-sat", "exit"}
    unsupported = [head for head in heads if head not in allowed]
    if unsupported:
        raise ValueError(f"unsupported original command protocol: {unsupported}")
    check = heads.index("check-sat")
    if any(head != "exit" for head in heads[check + 1:]):
        raise ValueError("commands after check-sat must only be exit")


def response(text: str, exit_code: int) -> tuple[str, bool, str]:
    try:
        forms = sexps(text)
    except ValueError as error:
        return "error", False, str(error)
    statuses = [form for form in forms if isinstance(form, str) and
                form in {"sat", "unsat", "unknown"}]
    errors = [form for form in forms if isinstance(form, list) and form and form[0] == "error"]
    if exit_code != 0:
        return "error", False, f"solver exited with {exit_code}"
    if errors:
        return "error", False, json.dumps(errors)
    if len(statuses) != 1:
        return "error", False, f"expected one solver status, found {statuses}"
    def model(form):
        return isinstance(form, list) and bool(form) and (
            form[0] in ("model", "define-fun") if isinstance(form[0], str)
            else any(model(child) for child in form))
    available = statuses[0] == "sat" and any(model(form) or form == [] for form in forms)
    return statuses[0], available, ""


def run_one(task: dict, backend: str, args, active: dict, lock: threading.Lock) -> dict:
    artifact = args.output / "cases" / backend / task["key"]
    artifact.mkdir(parents=True, exist_ok=True)
    result_path = artifact / "result.json"
    if args.resume and result_path.exists():
        return json.loads(result_path.read_text())
    record = {"key": task["key"], "backend": backend,
              "source_sha256": task["sha256"], "representative": task["case"],
              "status": "error", "model_available": False, "error": "", "wall_ms": 0,
              "artifacts": str(artifact), "exit_code": None}
    started = time.perf_counter()
    process = None
    try:
        original = args.output / "inputs" / (task["key"] + ".smt2")
        payload = original.read_bytes()
        command = [args.z3 if backend == "spacer" else args.eldarica, *ARGUMENTS[backend]]
        write_json(artifact / "invocation.json", {"command": command,
                   "timeout_seconds": args.solver_timeout, "input": str(original)})
        with (artifact / "stdout.txt").open("wb") as stdout, (artifact / "stderr.txt").open("wb") as stderr:
            process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=stdout,
                                       stderr=stderr, cwd=ROOT, start_new_session=True)
            with lock:
                active[process.pid] = {"process": process, "backend": backend,
                                       "case": task["case"], "key": task["key"]}
            try:
                process.communicate(payload, timeout=args.solver_timeout)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.communicate()
                record.update(status="timeout", error="solver wall-clock timeout")
            else:
                status, model, error = response((artifact / "stdout.txt").read_text(errors="replace"),
                                                process.returncode)
                record.update(status=status, model_available=model, error=error)
            record["exit_code"] = process.returncode
    except (OSError, ValueError) as error:
        record["error"] = str(error)
        if process is not None and process.poll() is None:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
    finally:
        if process is not None:
            with lock:
                active.pop(process.pid, None)
    record["wall_ms"] = round((time.perf_counter() - started) * 1000, 3)
    write_json(result_path, record)
    return record


def save(output: Path, cases: list[dict], records: list[dict], backends: list[str]) -> dict:
    results = {(record["key"], record["backend"]): record for record in records}
    rows = [{"case": case["case"], "suite": case["suite"],
             "source_sha256": case["source_sha256"], "backend": backend,
             "status": results[(case["native_key"], backend)]["status"],
             "model_available": results[(case["native_key"], backend)]["model_available"],
             "wall_ms": results[(case["native_key"], backend)]["wall_ms"],
             "exit_code": results[(case["native_key"], backend)]["exit_code"],
             "error": results[(case["native_key"], backend)]["error"],
             "artifacts": results[(case["native_key"], backend)]["artifacts"],
             "reused_identical_source": case["case"] != results[(case["native_key"], backend)]["representative"]}
            for case in cases for backend in backends if (case["native_key"], backend) in results]
    summary = {"tasks": len(cases), "distinct_sources": len({c["native_key"] for c in cases}),
               "expected_native_runs": len({c["native_key"] for c in cases}) * len(backends),
               "completed_native_runs": len(records), "completed_task_results": len(rows),
               "backends": {}, "suites": {}}
    for backend in backends:
        subset = [row for row in rows if row["backend"] == backend]
        measured = [record for record in records if record["backend"] == backend]
        summary["backends"][backend] = {"completed_tasks": len(subset),
            "task_statuses": dict(Counter(row["status"] for row in subset)),
            "distinct_statuses": dict(Counter(record["status"] for record in measured)),
            "task_models": sum(row["model_available"] for row in subset)}
    for suite in sorted({case["suite"] for case in cases}):
        summary["suites"][suite] = {backend: dict(Counter(
            row["status"] for row in rows if row["suite"] == suite and row["backend"] == backend))
            for backend in backends}
    write_json(output / "summary.json", summary)
    write_text(output / "results.jsonl", "".join(json.dumps(record) + "\n" for record in records))
    if rows:
        path = output / "results.csv"
        temporary = path.with_suffix(".csv.tmp")
        with temporary.open("w", newline="") as handle:
            writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
            writer.writeheader()
            writer.writerows(rows)
        temporary.replace(path)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=ROOT / "evaluation/CHC-COMP/generated")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--backends", nargs="+", choices=list(ARGUMENTS), default=list(ARGUMENTS))
    parser.add_argument("--cases", nargs="+")
    parser.add_argument("--solver-timeout", type=float, default=30)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20261101)
    parser.add_argument("--z3", default=os.environ.get("CHC_Z3", "z3"))
    parser.add_argument("--eldarica", default=os.environ.get("CHC_ELDARICA", "eld"))
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--progress", type=Path)
    args = parser.parse_args()
    if args.progress:
        summary = json.loads((args.progress / "summary.json").read_text())
        metadata = json.loads((args.progress / "metadata.json").read_text())
        print(f"{summary['completed_native_runs']}/{summary['expected_native_runs']} distinct-input/backend runs; complete={metadata['complete']}")
        for backend, data in summary["backends"].items():
            print(f"{backend}: {data['completed_tasks']}/{summary['tasks']} task results {data['task_statuses']}; models={data['task_models']}")
        return 0
    if args.output is None or min(args.solver_timeout, args.workers) <= 0:
        parser.error("--output and positive budgets/workers are required")
    if len(args.backends) != len(set(args.backends)):
        parser.error("duplicate backends")
    args.output = args.output.resolve()
    if args.output.exists() and any(args.output.iterdir()) and not args.resume:
        parser.error("output exists; use --resume with identical configuration")
    cases, manifests = inventory(args.corpus.resolve())
    if args.cases:
        wanted = set(args.cases)
        missing = wanted - {case["case"] for case in cases}
        if missing:
            parser.error(f"unknown cases: {sorted(missing)}")
        cases = [case for case in cases if case["case"] in wanted]
    if any(not case["source_sha256"] for case in cases):
        parser.error("missing original SMT source")
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "inputs").mkdir(exist_ok=True)
    tasks = {}
    for case in cases:
        key = case["source_sha256"]
        case["native_key"] = key
        if key not in tasks:
            text = Path(case["source"]).read_text()
            inspect_input(text)
            target = args.output / "inputs" / (key + ".smt2")
            if target.exists() and digest(target) != key:
                parser.error(f"changed frozen input: {target}")
            if not target.exists():
                target.write_bytes(Path(case["source"]).read_bytes())
            tasks[key] = {"key": key, "sha256": key, "case": case["case"]}
    binaries = {backend: binary_info(args.z3 if backend == "spacer" else args.eldarica,
                 ["--version"] if backend == "spacer" else ["-h"]) for backend in args.backends}
    if not all(info["available"] for info in binaries.values()):
        parser.error("missing solver executable")
    config = {"corpus": str(args.corpus.resolve()), "timeout_seconds": args.solver_timeout,
              "workers": args.workers, "backends": args.backends, "seed": args.seed,
              "binaries": binaries, "cases": [(case["case"], case["source_sha256"]) for case in cases],
              "solver_args": ARGUMENTS}
    metadata_path = args.output / "metadata.json"
    if args.resume and metadata_path.exists():
        previous = json.loads(metadata_path.read_text())
        if previous["configuration"] != json.loads(json.dumps(config)):
            parser.error("resume configuration differs from recorded run")
        metadata = previous
    else:
        metadata = {"started_at": datetime.now(timezone.utc).isoformat(), "complete": False,
                    "configuration": config, "git_head": git_info(["rev-parse", "HEAD"]),
                    "driver_sha256": digest(Path(__file__)),
                    "method": "Original SMT bytes unchanged; solver requests include model production. Identical source contents run once per backend, with explicit per-task mapping. No Lean startup or proof checking."}
    write_json(metadata_path, metadata)
    write_json(args.output / "inventory.json", {"manifests": manifests, "cases": cases})
    active, lock, records = {}, threading.Lock(), []
    def stop(signum, frame):
        with lock:
            for value in active.values():
                try:
                    os.killpg(value["process"].pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        raise KeyboardInterrupt
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    work = [(task, backend) for task in tasks.values() for backend in args.backends]
    random.Random(args.seed).shuffle(work)
    pool = ThreadPoolExecutor(max_workers=args.workers)
    futures = [pool.submit(run_one, task, backend, args, active, lock) for task, backend in work]
    save(args.output, cases, records, args.backends)
    try:
        for future in as_completed(futures):
            record = future.result()
            records.append(record)
            save(args.output, cases, records, args.backends)
            print(f"{len(records)}/{len(work)} {record['backend']} {record['representative']}: {record['status']} {record['wall_ms']:.0f}ms", flush=True)
    except KeyboardInterrupt:
        pool.shutdown(wait=True, cancel_futures=True)
        metadata["stopped_at"] = datetime.now(timezone.utc).isoformat()
        write_json(metadata_path, metadata)
        return 130
    finally:
        pool.shutdown(wait=True, cancel_futures=True)
    metadata.update(complete=len(records) == len(work),
                    finished_at=datetime.now(timezone.utc).isoformat())
    write_json(metadata_path, metadata)
    return int(any(record["status"] == "error" for record in records))


if __name__ == "__main__":
    raise SystemExit(main())
