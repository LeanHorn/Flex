#!/usr/bin/env python3
"""Freeze and evaluate RQ1 predicate goals without importing their manual proofs."""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import csv
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import time

from chc_parity import ROOT, binary_info, capture, digest, lean_setup, terminate_case, write_json
from rq1_corpus import inventory, snapshot_suite, summarize, imports


VARIANTS = ("zap_fix_deep", "zap_solver")


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def checkpoint(output: Path, state: dict) -> None:
    temporary = output / "progress.tmp"
    write_json(temporary, {"updated_at": now(), **state})
    temporary.replace(output / "progress.json")


def compile_suite(manifest: dict, output: Path, lean: str, environment: dict,
                  setup: dict) -> dict:
    workspace = output / "workspaces" / manifest["suite"]
    compiled = workspace / ".compiled"
    env = {**environment, "LEAN_PATH": str(compiled) + os.pathsep + environment.get("LEAN_PATH", "")}
    outcomes = {}
    for entry in manifest["modules"]:
        module = entry["module"]
        source = workspace / entry["path"]
        target = compiled / Path(entry["path"]).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        blocked = [m for m in imports(source.read_text())
                   if m in outcomes and outcomes[m]["status"] != "compiled"]
        if blocked:
            outcomes[module] = {"status": "dependency_failed", "dependencies": blocked}
            continue
        config = {**setup, "name": module}
        setup_path = workspace / "module-setup.json"
        write_json(setup_path, config)
        start = time.monotonic()
        log = target.with_suffix(".log")
        try:
            result = subprocess.run([lean, "--setup", str(setup_path), "--error=hasSorry",
                                     "-o", str(target), str(source)],
                                    cwd=workspace, env=env, text=True, capture_output=True, timeout=120)
            log.write_text(result.stdout + result.stderr)
            outcomes[module] = {"status": "compiled" if result.returncode == 0 else "compile_failed",
                                "exit_code": result.returncode, "log": str(log)}
        except subprocess.TimeoutExpired:
            outcomes[module] = {"status": "compile_timeout", "log": str(log)}
        outcomes[module]["elapsed_ms"] = round((time.monotonic() - start) * 1000)
    write_json(workspace / "compilation.json", outcomes)
    return outcomes


def source_hashes() -> dict:
    paths = [*sorted((ROOT / "Flex").rglob("*.lean")), ROOT / "lean-toolchain",
             ROOT / "lake-manifest.json", ROOT / "lakefile.lean",
             ROOT / "scripts/RQ1Baseline.lean", Path(__file__), ROOT / "scripts/rq1_corpus.py",
             ROOT / "scripts/chc_parity.py", ROOT / "native/chc_process.cpp"]
    return {str(path.relative_to(ROOT)): digest(path) for path in paths}


def synthesis_counts(record: dict) -> dict:
    """Only checked retained assignments earn progress; candidate imports are separate."""
    phases = record.get("phases", [])
    checked = record.get("kernel_checked") is True
    committed = lambda name: sum(p.get("predicates_instantiated", 0) for p in phases
                                 if p.get("phase") == name and p.get("status") in {"proved", "partial"})
    zap = committed("zap") if checked else None
    fix = committed("fix") if checked else None
    candidates = [p for p in phases if p.get("phase") in {"spacer_candidate", "eldarica_candidate"}
                  and p.get("status") == "imported"]
    solver = (max(0, record["initial_predicates"] - record["remaining_predicates"] - zap)
              if checked and record["variant"] == "zap_solver" else 0 if checked else None)
    retained = record.get("retained_solver", "")
    chosen = [p for p in candidates if p["phase"] == retained + "_candidate"]
    heads_certified = ((record.get("status") == "proved" or
                        all(p.get("head_certification_complete") is True for p in chosen))
                       if checked and chosen else None)
    progress = bool(checked and ((zap or 0) + (fix or 0) + (solver or 0)))
    instantiated = bool(checked and record.get("remaining_predicates") == 0)
    eliminated = bool(checked and record.get("remaining_predicates") == 0 and
                       ((solver or 0) == 0 or heads_certified))
    outcome = ("unmeasured" if not checked else "heads_eliminated" if eliminated else
               "instantiated" if instantiated else "partial_instantiation" if progress else "no_instantiation")
    return {"synthesis_outcome": outcome, "zap_eliminated": zap, "fix_instantiated": fix,
            "solver_instantiated": solver,
            "solver_heads_certified": heads_certified,
            "solver_imported": sum(p.get("witnesses", 0) for p in candidates),
            "solver_candidate_attempts": len(candidates),
            "synthesis_progress": progress, "instantiation_complete": instantiated,
            "elimination_complete": eliminated}


def run_case(case: dict, variant: str, args: argparse.Namespace, lean: str,
             environment: dict, setup: dict) -> dict:
    directory = args.output / "cases" / case["id"] / variant
    directory.mkdir(parents=True)
    workspace = args.output / "workspaces" / case["suite"]
    source = directory / "Case.lean"
    source.write_text(f"import RQ1Baseline\nimport {case['module']}\n"
                      f"set_option maxHeartbeats 0\nset_option maxRecDepth {args.recursion_limit}\n"
                      "set_option Elab.async false\n"
                      f"run_elab RQ1Baseline.run ``{case['declaration']} "
                      f"{json.dumps(variant)} {json.dumps(case['id'])}\n")
    setup_path = directory / "setup.json"
    write_json(setup_path, {**setup, "name": "RQ1Case"})
    env = {**environment,
           "LEAN_PATH": os.pathsep.join([str(args.output / "harness"), str(workspace / ".compiled"),
                                          environment.get("LEAN_PATH", "")]),
           "FLEX_RQ1_OUTPUT": str(directory),
           "FLEX_RQ1_CASE_SECONDS": str(args.case_timeout),
           "FLEX_RQ1_PA_SECONDS": str(args.pa_timeout),
           "FLEX_RQ1_SOLVER_MS": str(args.solver_timeout * 1000),
           "FLEX_RQ1_DISCHARGE": "1" if args.discharge else "0",
           "FLEX_RQ1_PHASE_HEARTBEATS": str(args.phase_heartbeats),
           "FLEX_RQ1_RECURSION_LIMIT": str(args.recursion_limit)}
    result_path = directory / variant / "result.json"
    progress_path = directory / variant / "progress.jsonl"
    log_path = directory / "lean.log"
    started = time.monotonic()
    first_event = None
    timed_out = False
    with log_path.open("w") as log:
        process = subprocess.Popen([lean, "--setup", str(setup_path), str(source)],
                                   cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                                   start_new_session=True)
        try:
            while process.poll() is None:
                elapsed = time.monotonic() - started
                # run_elab may buffer stdout; this file is flushed independently.
                if first_event is None and progress_path.exists() and progress_path.stat().st_size:
                    first_event = time.monotonic()
                if ((first_event is None and elapsed > args.startup_timeout) or
                    (first_event is not None and time.monotonic() - first_event > args.case_timeout)):
                    timed_out = True
                    terminate_case(process)
                    process.wait(timeout=10)
                    break
                time.sleep(0.1)
        except BaseException:
            terminate_case(process)
            process.wait(timeout=10)
            raise
    wall = round((time.monotonic() - started) * 1000)
    if result_path.exists() and not timed_out and process.returncode == 0:
        record = json.loads(result_path.read_text())
        if record.get("case") != case["id"] or record.get("variant") != variant:
            raise ValueError(f"mismatched result: {result_path}")
        if record.get("status") not in {"proved", "partial", "failed"}:
            raise ValueError(f"unexpected status: {result_path}")
        if record["status"] in {"proved", "partial"} and record.get("kernel_checked") is not True:
            raise ValueError(f"unchecked proof/bridge: {result_path}")
        if record["status"] == "proved" and (record.get("remaining_goals") != 0 or
                                             record.get("remaining_predicates") != 0):
            raise ValueError(f"incomplete proof marked proved: {result_path}")
        if record.get("initial_predicates") != len(case["predicates"]):
            raise ValueError(f"source/Lean predicate count mismatch: {result_path}")
    else:
        record = {"case": case["id"], "variant": variant,
                  "status": ("case_timeout" if first_event else "startup_timeout") if timed_out else "lean_failed",
                  "error": log_path.read_text()[-4000:], "phases": []}
        # Keep phase evidence even when a hard deadline interrupts final reporting.
        progress = progress_path.read_text() if progress_path.exists() else ""
        for line in progress.splitlines():
            if line.startswith("FLEX_RQ1_PHASE "):
                try:
                    record["phases"].append(json.loads(line[len("FLEX_RQ1_PHASE "):]))
                except json.JSONDecodeError:
                    pass
    record.update(suite=case["suite"], classification=case["classification"],
                  source_predicates=len(case["predicates"]), source_sha256=case["sha256"],
                  process_wall_ms=wall, startup_ms=None if first_event is None else
                  round((first_event - started) * 1000), artifacts=str(directory),
                  process_exit_code=process.returncode, censored=timed_out)
    record.update(synthesis_counts(record))
    write_json(directory / "record.json", record)
    return record


def summarize_results(output: Path, rows: list[dict], selected: list[dict]) -> None:
    by_variant = {}
    for variant in sorted({r["variant"] for r in rows}):
        records = [r for r in rows if r["variant"] == variant]
        by_variant[variant] = {"completed": len(records),
                               "outcomes": dict(Counter(r["status"] for r in records)),
                               "synthesis_outcomes": dict(Counter(r.get("synthesis_outcome", "unmeasured") for r in records)),
                               "vcs_with_instantiation_complete": sum(r.get("instantiation_complete", False) for r in records),
                               "vcs_with_elimination_complete": sum(r.get("elimination_complete", False) for r in records),
                               "vcs_with_zap_progress": sum((r.get("zap_eliminated") or 0) > 0 for r in records),
                               "vcs_with_fix_witnesses": sum((r.get("fix_instantiated") or 0) > 0 for r in records),
                               "vcs_with_solver_candidates": sum((r.get("solver_imported") or 0) > 0 for r in records),
                               "vcs_with_solver_heads_certified": sum(r.get("solver_heads_certified") is True for r in records),
                               "cyclic_outcomes": dict(Counter(r["status"] for r in records
                                                               if r["classification"] != "acyclic_only")),
                               "by_suite": {s: dict(Counter(r["status"] for r in records if r["suite"] == s))
                                            for s in sorted({r["suite"] for r in records})}}
    write_json(output / "summary.json", {"selected_vcs": len(selected), "variants": by_variant,
               "vcs_with_checked_synthesis_progress": len({r["case"] for r in rows if r.get("synthesis_progress")}),
               "vcs_with_instantiation_complete": len({r["case"] for r in rows if r.get("instantiation_complete")}),
               "vcs_with_elimination_complete": len({r["case"] for r in rows if r.get("elimination_complete")}),
               "cyclic_vcs_with_elimination_complete": len({r["case"] for r in rows
                    if r.get("elimination_complete") and r["classification"] != "acyclic_only"}),
               "vcs_fully_proved": len({r["case"] for r in rows if r["status"] == "proved"})})
    fields = ["case", "suite", "classification", "variant", "synthesis_outcome", "status", "source_predicates",
              "initial_predicates", "remaining_predicates", "zap_eliminated", "fix_instantiated",
              "solver_imported", "solver_instantiated", "solver_heads_certified", "synthesis_progress",
              "instantiation_complete", "elimination_complete", "kernel_checked",
              "remaining_goals", "elapsed_ms", "heartbeats",
              "process_wall_ms", "startup_ms", "censored", "error", "artifacts"]
    with (output / "results.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT.parent / "flex-benchmarks")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cases", nargs="+", help="exact suite/Name IDs; default all predicate VCs")
    parser.add_argument("--variants", nargs="+", choices=VARIANTS, default=list(VARIANTS))
    parser.add_argument("--inventory-only", action="store_true")
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--discharge", action="store_true", help="also attempt residual VC proof (off by default)")
    parser.add_argument("--compare", type=Path, help="previous complete run containing these inputs, with matching budgets")
    parser.add_argument("--reuse-completed", type=Path,
                        help="reuse checked results with identical inputs, harness, Flex code and budgets")
    parser.add_argument("--case-timeout", type=int, default=180)
    parser.add_argument("--startup-timeout", type=int, default=60)
    parser.add_argument("--pa-timeout", type=int, default=30)
    parser.add_argument("--solver-timeout", type=int, default=60)
    parser.add_argument("--phase-heartbeats", type=int, default=2000000)
    parser.add_argument("--recursion-limit", type=int, default=16384)
    parser.add_argument("--seed", type=int, default=20261026)
    args = parser.parse_args()
    if len(args.variants) != len(set(args.variants)):
        parser.error("duplicate variants")
    args.output = args.output.resolve()
    args.source = args.source.resolve()
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("use a fresh output directory; existing baselines are immutable")
    if any(v <= 0 for v in [args.case_timeout, args.startup_timeout, args.pa_timeout,
                            args.solver_timeout, args.phase_heartbeats, args.recursion_limit]):
        parser.error("budgets must be positive")
    args.output.mkdir(parents=True, exist_ok=True)
    rows = inventory(args.source)
    selected = [row for row in rows if row["selected"]]
    if args.cases:
        wanted = set(args.cases)
        absent = wanted - {row["id"] for row in selected}
        if absent:
            parser.error(f"unknown or predicate-free cases: {sorted(absent)}")
        selected = [row for row in selected if row["id"] in wanted]
    previous = None
    if args.compare:
        previous_meta = json.loads((args.compare / "metadata.json").read_text())
        previous_selection = json.loads((args.compare / "selection.json").read_text())
        if not previous_meta.get("complete") or not previous_meta.get("source_unchanged"):
            parser.error("comparison requires a complete, unchanged previous run")
        old_hashes = {r["id"]: r["sha256"] for r in previous_selection}
        if any(old_hashes.get(r["id"]) != r["sha256"] for r in selected):
            parser.error("comparison does not contain the selected inputs with matching hashes")
        if not set(args.variants).issubset(previous_meta["config"]["variants"]):
            parser.error("comparison does not contain the selected variants")
        for key in ("discharge", "case_timeout", "pa_timeout", "solver_timeout", "phase_heartbeats", "recursion_limit"):
            if getattr(args, key) != previous_meta["config"][key]:
                parser.error(f"comparison configuration differs: {key}")
        wanted = {(r["id"], v) for r in selected for v in args.variants}
        previous = [r for line in (args.compare / "results.jsonl").read_text().splitlines()
                    if ((r := json.loads(line))["case"], r["variant"]) in wanted]
        if Counter((r["case"], r["variant"]) for r in previous) != Counter(wanted):
            parser.error("comparison requires exactly one previous result per selected case/variant")
    write_json(args.output / "inventory.json", {"summary": summarize(rows), "cases": rows})
    write_json(args.output / "selection.json", selected)
    if args.inventory_only:
        print(json.dumps(summarize(rows), indent=2))
        return
    hashes = source_hashes()
    reused = {}
    if args.reuse_completed:
        previous_meta = json.loads((args.reuse_completed / "metadata.json").read_text())
        previous_selection = json.loads((args.reuse_completed / "selection.json").read_text())
        if selected != previous_selection:
            parser.error("reused inputs/classifications differ")
        for path, value in hashes.items():
            if path != "scripts/benchmark_rq1.py" and previous_meta["source_hashes"].get(path) != value:
                parser.error(f"reused source changed: {path}")
        for key in ("variants", "discharge", "case_timeout", "pa_timeout", "solver_timeout", "phase_heartbeats", "recursion_limit"):
            if getattr(args, key) != previous_meta["config"][key]:
                parser.error(f"reused configuration differs: {key}")
        for line in (args.reuse_completed / "results.jsonl").read_text().splitlines():
            row = json.loads(line)
            if (row.get("kernel_checked") is not True or row["status"] not in {"proved", "partial"}
                or row.get("process_exit_code") != 0 or row.get("elapsed_ms", float("inf")) > args.case_timeout * 1000):
                continue
            row.update(reused_from=str(args.reuse_completed.resolve()), startup_ms=None)
            row.update(synthesis_counts(row))
            key = (row["case"], row["variant"])
            if key in reused:
                parser.error(f"duplicate reused result: {key}")
            reused[key] = row
    metadata = {"started_at": now(), "complete": False, "source": str(args.source),
                "source_revision": subprocess.check_output(["git", "-C", str(args.source), "rev-parse", "HEAD"], text=True).strip(),
                "flex_revision": capture(["git", "rev-parse", "HEAD"]), "source_hashes": hashes,
                "reused_runs": len(reused),
                "config": {k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()},
                "policy": "Specification imports only; no User/Proof, handwritten witnesses or per-VC qualifiers. "
                          "Single repetition, serial execution; imports excluded from Lean phase timings. "
                          "Primary progress is retained predicate instantiation and a checked residual bridge. "
                          "Head elimination and complete VC proof are separate; residual discharge is optional. "
                          "An instantiated candidate with remaining head obligations is not yet a certified invariant."}
    write_json(args.output / "metadata.json", metadata)
    if args.reuse_completed:
        metadata["reuse_provenance"] = {
            "directory": str(args.reuse_completed.resolve()),
            "metadata_sha256": digest(args.reuse_completed / "metadata.json"),
            "results_sha256": digest(args.reuse_completed / "results.jsonl"),
            "keys": [list(key) for key in reused],
            "startup_ms": "unavailable for reused records; Lean elapsed time and heartbeats retained"}
    (args.output / "source.patch").write_text(capture(["git", "diff", "HEAD"]))
    frozen = args.output / "runner-source"
    frozen.mkdir()
    for name in ("benchmark_rq1.py", "rq1_corpus.py", "RQ1Baseline.lean"):
        shutil.copy2(ROOT / "scripts" / name, frozen / name)
    checkpoint(args.output, {"stage": "prepare", "completed": 0, "total": len(selected) * len(args.variants)})
    header = "import Flex.Tactic\nimport Flex.CHC\nimport Flex.Tactic.Automation\n"
    command, environment = lean_setup(args.output, False, header)
    metadata["tools"] = {name: binary_info(name, flags) for name, flags in
                         [("z3", ["--version"]), ("cvc5", ["--version"]), ("eld", ["-version"])]}
    if args.reuse_completed:
        for name, tool in metadata["tools"].items():
            old = previous_meta["tools"][name]
            if (tool.get("path"), tool.get("sha256")) != (old.get("path"), old.get("sha256")):
                raise ValueError(f"reused solver executable changed: {name}")
    metadata["lean_version"] = subprocess.check_output([command[0], "--version"], text=True).strip()
    write_json(args.output / "metadata.json", metadata)
    setup = json.loads(Path(command[2]).read_text())
    # Lake may return relative search paths; suite compilation has a different cwd.
    for key in ("LEAN_PATH", "LEAN_SRC_PATH"):
        environment[key] = os.pathsep.join(str((ROOT / p).resolve()) if not Path(p).is_absolute() else p
                                          for p in environment.get(key, "").split(os.pathsep) if p)
    manifests = []
    for suite in sorted({row["suite"] for row in selected}):
        workspace = args.output / "workspaces" / suite
        manifest = snapshot_suite(args.source, suite, [r for r in selected if r["suite"] == suite], workspace)
        if args.compare:
            old = json.loads((args.compare / "workspaces" / suite / "manifest.json").read_text())
            dependencies = {m["module"]: m["sha256"] for m in old["modules"]}
            if any(dependencies.get(m["module"]) != m["sha256"] for m in manifest["modules"]):
                raise ValueError(f"comparison specification dependencies changed: {suite}")
        if args.reuse_completed:
            old = json.loads((args.reuse_completed / "workspaces" / suite / "manifest.json").read_text())
            if manifest != old:
                raise ValueError(f"reused specification dependencies changed: {suite}")
        write_json(workspace / "manifest.json", manifest)
        manifests.append(manifest)
    with ThreadPoolExecutor(max_workers=3) as pool:
        compilation = list(pool.map(lambda m: compile_suite(m, args.output, command[0], environment, setup), manifests))
    compiled = dict(zip((m["suite"] for m in manifests), compilation))
    write_json(args.output / "compilation.json", compiled)
    if args.prepare_only:
        checkpoint(args.output, {"stage": "prepared", "compiled": {s: dict(Counter(v["status"] for v in ms.values()))
                                                                    for s, ms in compiled.items()}})
        return
    harness = args.output / "harness"
    harness.mkdir()
    write_json(harness / "setup.json", {**setup, "name": "RQ1Baseline"})
    shutil.copy2(ROOT / "scripts/RQ1Baseline.lean", harness / "RQ1Baseline.lean")
    result = subprocess.run([command[0], "--setup", str(harness / "setup.json"), "-o",
                             str(harness / "RQ1Baseline.olean"), str(harness / "RQ1Baseline.lean")],
                            cwd=harness, env=environment, text=True, capture_output=True, timeout=120)
    (harness / "compile.log").write_text(result.stdout + result.stderr)
    if result.returncode:
        raise RuntimeError(f"harness compilation failed; see {harness / 'compile.log'}")
    jobs = [(c, v) for c in selected for v in args.variants]
    random.Random(args.seed).shuffle(jobs)
    write_json(args.output / "schedule.json", [{"case": c["id"], "variant": v} for c, v in jobs])
    results = []
    for case, variant in jobs:
        checkpoint(args.output, {"stage": "running", "case": case["id"], "variant": variant,
                                 "completed": len(results), "total": len(jobs)})
        module = compiled[case["suite"]][case["module"]]
        if (case["id"], variant) in reused:
            record = reused[(case["id"], variant)]
        elif module["status"] != "compiled":
            record = {"case": case["id"], "suite": case["suite"], "classification": case["classification"],
                      "variant": variant, "status": "preparation_failed", "error": json.dumps(module)}
        else:
            record = run_case(case, variant, args, command[0], environment, setup)
        results.append(record)
        with (args.output / "results.jsonl").open("a") as handle:
            handle.write(json.dumps(record) + "\n")
        summarize_results(args.output, results, selected)
        print(f"{len(results)}/{len(jobs)} {case['id']} {variant}: {record['status']}", flush=True)
    metadata.update(complete=True, finished_at=now(), completed_runs=len(results),
                    source_unchanged=hashes == source_hashes())
    write_json(args.output / "metadata.json", metadata)
    checkpoint(args.output, {"stage": "complete", "completed": len(results), "total": len(jobs),
                             "source_unchanged": metadata["source_unchanged"]})
    if previous is not None:
        comparison = {}
        for variant in args.variants:
            before = {r["case"]: r for r in previous if r["variant"] == variant}
            after = {r["case"]: r for r in results if r["variant"] == variant}
            comparison[variant] = {}
            for label, predicate in [("proofs", lambda r: r["status"] == "proved"),
                                     ("synthesis", lambda r: bool(r.get("synthesis_progress"))),
                                     ("instantiation", lambda r: bool(r.get("instantiation_complete"))),
                                     ("elimination", lambda r: bool(r.get("elimination_complete"))),
                                     ("fix_witnesses", lambda r: (r.get("fix_instantiated") or 0) > 0)]:
                old = {c for c, r in before.items() if predicate(r)}
                new = {c for c, r in after.items() if predicate(r)}
                comparison[variant][label] = {"before": len(old), "after": len(new),
                                              "gained": sorted(new - old), "lost": sorted(old - new)}
        write_json(args.output / "comparison.json", comparison)


if __name__ == "__main__":
    main()
