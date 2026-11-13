#!/usr/bin/env python3
"""RQ2: identical Zap synthesis, constructive/grind/aesop head certificates."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import random
import re
import statistics
import subprocess
import sys
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import chc_parity as common
from benchmark_flex import freeze

VARIANTS = ("zap", "zap_grind", "zap_aesop")
HELPER = Path(__file__).with_name("RQ2.lean")
HARNESS = (HELPER, Path(__file__).resolve())
SHARED = (ROOT / "scripts/chc_parity.py", ROOT / "scripts/benchmark_flex.py")


def lean_source(case, header):
    source, error = common.case_source(case, header)
    if error:
        raise ValueError(f"{case['case']}: {error}")
    return re.sub(r"run_elab FlexParity.run \(some ``(.*?)\)",
                  lambda m: f"run_elab RQ2.run ``{m[1]} {json.dumps(case['case'])}", source)


def invoke(command, env, path, timeout):
    start = time.monotonic()
    with path.with_suffix(".log").open("w") as log:
        process = subprocess.Popen([*command, str(path)], cwd=ROOT, env=env,
                                   stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            common.terminate_case(process)
            code = "process_timeout"
    output = path.with_suffix(".log").read_text()
    rows = [json.loads(line[4:]) for line in output.splitlines() if line.startswith("RQ2 ")]
    return code, rows, output, (time.monotonic() - start) * 1000


def read_cases(args):
    if args.manifest:
        path = args.manifest.resolve()
        data = json.loads(path.read_text())
        cases = data["cases"] if isinstance(data, dict) else data
        for case in cases:
            for key in ("generated", "source"):
                if case.get(key) and not Path(case[key]).is_absolute():
                    case[key] = str((path.parent / case[key]).resolve())
            if "queries" not in case:
                case.setdefault("format", "lean_statement")
            case.setdefault("inventory_status", "translated")
            case.setdefault("generated_sha256", common.digest(Path(case["generated"])))
            case.setdefault("suite", case["case"].split("/")[0])
        manifests = [{"path": str(path), "sha256": common.digest(path)}]
    else:
        cases, manifests = common.inventory(args.corpus.resolve())
    seen, unique, excluded = set(), [], Counter()
    for case in cases:
        if case["inventory_status"] != "translated":
            excluded[case["inventory_status"]] += 1
            continue
        sha = case.get("source_sha256") or case["generated_sha256"]
        if sha in seen:
            excluded["duplicate_source"] += 1
            continue
        seen.add(sha)
        unique.append(case)
    return unique, {"manifests": manifests, "total": len(cases), "excluded": dict(excluded)}


def classify(args, cases, command, env, header):
    directory = args.output / "classification"
    directory.mkdir()

    def one(task):
        i, case = task
        path = directory / f"case-{i:04}.lean"
        path.write_text(lean_source(case, header))
        invocation = {**env, "RQ2_MODE": "classify",
                      "RQ2_PREPARE_HEARTBEATS": str(args.prepare_heartbeats),
                      "RQ2_PREPARE_TIMEOUT": str(args.prepare_timeout),
                      "RQ2_RECURSION": str(args.recursion)}
        code, rows, _, process_ms = invoke(command, invocation, path, args.process_timeout)
        row = next((r for r in reversed(rows) if r["case"] == case["case"]),
                   {"case": case["case"], "status": "classification_failed"})
        return {**row, "exit": code, "process_ms": process_ms, "log": str(path.with_suffix('.log'))}

    rows = []
    with ThreadPoolExecutor(max_workers=args.classify_workers) as pool:
        for row in pool.map(one, enumerate(cases)):
            rows.append(row)
            common.write_json(args.output / "classification.json", rows)
            print(f"Classified {len(rows)}/{len(cases)}", flush=True)
    return select_cases(args, cases, rows)


def select_cases(args, cases, rows):
    by_id = {c["case"]: c for c in cases}
    eligible = []
    for row in rows:
        if row.get("classification", {}).get("eligible"):
            eligible.append({**by_id[row["case"]], "classification": row["classification"],
                             "prepared_hash": row.get("prepared_hash")})
        elif args.include_unclassified and row["status"] != "classified":
            eligible.append({**by_id[row["case"]], "classification": {"kind": "unclassified"},
                             "classification_failure": row})
    # Equal quotas per graph kind, spread across source suites. No outcome is consulted.
    rng = random.Random(args.seed)
    groups = defaultdict(lambda: defaultdict(list))
    for case in eligible:
        groups[case["classification"]["kind"]][case["suite"]].append(case)
    for suites in groups.values():
        for group in suites.values():
            rng.shuffle(group)
    ordered = {}
    for kind, suites in groups.items():
        names = sorted(suites)
        rng.shuffle(names)
        ordered[kind] = []
        while any(suites.values()):
            for suite in names:
                if suites[suite]:
                    ordered[kind].append(suites[suite].pop())
    count = len(eligible) if args.count == 0 else args.count
    if count > len(eligible):
        raise ValueError(f"only {len(eligible)} eligible cases for requested {count}")
    chosen = []
    while len(chosen) < count:
        for kind in ("acyclic_only", "mixed", "cyclic_only", "unclassified"):
            if ordered.get(kind) and len(chosen) < count:
                chosen.append(ordered[kind].pop(0))
    selection = {"seed": args.seed, "eligible": len(eligible),
                 "classification_counts": dict(Counter(r.get("classification", {}).get("kind", r["status"]) for r in rows)),
                 "method": "source-deduplicated; eligible if Zap eliminates a predicate after its feedback cut; balanced by graph kind; round-robin suites, seeded order within suites; no success filtering",
                 "includes_unclassified": args.include_unclassified,
                 "cases": chosen}
    common.write_json(args.output / "selection.json", selection)
    return chosen


def geomean(values):
    return math.exp(statistics.mean(math.log(v) for v in values)) if values and min(values) > 0 else None


def summarize(output):
    path = output / "results.jsonl"
    rows = [json.loads(l) for l in path.read_text().splitlines()] if path.exists() else []
    selected = json.loads((output / "settings.json").read_text()).get("variants", VARIANTS)
    metrics = ("ms", "heartbeats", "depth", "constants", "kernel_us", "nodes",
               "auxiliary_declarations", "prepare_ms", "sol_ms", "build_ms")
    summaries = {}
    for variant in selected:
        subset = [r for r in rows if r["variant"] == variant]
        good = [r for r in subset if r["status"] == "reduced"]
        summaries[variant] = {"completed": len(subset), "reduced": len(good),
            "outcomes": dict(Counter(r["status"] for r in subset))}
        for key in metrics:
            values = [r[key] for r in good if r.get(key) is not None]
            summaries[variant][f"mean_{key}"] = statistics.mean(values) if values else None
            summaries[variant][f"geomean_{key}"] = geomean(values)
    pairs = {}
    baseline = {(r["case"], r["repeat"]): r for r in rows if r["variant"] == "zap" and r["status"] == "reduced"}
    for variant in selected:
        if variant == "zap":
            continue
        joint = [(baseline[(r["case"], r["repeat"])], r) for r in rows
                 if r["variant"] == variant and r["status"] == "reduced" and (r["case"], r["repeat"]) in baseline]
        pairs[variant] = {"jointly_reduced": len(joint)}
        for key in metrics:
            ratios = [b[key] / a[key] for a, b in joint
                      if a.get(key) is not None and a[key] > 0 and b.get(key) is not None]
            pairs[variant][f"mean_ratio_{key}"] = statistics.mean(ratios) if ratios else None
            pairs[variant][f"geomean_ratio_{key}"] = geomean(ratios)
    groups = []
    for dimension in ("suite", "kind"):
        for group in sorted({r[dimension] for r in rows}):
            for variant in selected:
                subset = [r for r in rows if r[dimension] == group and r["variant"] == variant]
                good = [r for r in subset if r["status"] == "reduced"]
                groups.append({"dimension": dimension, "group": group, "variant": variant,
                    "completed": len(subset), "reduced": len(good),
                    **{f"mean_{k}": statistics.mean(values) if (values :=
                        [r[k] for r in good if r.get(k) is not None]) else None for k in metrics}})
    data = {"completed": len(rows), "variants": summaries, "paired": pairs, "groups": groups}
    common.write_json(output / "summary.json", data)
    fields = ["case", "suite", "kind", "variant", "repeat", "status", "ms", "heartbeats", "depth",
              "constants", "kernel_us", "eliminated", "cut", "head_goals", "process_ms",
              "flex_ms", "flex_heartbeats", "approx_depth", "prepare_ms", "prepare_heartbeats",
              "prepared_hash", "sol_ms", "build_ms", "last_started_subphase", "nodes",
              "auxiliary_declarations", "direct_depth", "direct_nodes", "direct_constants",
              "metrics_version"]
    with (output / "results.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(rows)
    return data


def run(args, cases, command, env, header):
    directory = args.output / "runs"
    directory.mkdir(exist_ok=True)
    completed = set()
    records = args.output / "results.jsonl"
    if records.exists():
        completed = {(r["case"], r["variant"], r["repeat"]) for r in map(json.loads, records.read_text().splitlines())}
    tasks = [(c, v, repeat) for repeat in range(1, args.repeats + 1) for c in cases for v in args.variants]
    random.Random(args.seed).shuffle(tasks)
    lock = threading.Lock()
    pending = iter([(i, task) for i, task in enumerate(tasks) if (task[0]["case"], *task[1:]) not in completed])
    stopped = threading.Event()
    failures = []

    def trial(index, case, variant, repeat):
        if common.digest(Path(case["generated"])) != case["generated_sha256"]:
            raise ValueError(f"input changed: {case['case']}")
        path = directory / f"{index:04}-{variant}.lean"
        path.write_text(lean_source(case, header))
        invocation = {**env, "RQ2_MODE": "run", "RQ2_VARIANT": variant,
                      "RQ2_HEARTBEATS": str(args.heartbeats), "RQ2_TIMEOUT": str(args.timeout),
                      "RQ2_PREPARE_HEARTBEATS": str(args.prepare_heartbeats),
                      "RQ2_PREPARE_TIMEOUT": str(args.prepare_timeout),
                      "RQ2_RECURSION": str(args.recursion)}
        code, parsed, log, process_ms = invoke(command, invocation, path, args.process_timeout)
        row = parsed[-1] if parsed else {"status": "process_timeout" if code == "process_timeout" else "lean_error"}
        metrics = row.pop("certificate", {})
        row.update(case=case["case"], suite=case["suite"], kind=case["classification"]["kind"],
                   variant=variant, repeat=repeat, exit=code, process_ms=process_ms,
                   ms=row.get("zap_ns", 0) / 1e6,
                   flex_ms=row.get("tactic_ns", 0) / 1e6,
                   flex_heartbeats=row.get("heartbeats"),
                   heartbeats=row.get("zap_heartbeats_raw", 0) / 1000)
        row["prepare_ms"] = row.get("prepare_ns", 0) / 1e6
        row["prepare_heartbeats"] = row.get("prepare_heartbeats_raw", 0) / 1000
        starts = re.findall(r"\[phase_start\]\s+(\S+)", log)
        row["last_started_subphase"] = starts[-1] if starts else None
        for label, ns in re.findall(r"\[phase_time\]\s+\S+:(sol|build)=(\d+)", log):
            key = f"{label}_ms"
            row[key] = row.get(key, 0) + int(ns) / 1e6
        row.update(metrics)
        if row["status"] == "constructed":
            row["status"] = "measurement_timeout" if code == "process_timeout" else "measurement_error"
        if "kernel_ns" in row:
            row["kernel_us"] = row["kernel_ns"] / 1000
        counts = re.findall(r"ZAP_RESULT eliminated=(\d+) cut=(\d+) head_goals=(\d+)", log)
        if counts:
            # One Zap run per predicate goal; compare totals with the classification.
            row.update(zip(("eliminated", "cut", "head_goals"),
                           (sum(int(c[i]) for c in counts) for i in range(3))))
        if row["status"] == "certified":
            expected = case["classification"]
            if expected["kind"] == "unclassified":
                row["status"] = "unclassified_reduction"
            elif case.get("prepared_hash") != row.get("prepared_hash"):
                row["status"] = "preparation_mismatch"
            else:
                row["status"] = ("reduced" if code == 0 and row.get("head_goals") == 0
                                 and row.get("eliminated") == expected["eliminable"]
                                 and row.get("cut") == expected["cut"] else "incomplete_reduction")
        row["workers"] = args.workers
        return row

    def worker():
        while True:
            with lock:
                if stopped.is_set() or (args.output / "STOP").exists():
                    stopped.set()
                    return
                item = next(pending, None)
            if item is None:
                return
            index, (case, variant, repeat) = item
            try:
                row = trial(index, case, variant, repeat)
            except BaseException as error:  # stop every worker; re-raised after join
                with lock:
                    failures.append(error)
                    stopped.set()
                return
            with lock:
                with records.open("a") as handle:
                    handle.write(json.dumps(row) + "\n")
                completed.add((case["case"], variant, repeat))
                print(f"{len(completed)}/{len(tasks)} {variant} {row['status']} {case['case']} {row['ms']:.1f} ms", flush=True)
                summarize(args.output)

    # Trials are independent processes; with --workers > 1 they run concurrently and
    # wall-clock metrics (ms, kernel_us) are measured under contention.
    threads = [threading.Thread(target=worker) for _ in range(args.workers)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    if failures:
        raise failures[0]
    if stopped.is_set():
        print("Stopped between cases; --run-only resumes.", flush=True)
        return
    common.write_json(args.output / "completion.json", {"complete": True, "runs": len(completed)})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=ROOT / "evaluation/CHC-COMP/generated")
    parser.add_argument("--manifest", type=Path, help="statement-only corpus manifest (same format as benchmark_flex.py)")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--count", type=int, default=100, help="0 selects every eligible case")
    parser.add_argument("--repeats", type=int, default=1)
    parser.add_argument("--seed", type=int, default=20261103)
    parser.add_argument("--heartbeats", type=int, default=200000)
    parser.add_argument("--prepare-heartbeats", type=int, default=2000000)
    parser.add_argument("--prepare-timeout", type=int, default=120)
    parser.add_argument("--recursion", type=int, default=4096)
    parser.add_argument("--timeout", type=int, default=60, help="internal flex deadline AFTER successful preparation")
    parser.add_argument("--process-timeout", type=int, help="whole-process safeguard; defaults to preparation + flex + 120 seconds")
    parser.add_argument("--variants", nargs="+", choices=VARIANTS, default=list(VARIANTS))
    parser.add_argument("--include-unclassified", action="store_true", help="retain classification failures for targeted diagnostic retries")
    parser.add_argument("--classify-workers", type=int, default=2)
    parser.add_argument("--workers", type=int, default=1,
                        help="concurrent timing trials; >1 is faster but makes ms/kernel_us noisier")
    parser.add_argument("--classify-only", action="store_true")
    parser.add_argument("--run-only", action="store_true", help="resume frozen selection and settings")
    parser.add_argument("--progress", action="store_true")
    args = parser.parse_args()
    args.output = args.output.resolve()
    if args.progress:
        print(json.dumps(summarize(args.output), indent=2))
        return
    if args.run_only:
        saved = json.loads((args.output / "settings.json").read_text())
        for key in ("heartbeats", "timeout", "process_timeout", "recursion", "repeats", "seed",
                    "prepare_heartbeats", "prepare_timeout", "variants", "include_unclassified"):
            setattr(args, key, saved[key])
        cases = json.loads((args.output / "selection.json").read_text())["cases"]
        command = json.loads((args.output / "frozen-command.json").read_text())
        env = {**os.environ, **json.loads((args.output / "frozen-environment.json").read_text())}
        frozen_directory = args.output / "source/evaluation/RQ2"
        if not frozen_directory.is_dir():
            frozen_directory = args.output / "source/scripts"
        header = (frozen_directory / "RQ2.lean").read_text()
        if (args.output / "harness-hashes.json").exists():
            for path, expected in json.loads((args.output / "harness-hashes.json").read_text()).items():
                if common.digest(args.output / path) != expected:
                    raise ValueError(f"frozen harness changed: {path}")
            if common.digest(Path(__file__)) != common.digest(frozen_directory / "benchmark_rq2.py"):
                raise ValueError("runner changed; resume using the recorded runner version")
    else:
        if args.output.exists() and any(args.output.iterdir()):
            parser.error("output must be empty; use --run-only to resume")
        if min(args.repeats, args.timeout, args.heartbeats, args.prepare_timeout,
               args.prepare_heartbeats, args.classify_workers, args.workers) < 1 or args.count < 0:
            parser.error("invalid count or budget")
        if args.process_timeout is None:
            args.process_timeout = args.prepare_timeout + args.timeout + 120
        if args.process_timeout <= args.prepare_timeout + args.timeout:
            parser.error("process timeout must leave time after preparation and flex for kernel measurement")
        if len(args.variants) != len(set(args.variants)):
            parser.error("variants must be distinct")
        cases, metadata = read_cases(args)
        args.output.mkdir(parents=True, exist_ok=True)
        header = HELPER.read_text()
        # Freeze imports used by statements as well as the measurement harness.
        imports = [module for case in cases for module in
                   re.findall(r"^import (.*)$", Path(case["generated"]).read_text(), re.MULTILINE)]
        # Statements may import modules outside Flex's closure; build them before freezing.
        subprocess.run(["lake", "build", "Flex", *dict.fromkeys(m.strip() for m in imports)], cwd=ROOT, check=True,
                       stdout=(args.output / "build.log").open("w"), stderr=subprocess.STDOUT)
        command, env = common.lean_setup(args.output, True, common.with_imports(header, imports))
        command, env = freeze(args.output, command, env)
        for source in HARNESS:
            target = args.output / "source" / source.relative_to(ROOT)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source.read_bytes())
        common.write_json(args.output / "harness-hashes.json", {
            str(Path("source") / source.relative_to(ROOT)): common.digest(source)
            for source in (*HARNESS, *SHARED)})
        common.write_json(args.output / "settings.json", {
            **{k: v for k, v in vars(args).items() if isinstance(v, (str, int, bool))},
            "variants": args.variants,
            "platform": platform.platform(), "timing_workers": args.workers,
            "git_head": common.git_info(["rev-parse", "HEAD"]),
            "git_diff_sha256": hashlib.sha256((common.git_info(["diff"]) or "").encode()).hexdigest(),
            "postprocess": False, "nesting": False, "backends": [], "closeLeaves": False,
            "preprocess": "separate, identical limits for classification and trials", "splitFree": False,
            "metrics_version": 2})
        common.write_json(args.output / "inventory.json", {**metadata, "cases": cases})
        cases = classify(args, cases, command, env, header)
    print(f"Selected {len(cases)}: {dict(Counter(c['classification']['kind'] for c in cases))}", flush=True)
    if not args.classify_only:
        run(args, cases, command, env, header)


if __name__ == "__main__":
    main()
