#!/usr/bin/env python3
"""Serial, repeated comparison of fix oracle routing. No admitted benchmarks.

Imports and dependency builds are excluded from Lean's elaboration timer.
Process wall time is recorded separately. Each case/configuration also gets
one unreported warm-up. Order is shuffled reproducibly within each repetition.
"""
import argparse
import csv
import json
import os
from pathlib import Path
import platform
import random
import re
import signal
import statistics
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def source_prefix(path, marker):
    text = (ROOT / path).read_text().split(marker)[0]
    return re.sub(r"^import .*\n", "", text, flags=re.MULTILINE)


def cases():
    return {
        "countdown": {
            "source": source_prefix("Demo/PaCert.lean", "theorem cyc0_pa_cert"),
            "target": "cyc0", "options": "", "auto": "[*]", "smt": "[*]",
        },
        "loop01": {
            "source": source_prefix("Benchmarks/FluxRS/loop01.lean", "theorem testProof"),
            "target": "Test", "options": "", "auto": "[*]", "smt": "[*]",
        },
        "fib_fast": {
            "source": source_prefix("Benchmarks/FluxRS/FibFibFast.lean", "theorem FibFibFast_proof"),
            "target": "FibFibFast", "options": "",
            "auto": "[*] d[fib_spec_fib]", "smt": "[*, fib_spec_fib]",
        },
        "fib_scraped": {
            "source": """
@[grind] def fib (n : Int) : Int :=
  if n ≤ 1 then 1 else fib (n - 1) + fib (n - 2)
  termination_by n.toNat
def memoVC : Prop := ∃ k : Int → Int → Prop,
  (∀ n, n ≤ 1 → k n 1) ∧
  (∀ n a b, ¬ n ≤ 1 → k (n - 1) a → k (n - 2) b → k n (a + b)) ∧
  (∀ n v, k n v → v = fib n)
""",
            "target": "memoVC", "options": "(scrape := head) (defs := [fib])",
            "auto": "[*] d[fib]", "smt": "[*, fib]",
        },
    }


CONFIGS = ["lean", "lean_auto_fallback", "auto_synth", "smt_proof", "auto_synth_smt_proof"]


def tactic(case, config):
    auto = "flex_auto " + case["auto"]
    smt = "smt (timeout := some 1) " + case["smt"]
    routes = {
        "lean": "",
        "lean_auto_fallback": f"(oracle := {auto})",
        "auto_synth": f"(synth := {auto})",
        "smt_proof": f"(proof := {smt})",
        "auto_synth_smt_proof": f"(synth := {auto}) (proof := {smt})",
    }
    return f"fix {case['options']} {routes[config]}"


def run_one(prelude, case, config, timeout):
    content = (prelude + "\n" + case["source"] + '\noracle_bench "measured" in\n'
               + f"theorem measured : {case['target']} := by\n  {tactic(case, config)}\n")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=ROOT / "eval", delete=False) as f:
        f.write(content)
        path = Path(f.name)
    start = time.perf_counter()
    try:
        proc = subprocess.Popen(["lake", "lean", str(path)], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, start_new_session=True)
        timed_out = False
        try:
            output, _ = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(proc.pid, signal.SIGKILL)
            output, _ = proc.communicate()
        result = {"success": False, "timeout": timed_out,
                  "exit_code": proc.returncode, "process_seconds": time.perf_counter() - start,
                  "source": content, "output": output}
        match = re.search(r"^ORACLE_RESULT (.+)$", output, re.MULTILINE)
        if match:
            result.update(json.loads(match[1]))
        result["success"] = result["success"] and proc.returncode == 0 and not timed_out
        result["phases_ms"] = {phase: int(ns) / 1e6 for phase, ns in
                               re.findall(r"^FIX_PHASE (\w+) ns=(\d+)$", output, re.MULTILINE)}
        counts = re.search(r"FIX_CANDIDATES initial=(\d+) surviving=(\d+)", output)
        if counts:
            result["candidates"] = {"initial": int(counts[1]), "surviving": int(counts[2])}
        return result
    finally:
        path.unlink()


def version(command):
    return subprocess.check_output(command, cwd=ROOT, text=True).strip()


def cpu_name():
    try:
        return subprocess.check_output(["sysctl", "-n", "machdep.cpu.brand_string"],
                                       text=True, stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        return platform.processor() or platform.machine()


def aggregate(records):
    rows = []
    for case, config in sorted({(r["case"], r["config"]) for r in records if not r["warmup"]}):
        runs = [r for r in records if (r["case"], r["config"]) == (case, config) and not r["warmup"]]
        successes = [r for r in runs if r["success"]]
        row = {"case": case, "config": config, "successes": len(successes), "runs": len(runs)}
        # Never average successful and failed executions into a speed comparison.
        if len(successes) == len(runs):
            times = [r["elaboration_ns"] / 1e6 for r in runs]
            row.update(median_ms=statistics.median(times), min_ms=min(times), max_ms=max(times),
                       process_median_ms=statistics.median(r["process_seconds"] * 1000 for r in runs),
                       phases_ms={p: statistics.median(r["phases_ms"][p] for r in runs)
                                  for p in ("synthesis", "certificate", "residual")},
                       candidates=runs[0].get("candidates"), axioms=runs[0].get("axioms"))
        rows.append(row)
    return rows


def write_csv(summary, path):
    baselines = {r["case"]: r["median_ms"] for r in summary
                 if r["config"] == "lean" and "median_ms" in r}
    fields = ["case", "config", "successes", "runs", "median_ms", "min_ms", "max_ms",
              "process_median_ms", "synthesis_ms", "certificate_ms", "residual_ms",
              "slowdown_vs_lean"]
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        for row in summary:
            flat = {k: row[k] for k in fields if k in row}
            for phase, ms in row.get("phases_ms", {}).items():
                flat[phase + "_ms"] = ms
            if row["case"] in baselines and "median_ms" in row:
                flat["slowdown_vs_lean"] = row["median_ms"] / baselines[row["case"]]
            writer.writerow(flat)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--cases", nargs="+", choices=list(cases()), default=list(cases()))
    parser.add_argument("--configs", nargs="+", choices=CONFIGS, default=CONFIGS)
    parser.add_argument("--timeout", type=float, default=180)
    parser.add_argument("--output", type=Path, default=ROOT / "eval/oracle_results.json")
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    prelude = (ROOT / "eval/OracleBench.lean").read_text()
    data = {"metadata": {"platform": platform.platform(), "cpu": cpu_name(),
                         "lean": version(["lake", "env", "lean", "--version"]),
                         "z3": version(["z3", "--version"]), "repeats": args.repeats,
                         "solver_timeout_seconds": 1, "process_timeout_seconds": args.timeout,
                         "seed": 20261010, "manifest": json.loads((ROOT / "lake-manifest.json").read_text())},
            "records": [], "summary": []}
    rng = random.Random(20261010)
    for rep in range(args.repeats + 1):
        tasks = [(c, cfg) for c in args.cases for cfg in args.configs]
        rng.shuffle(tasks)
        for c, cfg in tasks:
            result = run_one(prelude, cases()[c], cfg, args.timeout)
            result.update(case=c, config=cfg, repetition=rep, warmup=rep == 0)
            data["records"].append(result)
            data["summary"] = aggregate(data["records"])
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(data, indent=2) + "\n")
            duration = result.get("elaboration_ns", 0) / 1e6
            print(f"{'warmup' if rep == 0 else f'run {rep}'} {c:12} {cfg:22} "
                  f"{'OK' if result['success'] else 'FAIL'} {duration:.1f} ms "
                  f"(process {result['process_seconds']:.2f}s)", flush=True)
    print(json.dumps(data["summary"], indent=2))
    write_csv(data["summary"], args.output.with_suffix(".csv"))


if __name__ == "__main__":
    main()
