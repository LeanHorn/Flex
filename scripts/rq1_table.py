#!/usr/bin/env python3
"""Numbers for the paper's RQ1 table (tab:case_studies) from one benchmark_rq1.py run.

    python3 scripts/benchmark_rq1.py --source flex-benchmarks --output OUT --discharge --jobs 8 \\
        --variants zap_fix_deep spacer eldarica
    python3 scripts/rq1_table.py OUT

Flex is zap_fix_deep. Full: the VC is proved and the proof kernel-checked. Partial: not full,
but Zap eliminated at least one predicate (kernel-checked bridge to the residual). Fix's
solutions count only in full proofs: without one they may be too weak, so they are discarded.
Spacer and Eldarica run alone (no Zap, no Fix), one solver call per CHC; Eldarica with
quantified clauses.
Time is the median, over every CHC of the row (failures included), of the time spent in Lean
after imports: inference, residual discharge and kernel check. Total sums that time over the
row's CHCs. Lines of code are not computed.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import statistics

ROWS = [
    ("Fibonacci", lambda suite, name: suite == "flux_to_lean_demo"
     and name.startswith(("Fib", "Memo", "Vectors"))),
    ("Sorting", lambda suite, name: suite == "flux_to_lean_demo" and name.startswith("Sort")),
    ("RingBuffer", lambda suite, name: suite == "flux_to_lean_demo" and name.startswith("Ringbuffer")),
    ("HashTable", lambda suite, name: suite == "hashtable"),
    ("VecDeque", lambda suite, name: suite == "vec_deque"),
    ("CStr", lambda suite, name: suite == "cstr"),
    ("String searching", lambda suite, name: suite == "pattern"),
]
# Trivial test functions, fully automated by every tool, and TickTock, which has no CHCs.
EXCLUDED_CASES = {"flux_to_lean_demo/SortTest1", "flux_to_lean_demo/VectorsTest1"}
EXCLUDED_SUITES = {"tock_theorems"}
COLUMNS = ("zap_fix_deep", "spacer", "eldarica")


def row_of(case: dict) -> str | None:
    if case["id"] in EXCLUDED_CASES or case["suite"] in EXCLUDED_SUITES:
        return None
    name = case["id"].split("/", 1)[1]
    matches = [label for label, member in ROWS if member(case["suite"], name)]
    if len(matches) != 1:
        raise ValueError(f"{case['id']} matches rows {matches}")
    return matches[0]


def seconds(record: dict) -> float:
    if record.get("elapsed_ms") is not None:
        return record["elapsed_ms"] / 1000
    # Killed at the case deadline, or Lean failed before reporting: time after imports.
    if record.get("startup_ms") is not None:
        return (record["process_wall_ms"] - record["startup_ms"]) / 1000
    if record.get("process_wall_ms") is not None:
        return record["process_wall_ms"] / 1000
    raise ValueError(f"no time for {record['case']} {record['variant']}: {record['status']}")


def full(record: dict) -> bool:
    return record["status"] == "proved"


def partial(record: dict) -> bool:
    """Not full, but Zap eliminated a predicate, with a kernel-checked bridge to the residual.

    Zap's solutions are exact, so they are strong enough by construction. Fix's solutions may be
    too weak, so they count only when they end in a full proof. Spacer and Eldarica alone run
    without Zap and so never make partial progress.
    """
    return not full(record) and (record.get("zap_eliminated") or 0) > 0


def median(values: list[float]) -> float | None:
    return statistics.median(values) if values else None


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("run", type=Path, help="benchmark_rq1.py output directory")
    args = parser.parse_args()
    inventory = json.loads((args.run / "inventory.json").read_text())["cases"]
    rows = {case["id"]: row_of(case) for case in inventory}
    selection = json.loads((args.run / "selection.json").read_text())
    chcs = [case["id"] for case in selection if rows[case["id"]]]
    records = [json.loads(line) for line in (args.run / "results.jsonl").read_text().splitlines()]
    counts = Counter((r["case"], r["variant"]) for r in records)
    variants = sorted({r["variant"] for r in records})
    missing = [(c, v) for c in chcs for v in variants if counts[(c, v)] != 1]
    if missing:
        raise ValueError(f"expected one record per CHC and variant, not for {missing[:5]}")
    result = {(r["case"], r["variant"]): r for r in records if r["case"] in chcs}
    anomalies = Counter((v, r["status"]) for (_, v), r in result.items()
                        if r["status"] not in {"proved", "partial", "failed"})
    absent = [v for v in COLUMNS if v not in variants]
    if absent:
        raise ValueError(f"the run has no results for {absent}")

    def summary(variant: str, cases: list[str]) -> dict:
        selected = [result[(c, variant)] for c in cases]
        times = [seconds(r) for r in selected]
        return {"full": sum(map(full, selected)), "partial": sum(map(partial, selected)),
                "time": median(times), "total": sum(times) if times else None}

    print(f"{len(chcs)} CHCs; variants: {', '.join(variants)}")
    if anomalies:
        print("Abnormal outcomes (counted as failures, at their time after imports):")
        for (variant, status), n in sorted(anomalies.items()):
            print(f"  {variant}: {n} {status}")
    table = [(label, [c for c in chcs if rows[c] == label]) for label, _ in ROWS]
    table.append(("All", chcs))

    # Run-to-run differences reach a second, so medians get one decimal and totals none.
    def time(value: float | None) -> str:
        """Median: seconds with one decimal; below that, `<0.1 s`."""
        if value is None:
            return "---"
        return rf"{value:.1f}\,s" if f"{value:.1f}" != "0.0" else r"$<$0.1\,s"

    def duration(value: float | None) -> str:
        """Total: whole seconds; below that, `<1 s`."""
        if value is None:
            return "---"
        return rf"{value:.0f}\,s" if f"{value:.0f}" != "0" else r"$<$1\,s"

    flex, *solvers = COLUMNS
    print(f"Columns: CHCs, {flex} (Full, Partial, Median, Total), "
          + ", ".join(f"{v} (Full, Median, Total)" for v in solvers))
    for label, cases in table:
        progress = summary(flex, cases)
        cells = [f"{len(cases):2}", f"{progress['full']:2}", f"{progress['partial']:2}",
                 time(progress["time"]), duration(progress["total"])]
        for variant in solvers:
            solver = summary(variant, cases)
            cells += [f"{solver['full']:2}", time(solver["time"]), duration(solver["total"])]
        print(f"{label:18} & " + " & ".join(cells) + r" \\")


if __name__ == "__main__":
    main()
