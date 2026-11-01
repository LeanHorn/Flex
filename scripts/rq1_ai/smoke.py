#!/usr/bin/env python3
"""Check prefix reuse and admission rejection on a few tasks; no AI trial."""

import argparse
import json
from pathlib import Path

from serve import Session


def run(manifest: Path, label: str):
    results = []
    for arm in ["original", "zap", "zap_fix"]:
        session = Session(manifest, "cstr/GhostGPtrStrlen", arm, 0, label)
        try:
            if arm == "original":
                assert not session.initial_complete
            before = session._prefix_runs()
            for proof in ["all_goals skip\nall_goals sorry", "all_goals trace_state\nall_goals sorry"]:
                answer = session.edit_proof(proof)
                assert answer["complete"] == session.initial_complete, "an admission was accepted"
                assert answer["prefix_executions"] == before == 1, "prefix reran after a suffix edit"
            try:
                session.read_source("../another-proof.lean")
                raise AssertionError("source isolation failed")
            except ValueError:
                pass
            try:
                session.edit_proof("flex")
                raise AssertionError("condition could be changed")
            except ValueError:
                pass
            if arm == "zap_fix":
                answer = session.edit_proof("all_goals flex_discharge")
                assert answer["complete"], answer
                assert answer["prefix_executions"] == 1
            results.append({"case": session.task_info["id"], "arm": arm,
                            "preparation_seconds": session.preparation_seconds,
                            "prefix_executions": session._prefix_runs(),
                            "complete": session._complete()})
            print(json.dumps(results[-1]), flush=True)
        finally:
            session.close()
    session = Session(manifest, "flux_to_lean_demo/FibSqrt", "zap_fix", 0, label)
    try:
        assert session.initial_complete, session.diagnostics.diagnostics
        results.append({"case": session.task_info["id"], "arm": "zap_fix", "automatic": True})
    finally:
        session.close()
    (manifest.parent / f"{label}.json").write_text(json.dumps(results, indent=2)+"\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--label", default="smoke")
    args = parser.parse_args()
    run(args.manifest, args.label)
