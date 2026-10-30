#!/usr/bin/env python3
"""Prepare the 61 RQ1 tasks without reading or copying their existing proofs."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import shlex
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE.parent))
from rq1_corpus import collect_dependencies, inventory, snapshot_suite

ARMS = ("original", "zap", "zap_fix")
MARKER = "  -- EDITABLE PROOF\n"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def frozen_sources() -> dict[str, str]:
    paths = sorted((ROOT / "Flex").rglob("*.lean"))
    paths += [ROOT / "Flex.lean", ROOT / "lakefile.lean", ROOT / "lake-manifest.json",
              ROOT / "lean-toolchain", ROOT / "native/chc_process.cpp"]
    paths += sorted(p for p in HERE.iterdir() if p.is_file())
    return {str(p): digest(p) for p in paths}


def write_launcher(output: Path) -> None:
    write_json(output / "mcp.json", {
        "mcpServers": {"rq1-proof": {"url": "http://127.0.0.1:8765/mcp"}}})
    command = " ".join(shlex.quote(str(p)) for p in
                       [output / "runtime/bin/python", HERE / "serve.py"])
    manifest = shlex.quote(str(output / "experiment.json"))
    script = output / "start-trial.sh"
    script.write_text('#!/bin/sh\nset -eu\n'
                      'if [ "$#" -ne 3 ]; then\n'
                      '  echo "Usage: start-trial.sh SUITE/NAME original|zap|zap_fix REPEAT" >&2\n'
                      '  exit 2\nfi\n'
                      f'exec {command} --manifest {manifest} --case "$1" --arm "$2" '
                      '--repeat "$3" --transport streamable-http --port 8765\n')
    script.chmod(0o755)


def template(case: dict, arm: str) -> str:
    return (f"import {case['module']}\nimport RQ1Support\n\nopen F\n\n"
            "set_option maxHeartbeats 8000000\nset_option maxRecDepth 16384\n\n"
            f"theorem RQ1_result : {case['declaration']} := by\n"
            f"  unfold {case['declaration']}\n  rq1_prefix {json.dumps(arm)}\n"
            + MARKER + "  all_goals sorry\n\nrq1_verify RQ1_result\n")


def prepare(source: Path, output: Path, repeats: int, seed: int) -> None:
    if output.exists():
        raise ValueError("Use a fresh output directory; existing trials must not be overwritten.")
    cases = [case for case in inventory(source) if case["selected"]]
    if len(cases) != 61:
        raise ValueError(f"Expected exactly 61 invariant-bearing VCs, found {len(cases)}")
    output.mkdir(parents=True)
    shutil.copy2(HERE / "AI.md", output / "AI.md")
    dependency_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    tasks = []
    build_results = {}
    for suite in sorted({case["suite"] for case in cases}):
        project = output / "projects" / suite
        selected = [case for case in cases if case["suite"] == suite]
        snapshot = snapshot_suite(source, suite, selected, project)
        (project / "LeanProofs.lean").write_text(
            "".join(f"import {case['module']}\n" for case in selected))
        shutil.copy2(ROOT / "lean-toolchain", project / "lean-toolchain")
        shutil.copy2(HERE / "Support.lean", project / "RQ1Support.lean")
        (project / "lakefile.toml").write_text(
            'name = "rq1_experiment"\nversion = "0.1.0"\n'
            'defaultTargets = ["LeanProofs", "RQ1Support"]\n\n'
            '[[require]]\nname = "Flex"\npath = ' + json.dumps(str(ROOT)) + '\n\n'
            '[[lean_lib]]\nname = "LeanProofs"\n\n'
            '[[lean_lib]]\nname = "RQ1Support"\n')
        packages = project / ".lake/packages"
        packages.mkdir(parents=True)
        for package in dependency_manifest["packages"]:
            name = package["name"]
            target = ROOT / ".lake/packages" / name
            if not target.is_dir():
                raise FileNotFoundError(f"Build Flex dependencies first: {target}")
            (packages / name).symlink_to(target, target_is_directory=True)
        manifest = {**dependency_manifest, "name": "rq1_experiment", "packages": [
            {"type": "path", "dir": str(ROOT), "name": "Flex", "scope": "",
             "inherited": False, "configFile": "lakefile.lean", "manifestFile": "lake-manifest.json"},
            *[{**p, "inherited": True} for p in dependency_manifest["packages"]]]}
        write_json(project / "lake-manifest.json", manifest)
        start = time.monotonic()
        with (project / "build.log").open("w") as log:
            result = subprocess.run(["lake", "build", "LeanProofs", "RQ1Support"],
                                    cwd=project, stdout=log, stderr=subprocess.STDOUT)
        build_results[suite] = {"seconds": time.monotonic() - start,
                                "exit_code": result.returncode,
                                "specification_modules": len(snapshot["modules"])}
        write_json(output / "builds.json", build_results)
        if result.returncode:
            raise RuntimeError(f"Preparation failed: {project / 'build.log'}")
        print(f"{suite}: {len(selected)} VCs, dependencies built in "
              f"{build_results[suite]['seconds']:.1f}s", flush=True)
        for case in selected:
            sources = [str(p.relative_to(source / suite)) for p in
                       collect_dependencies(source / suite, case["module"])]
            for arm in ARMS:
                task = {**case, "arm": arm, "project": str(project), "sources": sources,
                        "template": template(case, arm)}
                tasks.append(task)
        write_json(project / "specification.json", snapshot)
    order = [{"case": case["id"], "arm": arm, "repeat": repeat}
             for repeat in range(1, repeats + 1) for case in cases for arm in ARMS]
    random.Random(seed).shuffle(order)
    project_inputs = {}
    for project in (output / "projects").iterdir():
        for path in project.rglob("*.lean"):
            if ".lake" not in path.parts:
                project_inputs[str(path)] = digest(path)
        for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
            project_inputs[str(project / name)] = digest(project / name)
    write_json(output / "experiment.json", {
        "schema": 1, "source": str(source), "flex_root": str(ROOT),
        "flex_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source, text=True).strip(),
        "classes": dict(Counter(case["classification"] for case in cases)),
        "cases": len(cases), "conditions": list(ARMS), "tasks": tasks,
        "repeats": repeats, "seed": seed, "schedule": order,
        "inputs": {**frozen_sources(), **project_inputs},
        "limits": {"pa_seconds": 60, "preparation_seconds": 180,
                   "check_seconds": 600, "agent_seconds": 1800, "agent_tokens": 16000,
                   "max_heartbeats": 8000000, "max_rec_depth": 16384},
        "agent_model": None,
        "note": "Pin the agent model before trials. No AI trials or synthesis sweeps were run during preparation."
    })
    write_launcher(output)
    print(f"Ready: {output / 'experiment.json'} ({len(tasks)} tasks)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT.parent / "flex-benchmarks")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--seed", type=int, default=20261030)
    args = parser.parse_args()
    prepare(args.source.resolve(), args.output.resolve(), args.repeats, args.seed)
