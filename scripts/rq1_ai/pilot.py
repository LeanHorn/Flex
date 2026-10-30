#!/usr/bin/env python3
"""Run selected RQ1 cases with fresh Codex agents after Lean preparation."""

from __future__ import annotations

import argparse
from collections import Counter
import csv
import json
import os
from pathlib import Path
import random
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time

from prepare import HERE, frozen_sources, write_json
from usage import UsageRecorder

CASES = {
    "flux_to_lean_demo/SortInsertRec": "Acyclic; multiple predicate witnesses and recursive insertion.",
    "flux_to_lean_demo/FibSumLoop": "Cyclic; a small arithmetic loop invariant.",
    "cstr/GhostGPtrStrlen": "Cyclic; a string specification with semantic predicates.",
    "flux_to_lean_demo/SortInsert": "Mixed; array/order specifications and a cyclic loop predicate.",
    "flux_to_lean_demo/SortPartition": "Mixed; partitioning with array/order specifications.",
}
TOOLS = ["task", "edit_proof", "check", "goals", "read_source", "search_source"]


def stop(process):
    if process is None or process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=20)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def interrupt(process):
    """Let Codex cancel and flush telemetry before falling back to termination."""
    if process is None or process.poll() is not None:
        return
    process.send_signal(signal.SIGINT)
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        stop(process)


def allocate_port():
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def codex_command(workspace: Path, trial: Path, guide: Path, port: int,
                  model: str, effort: str, token_limit: int,
                  usage_endpoint: str | None = None) -> list[str]:
    command = ["codex", "exec", "--ignore-user-config", "--ignore-rules", "--ephemeral",
               "--skip-git-repo-check", "--sandbox", "read-only", "-C", str(workspace),
               "-m", model, "--json", "--output-last-message", str(trial / "final.txt")]
    for feature in ["shell_tool", "apps", "plugins", "remote_plugin", "multi_agent",
                    "memories", "hooks", "browser_use", "computer_use", "image_generation",
                    "view_image", "goals", "skill_search", "shell_snapshot"]:
        command += ["--disable", feature]
    # Suppress automatically discovered guides; the experiment guide is the sole task instruction.
    disabled_skills = [{"path": str(p.parent), "enabled": False}
                       for p in (Path.home()/".codex/skills").rglob("SKILL.md")]
    config = {
        "web_search": "disabled", "project_doc_max_bytes": 0,
        "features.skip_host_skill_discovery": True,
        "model_instructions_file": str(guide), "model_reasoning_effort": effort,
        "approval_policy": "never", "agents.enabled": False,
        "suppress_unstable_features_warning": True,
        "features.rollout_budget.enabled": True,
        "features.rollout_budget.limit_tokens": token_limit,
        "features.rollout_budget.prefill_token_weight": 0.0,
        "features.rollout_budget.sampling_token_weight": 1.0,
        "features.rollout_budget.reminder_at_remaining_tokens": [8000, 2000],
        "mcp_servers.rq1.url": f"http://127.0.0.1:{port}/mcp",
        "mcp_servers.rq1.required": True,
        "mcp_servers.rq1.enabled_tools": TOOLS,
        "mcp_servers.rq1.tool_timeout_sec": 610,
        "mcp_servers.rq1.default_tools_approval_mode": "approve",
    }
    for key, value in config.items():
        command += ["-c", key + "=" + json.dumps(value)]
    if usage_endpoint:
        command += ["-c", 'otel.exporter={otlp-http={endpoint=' + json.dumps(usage_endpoint)
                    + ',protocol="json"}}', "-c", "otel.log_user_prompt=false"]
    for tool in TOOLS:
        command += ["-c", f'mcp_servers.rq1.tools.{tool}.approval_mode="approve"']
    # TOML inline tables use '=' rather than JSON's ':'.
    entries = ",".join("{path="+json.dumps(x["path"])+",enabled=false}" for x in disabled_skills)
    command += ["-c", "skills.config=["+entries+"]"]
    command += ["Complete the assigned Lean proof using only the six rq1 MCP tools. "
                "Call task first, follow the supplied guide, and stop when complete is true. "
                "Do not inspect other files or request help. If the budget is exhausted, "
                "leave your best attempt and report that it remains incomplete."]
    return command


def read_events(path: Path):
    if not path.exists():
        return []
    result = []
    for line in path.read_text().splitlines():
        try:
            result.append(json.loads(line))
        except json.JSONDecodeError:
            pass  # The writer may still be finishing its latest line.
    return result


def summarize(output: Path, results: list[dict], planned: int):
    write_json(output / "results.json", results)
    fields = ["case", "arm", "status", "automatic", "complete", "preparation_seconds",
              "agent_seconds", "end_to_end_seconds", "input_tokens", "cached_input_tokens",
              "output_tokens", "reasoning_output_tokens", "proof_edits", "prefix_executions",
              "lean_check_seconds", "agent_exit_code", "usage_available", "usage_complete",
              "usage_source", "usage_responses"]
    with (output / "results.csv").open("w", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=fields, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(results)
    write_json(output / "summary.json", {
        "completed_trials": len(results), "planned_trials": planned,
        "conditions": {arm: {
            "completed_trials": len([r for r in results if r["arm"] == arm]),
            "automatic": sum(r.get("automatic", False) for r in results if r["arm"] == arm),
            "proved": sum(r.get("complete", False) for r in results if r["arm"] == arm),
            "incomplete_token_records": sum(not r.get("usage_complete", False)
                                             for r in results if r["arm"] == arm),
            "outcomes": dict(Counter(r["status"] for r in results if r["arm"] == arm)),
        } for arm in ["original", "zap", "zap_fix"]}})


def run_trial(manifest: Path, job: dict, runtime: Path, model: str, effort: str,
              completed: int) -> dict:
    output = manifest.parent
    data = json.loads(manifest.read_text())
    planned = len(data["schedule"])
    trial = output / "trials" / job["case"] / job["arm"] / str(job["repeat"])
    logs = output / "logs" / (job["case"].replace("/", "--") + "--" + job["arm"])
    logs.mkdir(parents=True, exist_ok=False)
    port = allocate_port()
    server = agent = recorder = None
    with (logs / "server.log").open("w") as server_log:
        try:
            started = time.monotonic()
            server = subprocess.Popen([str(runtime), str(HERE / "serve.py"), "--manifest", str(manifest),
                "--case", job["case"], "--arm", job["arm"], "--repeat", str(job["repeat"]),
                "--transport", "streamable-http", "--port", str(port)],
                stdout=server_log, stderr=subprocess.STDOUT)
            write_json(output / "progress.json", {"completed": completed, "total": planned,
                "active": job, "phase": "preparing", "server_pid": server.pid})
            ready_path = trial / "ready.json"
            while not ready_path.exists():
                if server.poll() is not None:
                    raise RuntimeError(f"Preparation failed: {logs / 'server.log'}")
                if time.monotonic()-started > 660:
                    return {**job, "status": "preparation_timeout", "complete": False,
                            "preparation_seconds": time.monotonic()-started}
                time.sleep(.2)
            ready = json.loads(ready_path.read_text())
            base = {**job, "preparation_seconds": ready["preparation_seconds"],
                    "automatic": ready["automatic"]}
            events = read_events(trial / "events.jsonl")
            if sum(e["event"] == "prefix_end" for e in events) != 1:
                raise RuntimeError(f"Preparation did not finish: {trial}")
            if ready["automatic"]:
                result = {**base, "status": "proved_automatically", "complete": True,
                        "agent_seconds": 0, "end_to_end_seconds": ready["preparation_seconds"],
                        "input_tokens": 0, "cached_input_tokens": 0, "output_tokens": 0,
                        "reasoning_output_tokens": 0, "proof_edits": 0, "prefix_executions": 1,
                        "lean_check_seconds": 0, "usage_available": True, "usage_complete": True,
                        "usage_source": "no_agent", "usage_responses": 0}
                write_json(trial / "result.json", result)
                return result
            # The server writes ready only after Lean has finished the prefix. Wait for HTTP binding.
            for _ in range(100):
                try:
                    with socket.create_connection(("127.0.0.1", port), timeout=.1):
                        break
                except OSError:
                    time.sleep(.1)
            else:
                raise RuntimeError("Prepared MCP server did not bind its port")
            with tempfile.TemporaryDirectory(prefix="rq1-agent-") as empty_workspace:
                recorder = UsageRecorder(trial)
                usage_endpoint = recorder.start()
                command = codex_command(Path(empty_workspace), trial, output / "AI.md", port,
                                        model, effort, data["limits"]["agent_tokens"], usage_endpoint)
                write_json(trial / "agent-command.json", command)
                agent_start = time.monotonic()
                timed_out = False
                with (trial / "agent.jsonl").open("w") as stdout, (trial / "agent.stderr").open("w") as stderr:
                    agent = subprocess.Popen(command, stdin=subprocess.DEVNULL, stdout=stdout,
                                             stderr=stderr, start_new_session=True)
                    write_json(output / "progress.json", {"completed": completed, "total": planned,
                        "active": job, "phase": "agent", "agent_pid": agent.pid,
                        "preparation_seconds": ready["preparation_seconds"]})
                    while agent.poll() is None:
                        if recorder.error:
                            raise RuntimeError(f"Token logging failed: {recorder.error}")
                        if time.monotonic()-agent_start > data["limits"]["agent_seconds"]:
                            timed_out = True
                            interrupt(agent)
                            break
                        time.sleep(.5)
                agent_seconds = time.monotonic()-agent_start
                status = json.loads((trial / "status.json").read_text())
                agent_events = read_events(trial / "agent.jsonl")
                final_usage = next((e["usage"] for e in reversed(agent_events)
                                    if e.get("type") == "turn.completed"), {})
                usage = recorder.finish(final_usage, timed_out)
                calls = [e["item"] for e in agent_events if e.get("type") == "item.completed"
                         and e.get("item", {}).get("type") == "mcp_tool_call"]
                unexpected = [c for c in calls if c.get("server") != "rq1" or c.get("tool") not in TOOLS]
                forbidden = [e for e in agent_events if e.get("item", {}).get("type") in
                             {"command_execution", "web_search", "file_change"}]
                if unexpected or forbidden:
                    raise RuntimeError(f"Agent used an unapproved tool: {trial / 'agent.jsonl'}")
                if not any(e["event"] == "agent_start" for e in read_events(trial / "events.jsonl")):
                    raise RuntimeError(f"Agent never reached the MCP task; invalid trial: {trial / 'agent.jsonl'}")
                over_budget = usage.get("output_tokens", 0) > data["limits"]["agent_tokens"]
                complete = status["complete"] and not over_budget and not timed_out
                outcome = ("proved_by_ai" if complete else "agent_timeout" if timed_out else
                           "token_budget" if over_budget else "incomplete" if agent.returncode == 0 else "agent_failed")
                result = {**base, "status": outcome, "complete": complete,
                    "agent_seconds": agent_seconds,
                    "end_to_end_seconds": ready["preparation_seconds"] + agent_seconds,
                    **usage, "proof_edits": sum(e["event"] == "edit" for e in read_events(trial / "events.jsonl")),
                    "prefix_executions": status["prefix_executions"],
                    "lean_check_seconds": status["lean_check_seconds"],
                    "agent_exit_code": agent.returncode}
                write_json(trial / "result.json", result)
                return result
        finally:
            stop(agent)
            stop(server)
            if recorder is not None:
                recorder.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepared", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--model", default="gpt-6-astra")
    parser.add_argument("--effort", default="high")
    parser.add_argument("--cases", type=Path, help="JSON object mapping case IDs to selection reasons")
    parser.add_argument("--seed", type=int, default=20261030)
    parser.add_argument("--agent-seconds", type=int, default=1800,
                        help="AI wall-time budget per trial (default: 1800 seconds)")
    args = parser.parse_args()
    if args.agent_seconds <= 0:
        parser.error("--agent-seconds must be positive")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / "experiment.json").exists():
        raise ValueError("Use a fresh pilot output; trials are never overwritten.")
    source = json.loads(args.prepared.read_text())
    source["limits"]["agent_seconds"] = args.agent_seconds
    cases = json.loads(args.cases.read_text()) if args.cases else CASES
    if not isinstance(cases, dict) or not cases:
        raise ValueError("The case selection must be a nonempty object.")
    selected = [t for t in source["tasks"] if t["id"] in cases]
    if len(selected) != 3 * len(cases) or {t["id"] for t in selected} != set(cases):
        raise ValueError("Every selected case needs all three prepared conditions.")
    jobs = [{"case": t["id"], "arm": t["arm"], "repeat": 1} for t in selected]
    random.Random(args.seed).shuffle(jobs)
    source.update(tasks=selected, cases=len(cases), repeats=1, schedule=jobs,
                  classes=dict(Counter(t["classification"] for t in selected if t["arm"] == "original")),
                  agent_model=args.model, agent_reasoning_effort=args.effort,
                  selection=cases, schedule_seed=args.seed, prepared_from=str(args.prepared.resolve()),
                  note="One repetition per condition on a selected subset of RQ1.")
    source["inputs"].update(frozen_sources())
    manifest = output / "experiment.json"
    write_json(manifest, source)
    shutil.copy2(HERE / "AI.md", output / "AI.md")
    snapshot = output / "runner-source"
    snapshot.mkdir()
    for path in HERE.iterdir():
        if path.is_file():
            shutil.copy2(path, snapshot / path.name)
    write_json(output / "runner.json", {"cli": subprocess.check_output(["codex", "--version"], text=True).strip(),
        "model": args.model, "effort": args.effort, "output_token_budget": source["limits"]["agent_tokens"],
        "prefill_token_weight": 0, "wall_seconds": source["limits"]["agent_seconds"],
        "token_recording": "Local per-response OTLP ledger; verified against final CLI usage",
        "timeout_recording": "Retain completed-response counts; mark any unaccounted tail as partial",
        "context": "Fresh ephemeral Codex session; guide and assigned MCP task only.",
        "reference": "https://learn.chatgpt.com/docs/config-file/config-reference"})
    results = []
    try:
        for job in jobs:
            result = run_trial(manifest, job, args.prepared.parent / "runtime/bin/python",
                               args.model, args.effort, len(results))
            results.append(result)
            summarize(output, results, len(jobs))
            print(json.dumps({"completed": len(results), **result}), flush=True)
    finally:
        summarize(output, results, len(jobs))
        write_json(output / "progress.json", {"completed": len(results), "total": len(jobs),
            "phase": "complete" if len(results) == len(jobs) else "stopped"})


if __name__ == "__main__":
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    main()
