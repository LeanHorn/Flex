#!/usr/bin/env python3
"""One persistent Lean session, one RQ1 task, and a restricted MCP interface."""

from __future__ import annotations

import argparse
import atexit
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import threading
import time

from leanclient import DocumentContentChange, LeanLSPClient
from mcp.server.fastmcp import FastMCP

from prepare import MARKER, digest, write_json

SUFFIX = "\nrq1_verify RQ1_result\n"
FORBIDDEN = re.compile(r"\b(flex|zap|fix|spacer|eldarica|solve|solve_fixpoint|"
                       r"fixpoint|pa_cert|fusion|flex_auto|auto|native_decide|"
                       r"run_tac|run_elab|unsafe|axiom)\b")


class Session:
    def __init__(self, manifest: Path, case: str, arm: str, repeat: int,
                 label: str | None = None):
        self.manifest_path = manifest.resolve()
        self.experiment = json.loads(self.manifest_path.read_text())
        if label is None and not 1 <= repeat <= self.experiment["repeats"]:
            raise ValueError("Repeat is outside the frozen experiment schedule.")
        self.task_info = next(t for t in self.experiment["tasks"]
                              if t["id"] == case and t["arm"] == arm)
        for path, expected in self.experiment["inputs"].items():
            if digest(Path(path)) != expected:
                raise ValueError(f"Frozen input changed; prepare a new experiment: {path}")
        self.project = Path(self.task_info["project"])
        self.directory = self.manifest_path.parent / "trials" / case / arm / (label or str(repeat))
        self.directory.mkdir(parents=True, exist_ok=False)
        self.events = self.directory / "events.jsonl"
        self.events.touch()
        os.environ["FLEX_AI_EVENTS"] = str(self.events)
        name = f"{self.task_info['name']}_{arm}_{label or repeat}"
        self.path = f"Tasks/{name}.lean"
        source = self.project / self.path
        source.parent.mkdir(exist_ok=True)
        self.prefix = self.task_info["template"].split(MARKER)[0] + MARKER
        source.write_text(self.task_info["template"])
        self.lock = threading.RLock()
        self.client = None
        self.agent_started = None
        self.closed = False
        self.operations = 0
        self.total_check_seconds = 0.0
        self.started = time.monotonic()
        self.caffeinate = None
        if sys.platform == "darwin":
            self.caffeinate = subprocess.Popen(["caffeinate", "-i", "-w", str(os.getpid())],
                                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        atexit.register(self.close)
        self.client = LeanLSPClient(str(self.project), max_opened_files=1,
                                    initial_build=False, prevent_cache_get=True)
        self.diagnostics = self._diagnostics()
        self.preparation_seconds = time.monotonic() - self.started
        self.initial_complete = self._complete()
        self.initial_goals = self._goals_at_prefix()
        self._record("ready", preparation_seconds=self.preparation_seconds,
                     automatic=self.initial_complete, goals=self.initial_goals)
        self._save_status()

    def _record(self, event: str, **fields) -> None:
        with self.events.open("a") as file:
            file.write(json.dumps({"event": event, "elapsed_seconds": time.monotonic()-self.started,
                                   **fields}) + "\n")

    def _diagnostics(self):
        return self.client.get_diagnostics(self.path, inactivity_timeout=600, max_timeout=600)

    def _complete(self) -> bool:
        return self.diagnostics.success and any(
            d.get("message", "").strip() == "RQ1_PROOF_COMPLETE"
            for d in self.diagnostics.diagnostics)

    def _prefix_runs(self) -> int:
        return sum(json.loads(line).get("event") == "prefix_start"
                   for line in self.events.read_text().splitlines())

    def _goals_at_prefix(self):
        result = self.client.get_goal(self.path, len(self.prefix.splitlines()), 2)
        return result.get("goals", []) if result is not None else None

    def _save_status(self):
        body = self.client.get_file_content(self.path)
        (self.directory / "Task.lean").write_text(body)
        write_json(self.directory / "status.json", {
            "case": self.task_info["id"], "arm": self.task_info["arm"],
            "preparation_seconds": self.preparation_seconds,
            "automatic": self.initial_complete, "complete": self._complete(),
            "prefix_executions": self._prefix_runs(), "tool_operations": self.operations,
            "tool_session_seconds": 0 if self.agent_started is None else time.monotonic()-self.agent_started,
            "lean_check_seconds": self.total_check_seconds,
            "proof_sha256": hashlib.sha256(body.encode()).hexdigest(),
            "diagnostics": self.diagnostics.diagnostics,
            "closed": self.closed})

    def _begin(self):
        if self.agent_started is None:
            self.agent_started = time.monotonic()
            self._record("agent_start")
        if time.monotonic()-self.agent_started > self.experiment["limits"]["agent_seconds"]:
            raise TimeoutError("The agent time budget is exhausted.")
        self.operations += 1

    def task(self) -> dict:
        with self.lock:
            self._begin()
            return {"case": self.task_info["id"], "condition": self.task_info["arm"],
                    "source": self.client.get_file_content(self.path),
                    "remaining_goals": self._goals_at_prefix(),
                    "complete": self._complete(), "allowed_sources": self.task_info["sources"],
                    "preparation_seconds": self.preparation_seconds}

    def check(self) -> dict:
        with self.lock:
            self._begin()
            start = time.monotonic()
            self.diagnostics = self._diagnostics()
            seconds = time.monotonic()-start
            self.total_check_seconds += seconds
            self._record("check", seconds=seconds, complete=self._complete(),
                         prefix_executions=self._prefix_runs())
            self._save_status()
            return {"complete": self._complete(), "diagnostics": self.diagnostics.diagnostics,
                    "seconds": seconds, "prefix_executions": self._prefix_runs()}

    def edit_proof(self, proof: str) -> dict:
        with self.lock:
            self._begin()
            if FORBIDDEN.search(proof):
                raise ValueError("The editable proof may not run synthesis or metaprogramming; see AI.md.")
            current = self.client.get_file_content(self.path)
            if not current.startswith(self.prefix) or not current.endswith(SUFFIX):
                raise ValueError("The frozen task changed outside the tool.")
            # Preserve the syntax and position of the entire elaborated prefix.
            start = (len(self.prefix.splitlines()), 0)
            end_text = current[:-len(SUFFIX)]
            end = (len(end_text.split("\n"))-1, len(end_text.split("\n")[-1]))
            body = "\n".join("  " + line if line else "" for line in proof.rstrip().splitlines()) + "\n"
            self.client.update_file(self.path, [DocumentContentChange(body, start=start, end=end)])
            (self.project / self.path).write_text(self.client.get_file_content(self.path))
            self._record("edit", proof=proof)
            return self.check()

    def goals(self, line: int, column: int = 1):
        with self.lock:
            self._begin()
            if line < 1 or column < 1:
                raise ValueError("Positions are one-based.")
            result = self.client.get_goal(self.path, line-1, column-1)
            return result.get("goals", []) if result is not None else None

    def read_source(self, path: str, start_line: int = 1, end_line: int = 120) -> dict:
        with self.lock:
            self._begin()
            if path not in self.task_info["sources"]:
                raise ValueError("Only this task's listed specification sources are available.")
            if start_line < 1 or end_line < start_line or end_line-start_line >= 200:
                raise ValueError("Read between 1 and 200 lines at a time.")
            lines = (self.project / path).read_text().splitlines()
            return {"path": path, "total_lines": len(lines), "text": "\n".join(
                f"{i+1}: {line}" for i, line in enumerate(lines)
                if start_line <= i+1 <= end_line)}

    def search_source(self, query: str) -> list[dict]:
        with self.lock:
            self._begin()
            if not query.strip():
                raise ValueError("Supply a nonempty literal search string.")
            results = []
            for path in self.task_info["sources"]:
                for i, line in enumerate((self.project / path).read_text().splitlines(), 1):
                    if query in line:
                        results.append({"path": path, "line": i, "text": line})
                        if len(results) == 40:
                            return results
            return results

    def close(self):
        if self.closed:
            return
        self.closed = True
        if self.client is not None:
            if hasattr(self, "initial_complete"):
                self._save_status()
            self.client.close()
        if self.caffeinate is not None:
            self.caffeinate.terminate()
            self.caffeinate.wait()
        atexit.unregister(self.close)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--case", required=True)
    parser.add_argument("--arm", choices=["original", "zap", "zap_fix"], required=True)
    parser.add_argument("--repeat", type=int, default=1)
    parser.add_argument("--transport", choices=["stdio", "streamable-http"], default="stdio")
    parser.add_argument("--port", type=int, default=8765)
    args = parser.parse_args()
    def terminate(_signum, _frame):
        raise SystemExit(0)
    signal.signal(signal.SIGTERM, terminate)
    session = Session(args.manifest, args.case, args.arm, args.repeat)
    server = FastMCP("rq1-proof", host="127.0.0.1", port=args.port,
                     instructions="Follow the supplied AI.md. Work only on the assigned task.")
    server.add_tool(session.task, name="task", description="Read the assigned task and current residual goals.")
    server.add_tool(session.edit_proof, name="edit_proof", description="Replace only the editable tactic block; return Lean diagnostics.")
    server.add_tool(session.check, name="check", description="Check the current proof in the persistent Lean session.")
    server.add_tool(session.goals, name="goals", description="Inspect goals at a one-based line and column in the task.")
    server.add_tool(session.read_source, name="read_source", description="Read the assigned VC or one of its specification dependencies.")
    server.add_tool(session.search_source, name="search_source", description="Literal search in this task's specification dependencies only.")
    write_json(session.directory / "ready.json", {
        "pid": os.getpid(), "transport": args.transport, "port": args.port,
        "preparation_seconds": session.preparation_seconds,
        "automatic": session.initial_complete})
    try:
        server.run(transport=args.transport)
    finally:
        session.close()


if __name__ == "__main__":
    main()
