"""Durable, local token accounting for Codex responses, including interrupted runs."""

from __future__ import annotations

from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import threading
import time


COUNTERS = {
    "input_tokens": "input_token_count",
    "cached_input_tokens": "cached_token_count",
    "cache_write_input_tokens": "cache_write_token_count",
    "output_tokens": "output_token_count",
    "reasoning_output_tokens": "reasoning_token_count",
}


class UsageRecorder:
    """Persist response counts before acknowledging the local OTLP request.

    Successful runs must reconcile with Codex's final usage. On interruption,
    retain the measured responses and explicitly flag any unaccounted tail.
    """

    def __init__(self, directory: Path):
        self.directory = directory
        self.records = []
        self.seen = set()
        self.lock = threading.RLock()
        self.error = None
        self.server = self.thread = None

    def start(self):
        recorder = self

        class Handler(BaseHTTPRequestHandler):
            def do_POST(self):
                try:
                    payload = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
                    recorder.accept(payload)
                    self.send_response(200)
                    self.end_headers()
                    self.wfile.write(b"{}")
                except Exception as error:
                    recorder.error = str(error)
                    self.send_error(500, "Token ledger could not be saved")

            def log_message(self, *_):
                pass

        self.server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        self.thread.start()
        return f"http://127.0.0.1:{self.server.server_port}/v1/logs"

    def accept(self, payload):
        with self.lock:
            for resource in payload.get("resourceLogs", []):
                for scope in resource.get("scopeLogs", []):
                    for record in scope.get("logRecords", []):
                        attrs = {a["key"]: next(iter(a["value"].values()))
                                 for a in record.get("attributes", [])}
                        if attrs.get("event.kind") != "response.completed":
                            continue
                        if not all(key in attrs for key in COUNTERS.values()):
                            raise ValueError("Response completion omitted token counters")
                        # Codex also emits an auxiliary connection warmup. The
                        # model response has request reasoning metadata. Preserve
                        # both separately and reconcile model totals with the CLI.
                        kind = "model" if "model_reasoning_effort" in attrs else "auxiliary"
                        usage = {key: int(attrs[value]) for key, value in COUNTERS.items()}
                        if any(v < 0 for v in usage.values()):
                            raise ValueError("Negative token count")
                        timestamp = record.get("observedTimeUnixNano") or attrs["event.timestamp"]
                        identity = (attrs["conversation.id"], timestamp, attrs["event.name"])
                        if identity in self.seen:
                            continue
                        entry = {"thread_id": identity[0], "time_unix_nano": identity[1],
                                 "event": identity[2], "kind": kind, "usage": usage}
                        # Do not store prompt text, account identifiers, tool
                        # output, or other unrelated telemetry attributes.
                        with (self.directory / "usage-events.jsonl").open("a") as file:
                            file.write(json.dumps(entry) + "\n")
                            file.flush()
                            os.fsync(file.fileno())
                        self.seen.add(identity)
                        self.records.append(entry)
                        self.save()

    def totals(self, kind="model"):
        return {key: sum(r["usage"][key] for r in self.records if r["kind"] == kind)
                for key in COUNTERS}

    def save(self, **extra):
        snapshot = {"usage": self.totals(), "auxiliary_usage": self.totals("auxiliary"),
                    "responses": sum(r["kind"] == "model" for r in self.records),
                    "coverage": "completed_responses", **extra}
        path = self.directory / "usage.json"
        temporary = path.with_suffix(".tmp")
        with temporary.open("w") as file:
            file.write(json.dumps(snapshot, indent=2) + "\n")
            file.flush()
            os.fsync(file.fileno())
        temporary.replace(path)

    def finish(self, final_usage: dict, interrupted: bool):
        # The exporter flushes on graceful exit. Allow in-flight local HTTP
        # delivery to finish before requiring agreement with the final summary.
        until = time.monotonic() + 5
        while final_usage and self.totals() != {k: final_usage.get(k, 0) for k in COUNTERS}:
            if time.monotonic() >= until:
                break
            time.sleep(.1)
        with self.lock:
            if self.error:
                raise RuntimeError(f"Token recording failed: {self.error}")
            measured = self.totals()
            count = sum(r["kind"] == "model" for r in self.records)
            if final_usage:
                expected = {k: final_usage.get(k, 0) for k in COUNTERS}
                if measured != expected:
                    self.save(coverage="mismatch", final_usage=final_usage)
                    raise RuntimeError("Per-response usage disagrees with Codex's final usage")
                self.save(coverage="complete", final_usage=final_usage)
                return {**final_usage, "usage_available": True, "usage_complete": True,
                        "usage_source": "otel_verified_against_cli", "usage_responses": count}
            self.save(coverage="partial" if count else "unknown", interrupted=interrupted)
            return {**(measured if count else {}), "usage_available": bool(count),
                    "usage_complete": False, "usage_source": "otel_completed_responses",
                    "usage_responses": count}

    def close(self):
        if self.server:
            self.server.shutdown()
            self.server.server_close()
            self.thread.join(timeout=5)
