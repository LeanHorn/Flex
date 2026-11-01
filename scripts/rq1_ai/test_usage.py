"""Accounting checks: duplicates, interruptions, warmup, and reconciliation."""

import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from usage import COUNTERS, UsageRecorder


def response(stamp, output, model=True):
    attrs = {"event.name": "codex.sse_event", "event.kind": "response.completed",
             "conversation.id": "test-thread", "event.timestamp": "test-time",
             **{v: "0" for v in COUNTERS.values()}, "output_token_count": str(output)}
    if model:
        attrs["model_reasoning_effort"] = "high"
    return {"resourceLogs": [{"scopeLogs": [{"logRecords": [{
        "timeUnixNano": "0", "observedTimeUnixNano": str(stamp),
        "attributes": [{"key": k, "value": {"stringValue": v}} for k, v in attrs.items()]
    }]}]}]}


class UsageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.recorder = UsageRecorder(self.path)

    def test_distinct_responses_and_retried_batch(self):
        self.recorder.accept(response(1, 3))
        self.recorder.accept(response(2, 7))
        self.recorder.accept(response(2, 7))
        self.assertEqual(self.recorder.totals()["output_tokens"], 10)
        self.assertEqual(len((self.path / "usage-events.jsonl").read_text().splitlines()), 2)

    def test_warmup_is_saved_separately(self):
        self.recorder.accept(response(1, 2, model=False))
        self.recorder.accept(response(2, 5))
        self.assertEqual(self.recorder.totals()["output_tokens"], 5)
        self.assertEqual(self.recorder.totals("auxiliary")["output_tokens"], 2)

    def test_interruption_keeps_durable_partial_usage(self):
        self.recorder.accept(response(1, 17))
        saved = json.loads((self.path / "usage.json").read_text())
        self.assertEqual(saved["usage"]["output_tokens"], 17)
        result = self.recorder.finish({}, interrupted=True)
        self.assertEqual(result["output_tokens"], 17)
        self.assertTrue(result["usage_available"])
        self.assertFalse(result["usage_complete"])

    def test_no_usage_is_unknown_not_zero(self):
        result = self.recorder.finish({}, interrupted=True)
        self.assertFalse(result["usage_available"])
        self.assertNotIn("output_tokens", result)

    def test_complete_usage_must_match_cli(self):
        self.recorder.accept(response(1, 9))
        result = self.recorder.finish({"output_tokens": 9}, interrupted=False)
        self.assertTrue(result["usage_complete"])
        with patch("usage.time.monotonic", side_effect=[0, 6]):
            with self.assertRaisesRegex(RuntimeError, "disagrees"):
                self.recorder.finish({"output_tokens": 10}, interrupted=False)

    def test_negative_counts_rejected(self):
        with self.assertRaises(ValueError):
            self.recorder.accept(response(1, -1))


if __name__ == "__main__":
    unittest.main()
