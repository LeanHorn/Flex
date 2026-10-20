"""Coverage and accounting checks for the CHC corpus runner."""

import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest

from chc_parity import case_source, deadline_cleanup, inventory, result_row, summarize


class ParityAccounting(unittest.TestCase):
    def test_failed_translation_and_missing_generated_file_remain_in_inventory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "suite").mkdir()
            for name in ("ok", "bad", "missing"):
                (root / f"{name}.smt2").write_text("(check-sat)")
            (root / "suite/ok.lean").write_text("def Problem := True")
            files = [{
                "input": f"{name}.smt2", "output": f"/stale/path/{name}.lean",
                "status": "failed" if name == "bad" else "translated",
                "queries": [], "error": "unsupported" if name == "bad" else None,
            } for name in ("ok", "bad", "missing")]
            (root / "suite-manifest.json").write_text(json.dumps({
                "project": "suite", "total": 3, "input_root": str(root), "files": files}))
            cases, _ = inventory(root)
            self.assertEqual(len(cases), 3)
            self.assertEqual({c["inventory_status"] for c in cases},
                             {"translated", "translation_failed", "generated_missing"})
            summary = summarize(cases, cases[:1], [], ["spacer"])
            self.assertEqual(summary["unselected_files"], 2)
            self.assertEqual(summary["expected_runs"], 1)

    def test_unknown_and_timeout_are_not_answer_agreement(self):
        record = {"case": "x", "backend": "spacer", "inventory_status": "translated",
                  "status": "solver_timeout", "wall_ms": 1, "error": "", "events": [
                      {"stage": "native_solver", "status": "unknown"},
                      {"stage": "solver", "status": "unknown"}]}
        self.assertIsNone(result_row(record)["answer_agreement"])
        record["events"][0]["status"] = "sat"
        record["events"][1]["status"] = "unsat"
        self.assertIs(result_row(record)["answer_agreement"], False)
        record["events"][1].update(status="error", solver_status="sat", model_available=False)
        self.assertIs(result_row(record)["answer_agreement"], True)
        self.assertEqual(result_row(record)["flex_outcome"], "error")

    def test_partial_requires_kernel_check_and_running_events_do_not_count(self):
        case = {"case": "x", "inventory_status": "translated"}
        record = {**case, "backend": "spacer", "status": "partial", "wall_ms": 1,
                  "error": "", "events": [
                      {"stage": "import", "status": "running"},
                      {"stage": "import", "status": "ok"},
                      {"stage": "kernel", "status": "ok"}]}
        summary = summarize([case], [case], [record], ["spacer"])["backends"]["spacer"]
        self.assertEqual(summary["certified_partial"], 1)
        self.assertEqual(summary["fully_proved"], 0)
        self.assertEqual(summary["stages"]["import"], {"ok": 1})
        record["events"][-1]["status"] = "error"
        summary = summarize([case], [case], [record], ["spacer"])["backends"]["spacer"]
        self.assertEqual(summary["certified_partial"], 0)

    def test_template_proofs_are_excluded(self):
        with tempfile.TemporaryDirectory() as directory:
            generated = Path(directory) / "case.lean"
            generated.write_text(
                "import Mathlib.Data.Real.Basic\nnamespace Example\nsection\n"
                "def Problem : Prop := True\nend\n\n-- Proofs\n\n"
                "theorem problem : Problem := by sorry\nend Example\n")
            case = {"case": "case", "inventory_status": "translated",
                    "generated": str(generated), "namespace": "Example",
                    "queries": [{"target_kind": "model_existence",
                                 "goal_name": "Example.Problem"}]}
            source, unavailable = case_source(case, "import Flex")
            self.assertFalse(unavailable)
            self.assertNotIn("sorry", source)
            self.assertIn("import Mathlib.Data.Real.Basic", source.split("namespace")[0])
            self.assertIn("FlexParity.run (some ``Example.Problem)", source)

    def test_deadline_allows_solver_in_separate_group_to_be_reaped(self):
        with tempfile.TemporaryDirectory() as directory:
            events = Path(directory) / "events.jsonl"
            child = "import time; time.sleep(0.15)"
            parent = (
                "import subprocess,sys,time,json; from pathlib import Path; "
                f"events=Path({str(events)!r}); "
                "events.write_text(json.dumps({'stage':'solver','status':'running'})+'\\n'); "
                f"p=subprocess.Popen([sys.executable,'-c',{child!r}],start_new_session=True); "
                "print(p.pid,flush=True); p.wait(); "
                "events.write_text(json.dumps({'stage':'solver','status':'sat'})+'\\n'); "
                "time.sleep(120)")
            process = subprocess.Popen([sys.executable, "-c", parent], text=True,
                                       stdout=subprocess.PIPE, start_new_session=True)
            child_pid = int(process.stdout.readline())
            try:
                self.assertTrue(deadline_cleanup(process, events, 0.5))
                with self.assertRaises(ProcessLookupError):
                    os.kill(child_pid, 0)
            finally:
                process.stdout.close()
                for pid in (child_pid, process.pid):
                    try:
                        os.killpg(pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                process.wait()


if __name__ == "__main__":
    unittest.main()
