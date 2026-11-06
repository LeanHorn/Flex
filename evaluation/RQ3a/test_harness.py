"""Check resumable records and the CSV contract without running solvers."""
import csv
import json
from pathlib import Path
import tempfile
import unittest
from types import SimpleNamespace

import benchmark
import report


class HarnessTests(unittest.TestCase):
    def test_reserved_budgets_and_backend_accounting(self):
        args=SimpleNamespace(flex_timeout=180,combined_timeout=360,case_timeout=None)
        for config in ['flex','se_zap_fix']:
            self.assertEqual(benchmark.budgets(config,args),(360,480))
            self.assertEqual(benchmark.stage_budget(config,args),180)
        self.assertEqual(benchmark.stage_budget('se',args),0)
        legacy={'flex_timeout':180}
        self.assertIsNone(report.stage_budget('flex',legacy))
        self.assertEqual(report.stage_budget('se_zap_fix',legacy),180)
        current={**legacy,'configuration_budgets':{'flex':{'stage_timeout':180}}}
        self.assertEqual(report.stage_budget('flex',current),180)
        phases=[{'phase':'attempt/eldarica','status':'start'},
                {'phase':'attempt/eldarica','status':'start'},
                {'phase':'attempt/spacer','status':'skipped_budget'}]
        calls=[{'stage':'chc/solver','solver_backend':'eldarica','backend_attempt':i}
               for i in [1,1,2]]
        usage=report.backend_usage(phases,calls)
        self.assertEqual(usage['eldarica_attempts'],2)
        self.assertEqual(usage['eldarica_calls_completed'],3)
        self.assertEqual(usage['eldarica_retries_completed'],1)
        self.assertEqual(usage['spacer_skip_reasons'],'skipped_budget')

    def test_resume_repairs_only_the_unfinished_record(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            case = {'case': 'query.lean'}
            schedule = benchmark.schedule_cases({'cases': {'b': [case]}}, benchmark.DEFAULTS['b'], 1)
            self.assertEqual(len(schedule), 5)
            record = {'study': 'b', 'case': case['case'], 'configuration': 'se'}
            path = output/'results.jsonl'
            path.write_text(json.dumps(record)+'\n{"case":')
            self.assertEqual(benchmark.resume_records(output, schedule), [record])
            self.assertEqual(len(list(output.glob('results.interrupted-*'))), 1)
            path.write_text(path.read_text()+json.dumps(record)+'\n')
            with self.assertRaisesRegex(ValueError, 'duplicate'):
                benchmark.resume_records(output, schedule)

    def test_portable_phases_and_unfinished_timing(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            record = {'study': 'b', 'case': 'query.lean', 'configuration': 'se',
                      'status': 'case_timeout', 'artifacts': '/old/machine/missing'}
            path = output/'runs/b/cases/se/query/phases.jsonl'
            path.parent.mkdir(parents=True)
            events = [{'phase': 'zap', 'status': 'start', 'heartbeats_raw': 1000},
                      {'phase': 'zap', 'status': 'ok', 'heartbeats_raw': 3000, 'elapsed_ms': 7},
                      {'phase': 'fix', 'status': 'start', 'heartbeats_raw': 4000}]
            path.write_text(''.join(json.dumps(e)+'\n' for e in events)+'{"incomplete":')
            phases = report.phase_events(record, output)
            row, _ = report.row(record, {('b', 'query.lean'): {'suite': 'test', 'bytes': 10}}, {}, phases)
            self.assertEqual(row['zap_ms'], 7)
            self.assertIsNone(row['fix_ms'])
            self.assertFalse(row['phase_log_complete'])
            self.assertFalse(row['predicate_progress'])
            record['phase_events'] = phases
            path.unlink()
            self.assertEqual(report.phase_events(record, output), events)

    def test_coverage_and_native_timing_csv(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            case = {'case': 'query.lean', 'suite': 'test', 'bytes': 10}
            settings = dict(flex_timeout=180, combined_timeout=360, solver_timeout=90,
                            heartbeats=4000000, proof_heartbeats=40000)
            (output/'selection.json').write_text(json.dumps({'cases': {'b': [case]}}))
            (output/'settings.json').write_text(json.dumps(settings))
            identity = {'study': 'b', 'case': 'query.lean', 'phase_events': []}
            terminal = {'stage': 'result', 'status': 'partial', 'kernel_checked': True,
                        'all_predicates_instantiated': True, 'fully_proved': False,
                        'retention': {'heads_known': True, 'remaining_heads': 0}}
            records = [{**identity, 'configuration': 'native_spacer', 'status': 'sat',
                        'model_obtained': True, 'elapsed_ms': 12, 'wall_ms': 100},
                       {**identity, 'configuration': 'se', 'status': 'partial', 'events': [terminal]},
                       {**identity, 'configuration': 'zap_fix', 'status': 'kernel_failed',
                        'events': [{**terminal, 'fully_proved': True}]}]
            (output/'results.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
            _, summary = report.tables(output)
            self.assertEqual(summary['by_configuration']['b/se']['all_heads_eliminated'], 1)
            self.assertEqual(summary['by_configuration']['b/se']['fully_proved'], 0)
            self.assertEqual(summary['by_configuration']['b/zap_fix']['fully_proved'], 0)
            self.assertEqual(summary['native_union']['either_model_observed'], 1)
            with (output/'statistics.csv').open() as f:
                measured = [r for r in csv.DictReader(f) if r['configuration']=='native_spacer'
                            and r['suite']=='ALL' and r['population']=='model_returned' and r['metric']=='native_ms']
            self.assertEqual(float(measured[0]['median']), 12)
            self.assertEqual((output/'discrepancies.csv').read_text().count('\n'), 1)


if __name__ == '__main__':
    unittest.main()
