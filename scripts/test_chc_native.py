"""Native solver protocol and process-group timeout checks."""

import argparse
from pathlib import Path
import tempfile
import shlex
import threading
import time
import unittest

from chc_native import inspect_input, response, run_one, sexps


class NativeProtocol(unittest.TestCase):
    def test_smt_comments_strings_and_symbols_are_preserved(self):
        source = '''; (check-sat) is a comment
(set-info :source "text with ( and ""quotes""")
(declare-fun |strange;name| () Bool)
(assert |strange;name|)
(check-sat)
(exit)
'''
        inspect_input(source)
        forms = sexps(source)
        self.assertEqual(forms[1], ['declare-fun', '|strange;name|', [], 'Bool'])
        with self.assertRaises(ValueError):
            inspect_input('(check-sat) (assert false)')
        with self.assertRaises(ValueError):
            inspect_input('(set-option :timeout 1) (check-sat)')

    def test_models_statuses_and_errors_are_distinct(self):
        self.assertEqual(response('sat\n((define-fun p () Bool true))', 0), ('sat', True, ''))
        self.assertEqual(response('sat\n(model)', 0), ('sat', True, ''))
        self.assertEqual(response('sat\n()', 0), ('sat', True, ''))
        self.assertEqual(response('sat\n', 0), ('sat', False, ''))
        self.assertEqual(response('unsat\n', 0), ('unsat', False, ''))
        self.assertEqual(response('unknown\n', 0), ('unknown', False, ''))
        self.assertEqual(response('sat\n(error "bad")', 0)[0], 'error')
        self.assertEqual(response('sat\n', 1)[0], 'error')
        self.assertEqual(response('sat\nsat\n', 0)[0], 'error')

    def test_timeout_stops_solver_and_child(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'inputs').mkdir()
            (root / 'inputs/test.smt2').write_text('(check-sat)\n')
            heartbeat = root / 'heartbeat'
            executable = root / 'solver'
            executable.write_text('#!/bin/sh\n(\n i=0\n while :; do\n'
                                  '  i=$((i+1))\n'
                                  f'  printf "%s" "$i" > {shlex.quote(str(heartbeat))}\n'
                                  '  sleep 0.02\n done\n) &\nwait\n')
            executable.chmod(0o755)
            args = argparse.Namespace(output=root, resume=False, z3=str(executable),
                                      eldarica=str(executable), solver_timeout=3)
            task = {'key': 'test', 'sha256': 'test', 'case': 'test.lean'}
            active = {}
            result = run_one(task, 'spacer', args, active, threading.Lock())
            self.assertEqual(result['status'], 'timeout')
            self.assertFalse(active)
            self.assertTrue(heartbeat.exists())
            stopped_value = heartbeat.read_text()
            time.sleep(.15)
            self.assertEqual(heartbeat.read_text(), stopped_value)
            self.assertLess(result['wall_ms'], 5000)


if __name__ == '__main__':
    unittest.main()
