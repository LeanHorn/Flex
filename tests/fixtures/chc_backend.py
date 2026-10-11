#!/usr/bin/env python3
"""Executable solver stand-in for Demo/CHC/Backends.lean.

The test copies this into a temporary directory alongside the expected script
and response mode. Check argv and the complete input before answering, so a
successful response also checks the backend's wire protocol.
"""

import sys
import time
from pathlib import Path


def main() -> None:
    executable = Path(sys.argv[0])
    backend = executable.name.split()[0]
    expected_args = {
        "spacer": ["-in", "-smt2", "-model", "fp.engine=spacer"],
        "eldarica": ["-in", "-hsmt", "-ssol"],
    }
    if sys.argv[1:] != expected_args[backend]:
        raise ValueError(f"unexpected {backend} arguments: {sys.argv[1:]!r}")
    directory = executable.parent
    expected_input = (directory / "expected.smt2").read_bytes()
    if sys.stdin.buffer.read() != expected_input:
        raise ValueError("backend did not send the complete expected SMT-LIB script")

    mode = (directory / "mode").read_text()
    print(f"fixture backend={backend} mode={mode}", file=sys.stderr, flush=True)
    responses = {
        "sat": "sat\n((define-fun k_0 ((b Bool) (x Int)) Bool (>= x 0)))\n",
        "empty": "sat\n()\n",
        "unsat": "unsat\n",
        "unknown": 'unknown\n(:reason-unknown "fixture incomplete")\n',
        "solver-error": '(error "fixture rejected input")\nsat\n()\n',
        "malformed": "sat\n((define-fun k_0 () Bool true)\n",
        "missing-model": "sat\n",
        "exit-error": "sat\n()\n",
        "timeout": "sat\n",
    }
    print(responses[mode], end="", flush=True)
    if mode == "exit-error":
        sys.exit(7)
    if mode == "timeout":
        time.sleep(60)


if __name__ == "__main__":
    main()
