#!/usr/bin/env python3
"""Deterministic subprocess fixtures for Demo/CHCRunner.lean; no solver needed."""

import os
import signal
import sys
import time


def main() -> None:
    mode = sys.argv[1]
    if mode == "echo":
        sys.stdout.write(sys.stdin.read())
        sys.stderr.write("fixture stderr\n")
    elif mode == "drain":
        # Write more than a pipe buffer before reading stdin. All three pipes
        # must make progress concurrently to avoid a subprocess deadlock.
        for _ in range(16):
            os.write(sys.stdout.fileno(), b"o" * 8192)
            os.write(sys.stderr.fileno(), b"e" * 8192)
        data = sys.stdin.buffer.read()
        print(f"\ninput-bytes={len(data)}")
    elif mode == "exit-error":
        sys.stdout.write("sat\n()\n")
        sys.stderr.write("deliberate process failure\n")
        sys.exit(7)
    elif mode == "utf8":
        # Put a multibyte character across the runner's 4096-byte read boundary.
        sys.stdout.buffer.write(b"a" * 4095 + "€🙂".encode())
    elif mode in ("timeout", "blocked-stdin"):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        print(os.getpid(), flush=True)
        print("waiting for cancellation", file=sys.stderr, flush=True)
        # Both modes ignore graceful termination. The second is invoked with
        # enough input to block its writer because this child never reads it.
        time.sleep(60)
    else:
        raise ValueError(f"unknown fixture mode: {mode}")


if __name__ == "__main__":
    main()
