#!/usr/bin/env python3
"""Deterministic subprocess fixtures for Demo/CHC/Runner.lean; no solver needed."""

import os
import signal
import sys
import time
from pathlib import Path


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
    elif mode == "invalid-utf8":
        sys.stdout.buffer.write(b"\xff\xfe")
        sys.stderr.write("invalid encoding fixture\n")
    elif mode == "argv":
        # The runner must pass argv directly, including shell metacharacters.
        sys.stdout.write("\n".join(sys.argv[2:]))
    elif mode == "close-stdin":
        os.close(sys.stdin.fileno())
        print("stdin closed", flush=True)
        time.sleep(0.1)
    elif mode == "signal-exit":
        os.kill(os.getpid(), signal.SIGTERM)
    elif mode == "cancel":
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        Path(sys.argv[2]).write_text(str(os.getpid()))
        time.sleep(60)
    elif mode == "descendant-pipe":
        # The parent exits, but its descendant retains both output pipes.
        # A heartbeat distinguishes a killed descendant from a live process
        # whose pipes were merely abandoned; checking kill(0) would see zombies.
        child = os.fork()
        if child:
            print(child, flush=True)
            return
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        heartbeat = Path(sys.argv[2])
        until = time.monotonic() + 60
        with heartbeat.open("w") as output:
            while time.monotonic() < until:
                output.write(".")
                output.flush()
                time.sleep(0.02)
        os._exit(0)
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
