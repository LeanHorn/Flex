"""Shared kvar (κ) classification for VC logs.

`zap`/`fusion` runs before `solve_fixpoint` and reports, via `[fusion] Start
κ: [...]` / `[fusion] End κ: [...]` log lines, the κ's it started with and
the κ's still unsolved afterward (the rest were eliminated as acyclic) — see
Flex/Tactic/Tactics/Fusion.lean. Every eval script that needs to know which
kind of kvars a VC has (none / acyclic-only / cyclic-only / both) must derive
it from these lines rather than any other heuristic.
"""

from __future__ import annotations

import re

FUSION_START_RE = re.compile(
    r"info: .*/(\w+)Proof\.lean:\d+:\d+: \[fusion\] Start κ:\s*\[([^\]]*)\]"
)
FUSION_END_RE = re.compile(r"\[fusion\] End κ:\s*\[([^\]]*)\]")

# Path-qualified variant: captures the directory prefix before `/User/Proof/`
# so callers can disambiguate VCs whose basenames collide across test
# directories (e.g. lean_bench_merged, where many tests share names like
# `Test00Proof.lean`).
FUSION_START_PATHED_RE = re.compile(
    r"info: (\S+)/User/Proof/(\w+)Proof\.lean:\d+:\d+: \[fusion\] Start κ:\s*\[([^\]]*)\]"
)

# `benchPhase` (see below) emits a bare `[phase] fusion:sol=...` line between
# `Start` and `End` whenever fusion has ≥1 acyclic κ to eliminate (the `sol`
# step runs, THEN `End` prints — see Flex/Tactic/Tactics/Fusion.lean). A fixed
# 1-line lookahead for `End` right after `Start` breaks the moment
# `flex.benchPhases` is on, so `_find_end` skips over any such phase lines.
_BARE_PHASE_RE = re.compile(r"^\[phase\]\s+\w+:\w+=\d+\s+ms=\d+$")


def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


def _find_end(lines: list[str], i: int) -> tuple[list[str], int]:
    """From `lines[i]` (a `Start` line), scan forward past any bare `[phase]`
    lines and return (`end` κ list, index of the line consumed as `End` —
    or `i` unchanged if no `End` was found)."""
    j = i + 1
    while j < len(lines) and _BARE_PHASE_RE.match(lines[j]):
        j += 1
    if j < len(lines):
        em = FUSION_END_RE.search(lines[j])
        if em:
            return _items(em.group(1)), j
    return [], i


def classify(acyclic: list[str], cyclic: list[str]) -> str:
    if acyclic and cyclic:
        return "both"
    if acyclic:
        return "acyclic_only"
    if cyclic:
        return "cyclic_only"
    return "none"


def parse_log_kappa(text: str) -> dict[str, str]:
    """Classify each VC from fusion's Start/End κ lists.

    Per the classification rule:
      - no κ's to start with            -> none
      - something before, none after    -> acyclic_only
      - same count before and after     -> cyclic_only (fusion ate nothing)
      - fewer after than before         -> both
    """
    results: dict[str, str] = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = FUSION_START_RE.search(lines[i])
        if m:
            vc = m.group(1)
            start = _items(m.group(2))
            end, i = _find_end(lines, i)
            if not start:
                results[vc] = "none"
            elif not end:
                results[vc] = "acyclic_only"
            elif len(end) == len(start):
                results[vc] = "cyclic_only"
            else:
                results[vc] = "both"
        i += 1
    return results


# `benchPhase` (Flex/Tactic/Utils.lean, gated by `flex.benchPhases`) emits
# `[phase] <tac>:<phase>=<hb> ms=<ms>`, normally as a bare line (no
# `info:`/position prefix — same reason `FUSION_END_RE` is bare above), which
# belongs to whichever VC's tagged `info: .../XProof.lean:...:` line most
# recently preceded it. But a VC with NO κ-binders at all (`zap` throws
# "goal has no ∃-binders" before printing anything, caught by `try`) never
# emits a `[fusion] Start κ:` line — there, `benchSimpStar`'s own `[phase]`
# line is the first print in that VC's command and so IS itself tagged. So
# the anchor here is deliberately ANY tagged line for a `...Proof.lean` path,
# not specifically a `[fusion] Start` one — `INFO_TAG_RE`/`INFO_TAG_PATHED_RE`
# below, distinct from `FUSION_START_RE`/`FUSION_START_PATHED_RE` (which stay
# specific to kappa classification).
INFO_TAG_RE = re.compile(r"^info: .*/(\w+)Proof\.lean:\d+:\d+:")
INFO_TAG_PATHED_RE = re.compile(r"^info: (\S+)/User/Proof/(\w+)Proof\.lean:\d+:\d+:")

PHASE_RE = re.compile(r"\[phase\]\s+(\w+):(\w+)=(\d+)\s+ms=(\d+)")


def _add_phase(bucket: dict[str, dict[str, int]], m: re.Match) -> None:
    key = f"{m.group(1)}:{m.group(2)}"
    entry = bucket.setdefault(key, {"hb": 0, "ms": 0})
    entry["hb"] += int(m.group(3))
    entry["ms"] += int(m.group(4))


def parse_phases(text: str) -> dict[str, dict[str, dict[str, int]]]:
    """VC name -> {'tac:phase': {'hb': N, 'ms': N}}, keyed like `parse_log_kappa`.

    Carries the current VC key forward across bare lines: it's updated on
    every tagged `info: .../XProof.lean:...:` line, and every `[phase]` line
    up to the next tagged line (whether that line is itself a `[phase]` line
    or something else, e.g. `[fusion] Start κ:`) is folded into that VC's
    totals.
    """
    results: dict[str, dict[str, dict[str, int]]] = {}
    current: str | None = None
    for line in text.splitlines():
        m = INFO_TAG_RE.match(line)
        if m:
            current = m.group(1)
            results.setdefault(current, {})
        if current is None:
            continue
        pm = PHASE_RE.search(line)
        if pm:
            _add_phase(results[current], pm)
    return results


def parse_phases_pathed(text: str) -> dict[str, dict[str, dict[str, int]]]:
    """Like `parse_phases`, but keyed like `parse_log_kappa_pathed` — use for
    merged/multi-suite logs (e.g. lean_bench_merged)."""
    results: dict[str, dict[str, dict[str, int]]] = {}
    current: str | None = None
    for line in text.splitlines():
        m = INFO_TAG_PATHED_RE.match(line)
        if m:
            current = f"{m.group(1)}/{m.group(2)}"
            results.setdefault(current, {})
        if current is None:
            continue
        pm = PHASE_RE.search(line)
        if pm:
            _add_phase(results[current], pm)
    return results


def parse_log_kappa_pathed(text: str) -> dict[str, str]:
    """Like `parse_log_kappa`, but keys results by `<test_path>/<VCName>`
    (the directory prefix before `/User/Proof/`) instead of bare VC name.

    Use this for merged/multi-suite logs (e.g. lean_bench_merged) where the
    same VC basename appears under many different test directories — keying
    by bare name would silently conflate unrelated VCs' classifications.
    """
    results: dict[str, str] = {}
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = FUSION_START_PATHED_RE.search(lines[i])
        if m:
            key = f"{m.group(1)}/{m.group(2)}"
            start = _items(m.group(3))
            end, i = _find_end(lines, i)
            if not start:
                results[key] = "none"
            elif not end:
                results[key] = "acyclic_only"
            elif len(end) == len(start):
                results[key] = "cyclic_only"
            else:
                results[key] = "both"
        i += 1
    return results
