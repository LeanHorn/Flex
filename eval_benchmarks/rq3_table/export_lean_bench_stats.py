#!/usr/bin/env python3
"""Parse the merged lean_bench build log and VC files; export per-VC stats as JSON.

Reads lean_bench_log.txt (produced by run_merged_suite.py) and the VC files
under <merged_dir>/**/<Cat>/<Test>/Flux/VC/*.lean.

Output (stdout): JSON array: [{"suite": "Flux lean-bench", "vcs": [...]}]

Each VC entry:
  {
    "name":    "<test_id>/<VCName>",
    "trivial": bool,          # body of last def is True
    "kappa":   "none"|"acyclic_only"|"cyclic_only"|"both",
    "failed":  bool,
  }
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

SCRIPT_DIR     = Path(__file__).resolve().parent
DEFAULT_MERGED = SCRIPT_DIR.parent / "lean_bench_merged"
DEFAULT_LOG    = SCRIPT_DIR / "lean_bench_log.txt"

DEF_RE = re.compile(r"^def \S+ :=\s*$|^def \S+ := (.+)", re.MULTILINE)

LEAN_LINE_RE = re.compile(
    r"^(?:info|error):\s+((\S+)/User/Proof/(\w+)Proof\.lean):\d+:\d+:\s+(.*)"
)
LAKE_FAIL_RE  = re.compile(r"^✖\s+\[\d+/\d+\]\s+Building\s+([\w.]+)")
# `fusion` (which runs before `solve_fixpoint`) reports the κ's it started
# with and the κ's still unsolved afterward — see Fusion.lean.
FUSION_END_BARE_RE = re.compile(r"^\[fusion\] End κ:\s*\[([^\]]*)\]")

# `benchPhase` (Flex/Tactic/Utils.lean, gated by `flex.benchPhases`) emits a
# bare `[phase] fusion:sol=...` line between `Start` and `End` whenever
# fusion has ≥1 acyclic κ to eliminate (the `sol` step runs, THEN `End`
# prints). A fixed 1-line lookahead for `End` right after `Start` breaks the
# moment `flex.benchPhases` is on — this VC would otherwise be misclassified
# as having no residual cyclic κ — so skip over any such phase lines first.
_BARE_PHASE_RE = re.compile(r"^\[phase\]\s+\w+:\w+=\d+(?:\s+ms=\d+)?$")


def is_trivially_true(path: Path) -> bool:
    text = path.read_text(encoding="utf-8", errors="replace")
    matches = list(DEF_RE.finditer(text))
    if not matches:
        return False
    last = matches[-1]
    if last.group(1) is not None:
        return last.group(1).strip() == "True"
    body = re.split(r"\bend\b", text[last.end():], maxsplit=1)[0].strip()
    return body == "True"


def classify(start: list[str] | None, end: list[str] | None) -> str:
    """Classify a VC from fusion's Start/End κ lists.

      - no κ's to start with         -> none
      - something before, none after -> acyclic_only
      - same count before and after  -> cyclic_only (fusion ate nothing)
      - fewer after than before      -> both
    """
    if not start:
        return "none"
    if not end:
        return "acyclic_only"
    if len(end) == len(start):
        return "cyclic_only"
    return "both"


def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


def load_timing(log_dir: Path) -> dict:
    result = {}
    for key, fname in [("time_ms", "lean_bench.time"),
                       ("flux_time_ms", "flux_bench.time")]:
        try:
            result[key] = int((log_dir / fname).read_text().strip())
        except Exception:
            pass
    return result


def _vc_key(test_path: str, vc_name: str) -> str:
    """Unique key: '<cat>/<test>/<VCName>' (e.g. 'Vec/Vec00/TestIsEmpty')."""
    return f"{test_path}/{vc_name}"


def parse_merged_log(log_path: Path) -> dict[str, dict]:
    """
    Parse the raw `lake build` log from the merged project.

    Returns dict keyed by '<cat>/<test>/<VCName>':
      {"failed": bool, "start": [...], "end": [...]}
    """
    vcs: dict[str, dict] = {}

    def _get(key: str) -> dict:
        if key not in vcs:
            vcs[key] = {"failed": False, "start": None, "end": None}
        return vcs[key]

    all_lines = log_path.read_text(encoding="utf-8", errors="replace").splitlines()
    i = 0
    while i < len(all_lines):
        line = all_lines[i]

        # Lake-level failure marker.
        lf = LAKE_FAIL_RE.match(line)
        if lf:
            module = lf.group(1)
            # e.g. Vec.Vec00.User.Proof.TestIsEmptyProof
            parts = module.split(".")
            try:
                proof_idx = next(j for j, p in enumerate(parts) if p == "Proof")
                vc_name = parts[proof_idx + 1]
                if vc_name.endswith("Proof"):
                    vc_name = vc_name[:-5]
                test_path = "/".join(parts[:proof_idx - 1])  # skip "User"
                _get(_vc_key(test_path, vc_name))["failed"] = True
            except (StopIteration, IndexError):
                pass
            i += 1
            continue

        # Lean info/error line referencing a Proof file.
        lm = LEAN_LINE_RE.match(line)
        if not lm:
            i += 1
            continue
        level_char = line.split(":", 1)[0]
        # group(1)=full fpath, group(2)=cat/test path, group(3)=VCName, group(4)=message
        test_path, vc_name, message = lm.group(2), lm.group(3), lm.group(4)
        key = _vc_key(test_path, vc_name)

        if level_char == "error":
            _get(key)["failed"] = True
            i += 1
            continue

        if "[fusion] Start" in message:
            raw = re.search(r"κ:\s*\[([^\]]*)\]", message)
            start = _items(raw.group(1)) if raw else []
            # End line follows, without an info: prefix, possibly after one
            # or more bare `[phase]` lines (see `_BARE_PHASE_RE`).
            end: list[str] = []
            j = i + 1
            while j < len(all_lines) and _BARE_PHASE_RE.match(all_lines[j]):
                j += 1
            if j < len(all_lines):
                em = FUSION_END_BARE_RE.match(all_lines[j])
                if em:
                    end = _items(em.group(1))
                    i = j
            _get(key)["start"] = start
            _get(key)["end"] = end

        i += 1

    return vcs


def run_merged(merged_dir: Path, log_path: Path) -> list[dict]:
    vc_info = parse_merged_log(log_path)

    vcs: list[dict] = []
    # VC files in merged project: <merged>/<Cat>/<Test>/Flux/VC/<Name>.lean
    for vc_path in sorted(merged_dir.rglob("Flux/VC/*.lean")):
        vc_name = vc_path.stem
        trivial = is_trivially_true(vc_path)

        # Derive test_id from path, e.g.:
        # .../AbstractRefinements/Test00/Flux/VC/Max.lean -> AbstractRefinements/Test00
        try:
            rel_parts = vc_path.relative_to(merged_dir).parts
            flux_idx = rel_parts.index("Flux")
            test_id = "/".join(rel_parts[:flux_idx])
        except (ValueError, IndexError):
            test_id = str(vc_path.parent.parent.parent)

        key = _vc_key(test_id, vc_name)
        info = vc_info.get(key, {})

        vcs.append({
            "name":    f"{test_id}/{vc_name}",
            "trivial": trivial,
            "kappa":   classify(info.get("start"), info.get("end")),
            "failed":  info.get("failed", False),
        })
    return vcs


def main() -> None:
    merged_dir = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else DEFAULT_MERGED
    log_path = DEFAULT_LOG

    if not log_path.exists():
        print(f"error: log not found: {log_path}", file=sys.stderr)
        sys.exit(1)
    if not merged_dir.is_dir():
        print(f"error: merged dir not found: {merged_dir}", file=sys.stderr)
        sys.exit(1)

    vcs = run_merged(merged_dir, log_path)

    suite: dict = {"suite": "Flux lean-bench", "vcs": vcs}
    suite.update(load_timing(log_path.parent))

    print(json.dumps([suite], indent=2))


if __name__ == "__main__":
    main()
