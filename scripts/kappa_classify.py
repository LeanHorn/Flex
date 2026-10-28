#!/usr/bin/env python3
"""Parse solve_fixpoint output and classify kappa variable usage.

With `flex.benchPhases` on, each call to solve_fixpoint prints a consecutive
pair of lines (with the option off it prints nothing, so pass
`-Dflex.benchPhases=true` to Lean):
  [solve_fixpoint] Elimination κ: [...]
  [solve_fixpoint] Cut κ: [...]

This module pairs them up so that files with multiple theorems produce one
classification per invocation rather than one per file.

Classifications:
  none         – both lists empty
  acyclic_only – elimination variables only
  cyclic_only  – cut variables only
  both         – elimination and cut variables present

Usage:
    python3 scripts/kappa_classify.py < output.txt
    python3 scripts/kappa_classify.py output.txt
    lake env lean -Dflex.benchPhases=true file.lean 2>&1 | python3 scripts/kappa_classify.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

# Matches either line so we can scan in document order.
EITHER_RE = re.compile(
    r"\[solve_fixpoint\] (Elimination|Cut|Acyclic|Cyclic) κ:\s*\[([^\]]*)\]"
)


def _items(raw: str) -> list[str]:
    return [k.strip() for k in raw.split(",") if k.strip()]


def parse_invocations(text: str) -> list[tuple[list[str], list[str]]]:
    """Return one (elim_vars, cut_vars) pair per solve_fixpoint call.

    Each Elimination line opens an invocation; the next Cut line closes it.
    Legacy labels are also accepted. Unmatched lines form partial invocations.
    """
    invocations: list[tuple[list[str], list[str]]] = []
    pending_elim: list[str] | None = None

    for m in EITHER_RE.finditer(text):
        kind, raw = m.group(1), m.group(2)
        if kind in {"Elimination", "Acyclic"}:
            if pending_elim is not None:
                # Previous elimination list had no matching cut list.
                invocations.append((pending_elim, []))
            pending_elim = _items(raw)
        else:  # Cut
            elim_vars = pending_elim if pending_elim is not None else []
            invocations.append((elim_vars, _items(raw)))
            pending_elim = None

    if pending_elim is not None:
        invocations.append((pending_elim, []))

    return invocations


def classify(elim_vars: list[str], cut_vars: list[str]) -> str:
    if elim_vars and cut_vars:
        return "both"
    if elim_vars:
        return "acyclic_only"
    if cut_vars:
        return "cyclic_only"
    return "none"


def main() -> None:
    if len(sys.argv) > 1:
        text = Path(sys.argv[1]).read_text()
    else:
        text = sys.stdin.read()

    invocations = parse_invocations(text)
    if not invocations:
        print("classification : none (no solve_fixpoint calls found)")
        return

    tally: dict[str, int] = {"none": 0, "acyclic_only": 0, "cyclic_only": 0, "both": 0}
    for i, (elim_vars, cut_vars) in enumerate(invocations):
        label = classify(elim_vars, cut_vars)
        tally[label] += 1
        print(f"invocation {i+1:>2} : {label}")
        print(f"  elimination kappas : {elim_vars or '[]'}")
        print(f"  cut kappas         : {cut_vars or '[]'}")

    if len(invocations) > 1:
        print("\ntally:")
        for label, n in tally.items():
            if n:
                print(f"  {label:<14} {n}")


if __name__ == "__main__":
    main()
