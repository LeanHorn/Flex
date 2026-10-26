"""Select RQ1 predicate goals and freeze only their specification dependencies.

The graph classification parses the generated source grammar; the Lean harness
independently measures predicate elimination. No user proof module is imported.
"""

from __future__ import annotations

from collections import Counter
import hashlib
from pathlib import Path
import re


SUITES = ("cstr", "flux_to_lean_demo", "hashtable", "pattern", "vec_deque", "tock_theorems")
PREDICATE = re.compile(r"\bk\d+\b")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(source: str) -> str:
    """Preserve strings and newlines while removing nested Lean comments."""
    out: list[str] = []
    i, depth = 0, 0
    in_string = False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            out.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                out.append(source[i + 1])
                i += 2
            else:
                if source[i] == '"':
                    in_string = False
                i += 1
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i])
            in_string = source[i] == '"'
            i += 1
    if depth or in_string:
        raise ValueError("unterminated comment or string")
    return "".join(out)


def _outer(expression: str) -> str:
    expression = expression.strip()
    while expression.startswith("(") and expression.endswith(")"):
        depth = 0
        for i, char in enumerate(expression):
            depth += (char == "(") - (char == ")")
            if depth == 0:
                break
        if i != len(expression) - 1:
            break
        expression = expression[1:-1].strip()
    return expression


def _split(expression: str, operators: tuple[str, ...]) -> tuple[str, str] | None:
    depth = 0
    for i, char in enumerate(expression):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif depth == 0:
            for operator in operators:
                if expression.startswith(operator, i):
                    return expression[:i], expression[i + len(operator):]
    return None


def classify(source: str, name: str) -> dict:
    clean = strip_comments(source)
    match = re.search(r"^def\s+" + re.escape(name) + r"\s*:=", clean, re.M)
    if not match:
        raise ValueError(f"missing generated definition {name}")
    body = re.split(r"^end\b", clean[match.end():], maxsplit=1, flags=re.M)[0]
    predicates = re.findall(r"∃\s+(k\d+)\s*:", body)
    if len(predicates) != len(set(predicates)):
        raise ValueError(f"duplicate predicate binders in {name}")
    names = set(predicates)
    edges: dict[str, set[str]] = {k: set() for k in predicates}
    heads: set[str] = set()
    pending = [(body, frozenset())]
    while pending:
        expression, guards = pending.pop()
        expression = _outer(expression)
        if expression.startswith(("∀", "∃")):
            split = _split(expression, (",",))
            if split is None:
                raise ValueError(f"unrecognized quantifier in {name}: {expression[:80]}")
            pending.append((split[1], guards))
        elif split := _split(expression, ("->", "→")):
            premise, conclusion = split
            pending.append((conclusion, guards | (set(PREDICATE.findall(premise)) & names)))
        elif split := _split(expression, ("∧", "/\\", "∨", "\\/")):
            pending.extend((part, guards) for part in split)
        elif head := re.match(r"^(k\d+)\b", expression):
            name_ = head.group(1)
            if name_ in names:
                heads.add(name_)
                for guard in guards:
                    edges[guard].add(name_)
        elif set(PREDICATE.findall(expression)) & names:
            raise ValueError(f"unsupported predicate occurrence in {name}: {expression[:100]}")
    if names != heads:
        raise ValueError(f"predicates without parsed heads in {name}: {sorted(names - heads)}")

    cyclic = set()
    for start in predicates:
        seen, todo = set(), list(edges[start])
        while todo:
            current = todo.pop()
            if current == start:
                cyclic.add(start)
                break
            if current not in seen:
                seen.add(current)
                todo.extend(edges[current])
    acyclic = names - cyclic
    classification = ("mixed" if cyclic and acyclic else "cyclic_only" if cyclic
                      else "acyclic_only" if names else "none")
    return {"predicates": predicates,
            "cyclic_predicates": [k for k in predicates if k in cyclic],
            "acyclic_predicates": [k for k in predicates if k in acyclic],
            "dependency_edges": [[k, v] for k in predicates for v in sorted(edges[k])],
            "classification": classification, "selected": bool(predicates)}


def inventory(root: Path) -> list[dict]:
    rows = []
    for suite in SUITES:
        directory = root / suite / "LeanProofs/Flux/VC"
        if not directory.is_dir():
            raise FileNotFoundError(directory)
        for path in sorted(directory.glob("*.lean")):
            rows.append({"id": f"{suite}/{path.stem}", "suite": suite, "name": path.stem,
                         "module": f"LeanProofs.Flux.VC.{path.stem}",
                         "declaration": f"F.{path.stem}",
                         "source": str(path.relative_to(root)), "sha256": digest(path),
                         **classify(path.read_text(), path.stem)})
    return rows


def imports(source: str) -> list[str]:
    result = []
    for line in strip_comments(source).splitlines():
        if match := re.match(r"^\s*import\s+(.+?)\s*$", line):
            result.extend(match.group(1).split())
    return list(dict.fromkeys(result))


def check_specification(module: str, source: str) -> None:
    allowed = (module == "LeanProofs.Flux.Prelude" or module == "LeanProofs.Lib.Lemmas"
               or module.startswith(("LeanProofs.Flux.VC.", "LeanProofs.Flux.Fun.",
                                     "LeanProofs.Flux.Struct.", "LeanProofs.User.Fun.",
                                     "LeanProofs.User.Struct.")))
    if not allowed:
        raise ValueError(f"not a specification dependency: {module}")
    clean = strip_comments(source)
    if re.search(r"\b(sorry|admit|axiom|native_decide|qualif)\b", clean):
        raise ValueError(f"untrusted evidence or qualifier registration in {module}")


def collect_dependencies(suite_root: Path, module: str) -> list[Path]:
    """Return local specification files in dependency order, including the VC."""
    ordered: list[Path] = []
    active: set[str] = set()
    seen: set[str] = set()

    def visit(current: str) -> None:
        if current in active:
            raise ValueError(f"cyclic module import: {current}")
        if current in seen:
            return
        if not current.startswith("LeanProofs."):
            if current not in ("Init", "Lean", "Std", "Aesop", "Flex"):
                raise ValueError(f"unexpected external specification import: {current}")
            return
        path = suite_root / (current.replace(".", "/") + ".lean")
        source = path.read_text()
        check_specification(current, source)
        active.add(current)
        for dependency in imports(source):
            visit(dependency)
        active.remove(current)
        seen.add(current)
        ordered.append(path)

    visit(module)
    return ordered


def snapshot_suite(source_root: Path, suite: str, selected_cases: list[dict],
                   workspace: Path) -> dict:
    suite_root = source_root / suite
    modules: dict[str, dict] = {}
    for case in selected_cases:
        if case["suite"] != suite or not case["selected"]:
            raise ValueError("snapshot cases must be selected members of this suite")
        if digest(source_root / case["source"]) != case["sha256"]:
            raise ValueError(f"case changed since inventory: {case['id']}")
        for path in collect_dependencies(suite_root, case["module"]):
            relative = path.relative_to(suite_root)
            module = str(relative.with_suffix("")).replace("/", ".")
            if module in modules:
                continue
            destination = workspace / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            data = path.read_bytes()
            if destination.exists() and destination.read_bytes() != data:
                raise ValueError(f"snapshot would replace changed source: {destination}")
            destination.write_bytes(data)
            modules[module] = {"module": module, "path": str(relative),
                               "sha256": hashlib.sha256(data).hexdigest()}
    return {"suite": suite, "cases": [case["id"] for case in selected_cases],
            "modules": list(modules.values())}


def summarize(rows: list[dict]) -> dict:
    return {"total": len(rows), "selected": sum(row["selected"] for row in rows),
            "classes": dict(Counter(row["classification"] for row in rows)),
            "suites": {suite: dict(Counter(row["classification"] for row in rows
                                           if row["suite"] == suite)) for suite in SUITES}}
