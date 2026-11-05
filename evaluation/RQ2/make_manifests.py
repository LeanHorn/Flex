#!/usr/bin/env python3
"""Build RQ2 statement manifests from Flux projects and the LiquidHaskell corpus.

The runner compiles each case against this checkout's Lean environment, so a
statement file may import only Flex and its dependencies. Each VC is therefore
flattened: its project-local imports are inlined in dependency order. Inputs are
never modified; the flattened copies record their source module and hash.

Uninterpreted functions emitted as `def f : T := sorry` become `opaque f : T`
in the copies. Both leave `f` unconstrained, but the former makes every
certificate mentioning `f` depend on `sorryAx`, which the harness rejects.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re

IMPORT = re.compile(r"^import\s+(\S+)\s*$", re.M)
SORRY_DEF = re.compile(r"^(?:noncomputable\s+)?def\s+(\S+)\s*:\s*(.+?)\s*:=\s*sorry\s*$", re.M)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module_path(root: Path, module: str) -> Path:
    return root.joinpath(*module.replace("«", "").replace("»", "").split(".")).with_suffix(".lean")


def flatten(root: Path, target: str) -> tuple[str, list[str], list[str], list[str]]:
    """Inline project-local imports of `target`; return text, externals, modules, rewrites."""
    order, external, visiting, done = [], [], set(), set()

    def visit(module):
        if module in done:
            return
        if module in visiting:
            raise ValueError(f"import cycle at {module}")
        visiting.add(module)
        for dependency in IMPORT.findall(module_path(root, module).read_text()):
            if module_path(root, dependency).is_file():
                visit(dependency)
            elif dependency not in external:
                external.append(dependency)
        visiting.discard(module)
        done.add(module)
        order.append(module)

    visit(target)
    rewrites, parts = [], []
    for module in order:
        body = IMPORT.sub("", module_path(root, module).read_text())

        def opaque(match):
            rewrites.append(f"{module}:{match[1]}")
            return f"opaque {match[1]} : {match[2]}"

        parts.append(f"-- ===== {module} =====\n{SORRY_DEF.sub(opaque, body).strip()}\n")
    text = "".join(f"import {m}\n" for m in external) + "\n" + "\n".join(parts)
    return text, external, order, rewrites


def flux(args):
    cases = []
    for project in args.project:
        root = project.resolve()
        for vc in sorted(root.rglob("Flux/VC/*.lean")):
            if ".lake" in vc.parts:
                continue
            relative = vc.relative_to(root).with_suffix("")
            module = ".".join(relative.parts)
            source = vc.read_text()
            namespaces = re.findall(r"^namespace\s+(\S+)", source, re.M)
            names = re.findall(r"^def\s+(\S+)", source, re.M)
            if len(names) != 1 or len(namespaces) != 1:
                raise ValueError(f"{vc}: expected one namespace and one def")
            text, external, modules, rewrites = flatten(root, module)
            unknown = [m for m in external if m.split(".")[0] not in args.allowed_roots]
            if unknown:
                raise ValueError(f"{vc}: unresolved imports {unknown}")
            # Drop the `Flux/VC` segment: `wave/FdmapImpl__0__Create`, `flux_tests/Array/Test01`.
            stem = [p for p in relative.parts if p not in ("LeanProofs", "Flux", "VC")]
            case = "/".join([root.name, *stem])
            output = args.output / "statements" / f"{case}.lean"
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(f"-- RQ2 statement: {root.name}:{module} (flattened, no proof)\n{text}")
            cases.append({"case": case, "suite": root.name, "format": "lean_statement",
                          "generated": str(output.relative_to(args.output)),
                          "declaration": f"{namespaces[0]}.{names[0]}",
                          "vc_file": str(vc), "vc_sha256": digest(vc),
                          "inlined_modules": modules, "opaque_rewrites": rewrites})
    return cases, {"projects": [str(p.resolve()) for p in args.project]}


def liquidhaskell(args):
    corpus = args.corpus.resolve()
    data = json.loads((corpus / "manifest.json").read_text())
    helper = (corpus / data["import_helper"]).resolve()
    helper_text = helper.read_text()
    helper_imports = IMPORT.findall(helper_text)
    helper_body = IMPORT.sub("", helper_text).strip()
    cases = []
    for entry in data["cases"]:
        source = corpus / entry["lean"]
        text = source.read_text()
        imports = [m for m in IMPORT.findall(text) if m != "FixpointImport"]
        if "FixpointImport" not in IMPORT.findall(text):
            raise ValueError(f"{source}: expected `import FixpointImport`")
        body = IMPORT.sub("", text).strip()
        case = "liquid-haskell/" + entry["case"].removesuffix(".hs")
        output = args.output / "statements" / f"{case}.lean"
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(f"-- RQ2 statement: {entry['lean']} with FixpointImport inlined\n"
                          + "".join(f"import {m}\n" for m in dict.fromkeys(helper_imports + imports))
                          + f"\n-- ===== FixpointImport =====\n{helper_body}\n\n-- ===== {entry['case']} =====\n{body}\n")
        cases.append({"case": case, "suite": "liquid-haskell", "format": "lean_statement",
                      "generated": str(output.relative_to(args.output)), "declaration": "FixpointGoal",
                      "lean_file": str(source), "lean_sha256": digest(source),
                      "selection_outcome": entry.get("selection_outcome")})
    return cases, {"corpus": str(corpus), "helper": str(helper), "helper_sha256": digest(helper)}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="kind", required=True)
    f = sub.add_parser("flux", help="flatten every Flux/VC/*.lean under the given projects")
    f.add_argument("project", type=Path, nargs="+")
    f.add_argument("--allowed-roots", nargs="+", default=["Flex", "Lean", "Init", "Std", "Mathlib"])
    lh = sub.add_parser("liquidhaskell", help="inline FixpointImport into the LiquidHaskell corpus")
    lh.add_argument("corpus", type=Path)
    for p in (f, lh):
        p.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output = args.output.resolve()
    if args.output.exists() and any(args.output.iterdir()):
        parser.error("output must be empty")
    args.output.mkdir(parents=True, exist_ok=True)
    cases, provenance = (flux if args.kind == "flux" else liquidhaskell)(args)
    ids = [c["case"] for c in cases]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate case IDs")
    manifest = args.output / "manifest.json"
    manifest.write_text(json.dumps({"kind": args.kind, **provenance, "count": len(cases),
                                    "cases": cases}, indent=2, ensure_ascii=False) + "\n")
    rewritten = sum(bool(c.get("opaque_rewrites")) for c in cases)
    print(f"{manifest}: {len(cases)} cases" + (f", {rewritten} with opaque rewrites" if rewritten else ""))


if __name__ == "__main__":
    main()
