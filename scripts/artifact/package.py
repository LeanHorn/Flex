#!/usr/bin/env python3
"""Build the anonymous submission archive from Flex and flex-benchmarks.

    python3 scripts/artifact/package.py [--benchmarks ../flex-benchmarks] [--out ../flex-artifact]

Exports the committed HEAD of both repositories (no git history, no local results),
vendors SMTLib-to-Lean, turns every remote Flex dependency into a local path dependency,
removes identifying paths and URLs, then refuses to zip if any identifying string remains.
Output: OUT/artifact/{README.md, Flex/, flex-benchmarks/} and OUT/artifact.zip.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

# Removed from the Flex export: this packaging folder and internal notes.
FLEX_EXCLUDE = ["scripts/artifact", "evaluation/CLEANUP.txt"]
SMT2LEAN_EXCLUDE = ["benchmarks"]
SMT2LEAN_DIR = "vendor/SMTLib-to-Lean"

# Strings that must not appear anywhere in the archive (case-insensitive).
DENY = re.compile(r"leanhorn|jam-khan|jamkhan|jamkabeer|kabeer|petros|markopoulos|lehmann|"
                  r"hku\.hk|uchile|/home/[a-z]|/Users/[a-z]", re.I)
# Upstream third-party test files that carry their original author's build paths verbatim.
ALLOW = [re.compile(r"/Users/(rjhala|benjamin)/")]

TEXT_SUFFIXES = {".lean", ".md", ".txt", ".py", ".sh", ".json", ".toml", ".yml", ".yaml",
                 ".csv", ".fq", ".smt2", ".hs", ".rs", ".cpp", ".h", ".jsonl", ""}


def run(*command, **kwargs):
    return subprocess.run(command, check=True, **kwargs)


def export(repo: Path, rev: str, target: Path, exclude=()):
    target.mkdir(parents=True)
    archive = subprocess.run(["git", "-C", str(repo), "archive", "--format=tar", rev],
                             check=True, capture_output=True).stdout
    with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
        tar.extractall(target, filter="tar")
    for path in exclude:
        victim = target / path
        if victim.is_dir():
            shutil.rmtree(victim)
        elif victim.exists():
            victim.unlink()


def warn_if_dirty(repo: Path):
    status = subprocess.run(["git", "-C", str(repo), "status", "--porcelain", "--untracked-files=no"],
                            check=True, capture_output=True, text=True).stdout
    if status.strip():
        print(f"warning: {repo} has uncommitted changes; packaging HEAD only", file=sys.stderr)


def edit(path: Path, *pairs, count_check=True):
    text = path.read_text()
    for old, new in pairs:
        if count_check and old not in text:
            raise SystemExit(f"{path}: expected text not found: {old[:80]!r}")
        text = text.replace(old, new)
    path.write_text(text)


def vendor_smt2lean(flex: Path):
    manifest_path = flex / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    entry = next(p for p in manifest["packages"] if p["name"] == "smt2lean")
    source = ROOT / ".lake/packages/smt2lean"
    if not (source / ".git").exists():
        raise SystemExit(f"{source} missing: run `lake build` in Flex first")
    export(source, entry["rev"], flex / SMT2LEAN_DIR, SMT2LEAN_EXCLUDE)
    # Path dependency in both the Lake configuration and the manifest.
    lakefile = flex / "lakefile.lean"
    text = lakefile.read_text()
    text, n = re.subn(r'require smt2lean from git\s*\n\s*"[^"]+"\s*@\s*"[0-9a-f]+"',
                      f'require smt2lean from "vendor" / "SMTLib-to-Lean"', text)
    if n != 1:
        raise SystemExit("lakefile.lean: smt2lean requirement not found")
    lakefile.write_text(text)
    index = manifest["packages"].index(entry)
    manifest["packages"][index] = {
        "type": "path", "scope": entry.get("scope", ""), "name": "smt2lean",
        "manifestFile": "lake-manifest.json", "inherited": False,
        "dir": f"./{SMT2LEAN_DIR}", "configFile": entry.get("configFile", "lakefile.toml")}
    manifest_path.write_text(json.dumps(manifest, indent=1, ensure_ascii=False) + "\n")


def anonymize_flex_text(flex: Path):
    edit(flex / "README.md", ('git = "https://github.com/LeanHorn/Flex"\nrev = "main"',
                              'path = "../Flex"  # this folder'))
    readme = flex / "evaluation/RQ1/README.md"
    text = readme.read_text()
    # The opening paragraph points at an internal PR and local result folders.
    text = re.sub(r"The latest proof refresh is .*?\n\n", "", text, count=1, flags=re.S)
    readme.write_text(text)
    edit(flex / "evaluation/RQ3a/README.md",
         ("git clone https://github.com/LeanHorn/Flex.git\n"
          "git clone https://github.com/LeanHorn/flex-benchmarks.git\n",
          "# The artifact already contains Flex/ and flex-benchmarks/ side by side.\n"))
    edit(flex / SMT2LEAN_DIR / "README.md",
         ("git clone https://github.com/LeanHorn/SMTLib-to-Lean.git",
          "# vendored in Flex/vendor/SMTLib-to-Lean"))


def flex_path_dependencies(bench: Path, flex: Path):
    """Every suite requires Flex from GitHub; point it at the sibling Flex folder instead."""
    for lakefile in sorted(bench.rglob("lakefile.toml")):
        text = lakefile.read_text()
        relative = os.path.relpath(flex, lakefile.parent)
        text, n = re.subn(r'(\[\[require\]\]\s*\nname = "[Ff]lex"\s*\n)git = "[^"]*"\s*\nrev = "[^"]*"',
                          lambda m: f'{m.group(1)}path = "{relative}"', text)
        if n:
            lakefile.write_text(text)
            # The old manifest pins a remote Flex revision; Lake regenerates it from the path.
            (lakefile.parent / "lake-manifest.json").unlink(missing_ok=True)
        elif re.search(r'name = "[Ff]lex"', text):
            raise SystemExit(f"{lakefile}: unrecognized Flex requirement")


def scrub_bytes(data: bytes) -> bytes:
    # Translator source comments: absolute path of the generating machine → corpus-relative.
    return re.sub(rb'"/Users/[^"]*?/CHC-COMP/', b'"CHC-COMP/', data)


def rebuild_chc_archive(bench: Path):
    """Scrub source comments in the Lean archive; update the hashes that cover them."""
    corpus = bench / "CHC-COMP"
    path = corpus / "archives/lean4.tar.gz"
    with tarfile.open(path, "r:gz") as tar:
        members = [(m, tar.extractfile(m).read()) for m in tar.getmembers()]
    files = {m.name: scrub_bytes(data) for m, data in members}
    for name in [n for n in files if n.endswith("-manifest.json")]:
        report = json.loads(files[name])
        for entry in report["files"]:
            lean = f"generated/{report['project']}/{Path(entry['input']).with_suffix('.lean')}"
            entry["output_sha256"] = hashlib.sha256(files[lean]).hexdigest()
        files[name] = (json.dumps(report, indent=2, ensure_ascii=False) + "\n").encode()
    buffer = io.BytesIO()
    with gzip.GzipFile(fileobj=buffer, mode="wb", mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode="w", format=tarfile.PAX_FORMAT) as tar:
            for member, _ in members:
                data = files[member.name]
                info = tarfile.TarInfo(member.name)
                info.size, info.mode, info.mtime = len(data), member.mode, member.mtime
                tar.addfile(info, io.BytesIO(data))
    path.write_bytes(buffer.getvalue())
    manifest_path = corpus / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    for entry in manifest["archives"]:
        if entry["path"] == "archives/lean4.tar.gz":
            entry["bytes"] = path.stat().st_size
            entry["sha256"] = hashlib.sha256(path.read_bytes()).hexdigest()
    manifest_path.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")


def refresh_sums(bench: Path):
    """Rehash every file listed in CHC-COMP/SHA256SUMS after the edits above."""
    corpus = bench / "CHC-COMP"
    sums = corpus / "SHA256SUMS"
    lines = []
    for line in sums.read_text().splitlines():
        _, name = line.split("  ", 1)
        lines.append(f"{hashlib.sha256((corpus / name).read_bytes()).hexdigest()}  {name}")
    sums.write_text("\n".join(lines) + "\n")


def anonymize_bench_text(bench: Path):
    for path in [bench / "CHC-COMP/provenance.json", *bench.rglob("README.md")]:
        if path.exists():
            text = path.read_text()
            text = re.sub(r"https://github\.com/LeanHorn/SMTLib-to-Lean(\.git)?",
                          "Flex/vendor/SMTLib-to-Lean", text)
            text = text.replace("[Flex's instructions](https://github.com/LeanHorn/Flex#readme)",
                                "Flex's instructions (`Flex/README.md`)")
            path.write_text(text)


def anonymize_remaining_urls(root: Path):
    """Any other repository URL of ours (e.g. provenance in recorded metadata)."""
    pattern = re.compile(r"https://github\.com/LeanHorn/([\w.-]+?)(\.git)?\b")
    for path in root.rglob("*"):
        if path.is_file() and path.suffix in TEXT_SUFFIXES and not path.name.endswith(".gz"):
            try:
                text = path.read_text()
            except UnicodeDecodeError:
                continue
            new = pattern.sub(lambda m: f"anonymous/{m.group(1)}", text)
            if new != text:
                path.write_text(new)


def scan(root: Path) -> list[str]:
    hits = []

    def check(label, data: bytes):
        for line in data.decode("utf-8", "replace").splitlines():
            if DENY.search(line) and not any(a.search(line) for a in ALLOW):
                hits.append(f"{label}: {line.strip()[:160]}")
                return

    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        label = str(path.relative_to(root))
        if DENY.search(label):
            hits.append(f"{label}: identifying file name")
        if path.name.endswith((".tar.gz", ".tgz")):
            with tarfile.open(path, "r:gz") as tar:
                for member in tar.getmembers():
                    if member.isfile():
                        check(f"{label}!{member.name}", tar.extractfile(member).read())
        else:
            check(label, path.read_bytes())
    return hits


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--benchmarks", type=Path, default=ROOT.parent / "flex-benchmarks")
    parser.add_argument("--out", type=Path, default=ROOT.parent / "flex-artifact")
    args = parser.parse_args()
    stage = args.out / "artifact"
    if stage.exists():
        shutil.rmtree(stage)
    flex, bench = stage / "Flex", stage / "flex-benchmarks"
    for repo in (ROOT, args.benchmarks):
        warn_if_dirty(repo)
    print("exporting Flex and flex-benchmarks (HEAD) ...")
    export(ROOT, "HEAD", flex, FLEX_EXCLUDE)
    export(args.benchmarks.resolve(), "HEAD", bench)
    print("vendoring SMTLib-to-Lean ...")
    vendor_smt2lean(flex)
    anonymize_flex_text(flex)
    print("rewriting benchmark dependencies and corpus archive ...")
    flex_path_dependencies(bench, flex)
    rebuild_chc_archive(bench)
    anonymize_bench_text(bench)
    anonymize_remaining_urls(stage)
    refresh_sums(bench)
    shutil.copy2(HERE / "README.md", stage / "README.md")
    print("scanning for identifying strings ...")
    hits = scan(stage)
    if hits:
        print(f"{len(hits)} identifying strings remain; not zipping:", file=sys.stderr)
        for hit in hits[:50]:
            print("  " + hit, file=sys.stderr)
        sys.exit(1)
    archive = args.out / "artifact.zip"
    archive.unlink(missing_ok=True)
    run("zip", "-qrX", str(archive), "artifact", cwd=args.out)
    print(f"wrote {archive} ({archive.stat().st_size / 1e6:.1f} MB)")


if __name__ == "__main__":
    main()
