"""flat.py VC.lean ROOT OUT [extra-set-option ...]: inline local imports and append a probe."""
import os, re, sys
vc, root, out = sys.argv[1:4]; extra = sys.argv[4:]
M = "/Users/petros/Documents/UCSD/Work/lean-fixpoint/.lake/packages/mathlib/"
seen, ext, body = set(), [], []
def mod_path(m):
    p = os.path.join(root, *m.split(".")) + ".lean"
    return p if os.path.exists(p) else None
def visit(path):
    if path in seen: return
    seen.add(path)
    text = open(path).read()
    rest = []
    for line in text.split("\n"):
        m = re.match(r"^import\s+(\S+)", line)
        if m:
            local = mod_path(m.group(1))
            if local: visit(local)
            elif m.group(1) not in ext: ext.append(m.group(1))
        else: rest.append(line)
    body.append("\n".join(rest))
visit(vc)
ext = [e if os.path.exists(M + e.replace(".", "/") + ".lean") or not e.startswith("Mathlib") else "Mathlib.Data.Real.Basic" for e in ext]
src = open(vc).read()
ns = re.findall(r"^namespace (\S+)", src, re.M)
d = re.findall(r"^def (\S+)", src, re.M)[-1]
name = ".".join(ns + [d]) if ns else d
probe = open(os.path.join(os.path.dirname(__file__), "probe.lean")).read()
hdr = "\n".join(f"import {e}" for e in dict.fromkeys(ext + ["Flex"]))
opts = "\n".join(f"set_option {o}" for o in extra)
open(out, "w").write(f"{hdr}\n" + "\n".join(body) + f"\n{probe}\n{opts}\nexample : {name} := by\n  unfold {name}\n  intros\n  probe\n")
