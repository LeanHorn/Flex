"""compare.py BASE NEW: per-VC outcome comparison of two run.sh output directories."""
import collections, glob, os, re, sys

def classify(path):
    text = open(path, errors="ignore").read()
    m = re.search(r"PROBE outcome=<(.*?)>\s*$", text, re.M | re.S) or re.search(r"PROBE outcome=<([^\n]*)", text)
    if not m and not text.strip():
        return "running", "no output yet"
    if not m:
        return "crash", (re.search(r"error: .*", text) or re.search(r".+", text) or ["no output"])[0][:160]
    o = m.group(1)
    if o == "solved" or (o.startswith("partial") and o.endswith("grind-left=0")): return "closed", o
    if o.startswith("partial"): return "residual", o
    stage = re.match(r"failed\[Flex\.CHC\.Stage\.(\w+)\]", o)
    return (stage.group(1) if stage else "failed"), o

def load(d):
    return {os.path.basename(f): classify(f) for f in glob.glob(os.path.join(d, "*.lean.log"))}

def bucket(o):
    o = re.sub(r"clause \d+: ", "", o)
    o = re.sub(r"'[^']*'", "'_'", o)
    o = re.sub(r"\|[^|]*\|", "|_|", o)
    return o[:140]

base, new = load(sys.argv[1]), load(sys.argv[2])
keys = sorted(k for k in set(base) & set(new) if "running" not in (base[k][0], new[k][0]))
print(f"{len(keys)} VCs in both ({len(base)} base, {len(new)} new)\n")
cats = sorted({c for k in keys for c in (base[k][0], new[k][0])})
print(f"  {'':10} {'base':>5} {'new':>5}")
for c in cats:
    print(f"  {c:10} {sum(base[k][0] == c for k in keys):5} {sum(new[k][0] == c for k in keys):5}")
lost = [k for k in keys if base[k][0] == "closed" and new[k][0] != "closed"]
won = [k for k in keys if base[k][0] != "closed" and new[k][0] == "closed"]
print(f"\nREGRESSIONS ({len(lost)}):")
for k in lost: print(f"  {k[:80]}\n      {new[k][1][:160]}")
print(f"\nNEWLY CLOSED ({len(won)}):")
for k in won: print(f"  {k[:80]}  (was {base[k][0]})")
print("\nOPEN IN NEW, BY MESSAGE:")
for msg, n in collections.Counter(bucket(new[k][1]) for k in keys if new[k][0] != "closed").most_common(30):
    print(f"  {n:4} {msg}")
