# Flex: supplementary material

```text
Flex/              Lean 4 library, tactics and evaluation harnesses
  evaluation/RQ*/  one folder per research question, each with a detailed README
  Demo/            the STLC and Imp verifiers and their examples
  vendor/          SMTLib-to-Lean (CHC to Lean translation), a local dependency
flex-benchmarks/   benchmark corpora (Flux, WaVe, Liquid Fixpoint, CHC-COMP)
```

Keep the two folders side by side. Unless stated otherwise, commands run from `Flex/`.

## Setup

Requirements: Linux or macOS, 16 GB RAM, [elan](https://github.com/leanprover/elan)
(installs Lean 4.34.0 from `lean-toolchain`), Python 3.10+, clang, Z3 4.15.4, and
Java with Eldarica 2.3 (RQ1–RQ3 only). On Ubuntu 24.04:

```sh
sudo apt-get install -y clang lld z3 libc++-dev libc++abi-dev default-jre-headless unzip
curl -fsSL https://github.com/uuverifiers/eldarica/releases/download/v2.3/eldarica-bin-2.3.zip -o eldarica.zip
unzip eldarica.zip -d "$HOME/eldarica" && export PATH="$HOME/eldarica/eldarica:$PATH"
# Link Flex's native code against the host C library:
printf '#!/bin/sh\nexec clang -fuse-ld=lld -L "$(lean --print-prefix)/lib" "$@"\n' > "$HOME/flex-clang"
chmod +x "$HOME/flex-clang" && export LEAN_CC="$HOME/flex-clang"
```

Build (20–40 minutes, mostly dependencies) and run a quick check:

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake build      # do not run `lake update`
lake lean Tests/SMT.lean -- --error=hasSorry
lake lean Demo/Imp.lean
(cd ../flex-benchmarks && python3 CHC-COMP/unpack.py)
```

## Reproducing the evaluation

Each RQ has a **smoke** command (a few queries, minutes) and a **full** command
(many hours). Each run writes a new output folder with per-query logs, CSVs and a
summary; see the RQ's README to resume an interrupted run. Timings depend on the
machine; coverage should match the paper up to queries that finish near the timeout.

**RQ1: case studies**

```sh
python3 scripts/benchmark_rq1.py --discharge --variants zap_fix_deep spacer eldarica \
  --cases cstr/GhostGPtrStrlen --output evaluation/results/RQ1/smoke
python3 scripts/benchmark_rq1.py --discharge --variants zap_fix_deep spacer eldarica \
  --jobs 2 --output evaluation/results/RQ1/full
python3 scripts/rq1_table.py evaluation/results/RQ1/full
```

**RQ2: Zap versus search-based tactics**

```sh
B=../flex-benchmarks
python3 -B evaluation/RQ2/benchmark_rq2.py --manifest $B/rq2/smoke/manifest.json \
  --count 0 --output evaluation/results/RQ2/smoke
for set in liquid-fixpoint flux_tests flux-medium wave flux-other; do
  python3 -B evaluation/RQ2/benchmark_rq2.py --manifest $B/rq2/$set/manifest.json \
    --count 0 --repeats 3 --output evaluation/results/RQ2/$set
done
python3 -B evaluation/RQ2/benchmark_rq2.py --corpus $B/CHC-COMP/generated \
  --count 0 --repeats 3 --output evaluation/results/RQ2/chc-comp
```

RQ3 and RQ4 run from `flex-benchmarks/`:

```sh
cd ../flex-benchmarks
R=../Flex/evaluation/results
```

**RQ3a: refinement-type CHCs**

```sh
ARMS="--configs zap_fix spacer_only eldarica_only --no-figures"
python3 -B ../Flex/evaluation/RQ3a/benchmark.py --benchmarks . $ARMS --count 4 --workers 1 --output $R/RQ3a/smoke
python3 -B ../Flex/evaluation/RQ3a/benchmark.py --benchmarks . $ARMS --count 0 --workers 4 --output $R/RQ3a/full
python3 -B ../Flex/evaluation/RQ3a/report.py --tables-only $R/RQ3a/full
```

**RQ3b: CHC-COMP**

```sh
ARMS="--configs zap_fix spacer_only eldarica_only"
python3 -B ../Flex/evaluation/RQ3b/benchmark.py --benchmarks . $ARMS --count 6 --workers 2 --output $R/RQ3b/smoke
python3 -B ../Flex/evaluation/RQ3b/benchmark.py --benchmarks . $ARMS --count 0 --workers 5 --output $R/RQ3b/full
python3 -B ../Flex/evaluation/RQ3b/report.py $R/RQ3b/full
```

**RQ4: qualifier scraping**

```sh
python3 -B ../Flex/evaluation/RQ4/benchmark.py --benchmarks . --smoke --output $R/RQ4/smoke
python3 -B ../Flex/evaluation/RQ4/benchmark.py --benchmarks . --workers 1 --output $R/RQ4/full
python3 -B ../Flex/evaluation/RQ4/report.py --results $R/RQ4/full
```
