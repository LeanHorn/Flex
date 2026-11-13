# Flex: supplementary material

This archive contains the tool and the benchmarks used in the evaluation:

```text
Flex/              the Lean 4 library, tactics and evaluation harnesses
  vendor/          SMTLib-to-Lean (SMT-LIB/CHC to Lean translation), a local dependency
  evaluation/      one folder per research question, each with a detailed README
flex-benchmarks/   benchmark corpora (Flux, WaVe, Liquid Fixpoint, CHC-COMP, ...)
```

Keep the two folders side by side: the harnesses find the benchmarks at `../flex-benchmarks`,
and the benchmark projects depend on Flex through the relative path `../Flex`.

## 1. Requirements

- Linux (tested on Ubuntu 24.04, x86-64) or macOS; 16 GB RAM or more.
- [elan](https://github.com/leanprover/elan). The pinned toolchain (Lean 4.34.0) is installed
  automatically from `Flex/lean-toolchain`.
- Python 3.10 or newer (standard library only; `matplotlib` optional for figures,
  and `evaluation/RQ4/requirements.txt` for the RQ4 figures).
- A C/C++ toolchain, Z3 (we used 4.15.4), Java and Eldarica 2.3 on `PATH` (`z3`, `eld`).
  cvc5 comes with the pinned Lean dependencies.

On Ubuntu:

```sh
sudo apt-get install -y clang lld z3 libc++-dev libc++abi-dev default-jre-headless unzip
curl -fsSL https://github.com/uuverifiers/eldarica/releases/download/v2.3/eldarica-bin-2.3.zip -o eldarica.zip
unzip eldarica.zip -d "$HOME/eldarica" && export PATH="$HOME/eldarica/eldarica:$PATH"
# cvc5 needs the host glibc while Lean uses its own C++ runtime:
cat > "$HOME/flex-clang" <<'EOF'
#!/bin/sh
exec /usr/bin/clang -fuse-ld=lld -L "$(lean --print-prefix)/lib" "$@"
EOF
chmod +x "$HOME/flex-clang" && export LEAN_CC="$HOME/flex-clang"
```

The same setup is in `Flex/.github/workflows/lean_action_ci.yml`.

## 2. Build and smoke test (about 20–40 minutes, mostly dependency builds)

```sh
cd Flex
MATHLIB_NO_CACHE_ON_UPDATE=1 lake build          # fetches pinned dependencies; do not run `lake update`
lake lean Tests/SMT.lean -- --error=hasSorry     # small tactic test
lake lean Demo/Imp.lean                          # the Imp verifier and its example programs
(cd ../flex-benchmarks && python3 CHC-COMP/unpack.py)   # unpack and verify the CHC-COMP corpus
```

Every command below runs from `Flex/` unless stated otherwise. Each harness writes a fresh
output folder containing per-query logs, `results.csv`/`results.jsonl` and a `summary.json`.
Runs can be interrupted and resumed (see each README). Full runs take many hours; the
**smoke** variants check the pipeline end to end in minutes.

## 3. RQ1: case studies (`evaluation/RQ1/README.md`)

```sh
# smoke: one case
python3 scripts/benchmark_rq1.py --discharge --variants zap_fix_deep spacer eldarica \
  --cases cstr/GhostGPtrStrlen --output evaluation/results/RQ1/smoke
# full (61 VCs x 3 variants)
python3 scripts/benchmark_rq1.py --discharge --jobs 2 --variants zap_fix_deep spacer eldarica \
  --output evaluation/results/RQ1/full
python3 scripts/rq1_table.py evaluation/results/RQ1/full    # numbers in the RQ1 table
```

## 4. RQ2: Zap vs. search-based tactics (`evaluation/RQ2/README.md`)

```sh
B=../flex-benchmarks
# smoke: four Liquid Fixpoint queries x three variants
python3 -B evaluation/RQ2/benchmark_rq2.py --manifest $B/rq2/smoke/manifest.json --count 0 \
  --output evaluation/results/RQ2/smoke
# full: each set separately, three repetitions (serial timing; use --workers N only for exploration)
for set in liquid-fixpoint flux_tests flux-medium wave flux-other; do
  python3 -B evaluation/RQ2/benchmark_rq2.py --manifest $B/rq2/$set/manifest.json \
    --count 0 --repeats 3 --output evaluation/results/RQ2/$set
done
python3 -B evaluation/RQ2/benchmark_rq2.py --corpus $B/CHC-COMP/generated \
  --count 0 --repeats 3 --output evaluation/results/RQ2/chc-comp
```

## 5. RQ3a: refinement-type CHCs (`evaluation/RQ3a/README.md`)

Run from `flex-benchmarks/`:

```sh
cd ../flex-benchmarks
# smoke: 4 queries x the paper's three arms (Flex = Zap + Fix, Spacer alone, Eldarica alone)
python3 -B ../Flex/evaluation/RQ3a/benchmark.py --benchmarks . --count 4 \
  --configs zap_fix spacer_only eldarica_only --workers 1 --no-figures \
  --output ../Flex/evaluation/results/RQ3a/smoke
# full: every query x the same arms (add `se flex` for the combined pipelines)
python3 -B ../Flex/evaluation/RQ3a/benchmark.py --benchmarks . --count 0 \
  --configs zap_fix spacer_only eldarica_only --workers 4 --no-figures \
  --output ../Flex/evaluation/results/RQ3a/full
python3 -B ../Flex/evaluation/RQ3a/report.py --tables-only ../Flex/evaluation/results/RQ3a/full
```

## 6. RQ3b: CHC-COMP (`evaluation/RQ3b/README.md`)

Run from `flex-benchmarks/`:

```sh
cd ../flex-benchmarks
# smoke: 6 tasks x the paper's three arms
python3 -B ../Flex/evaluation/RQ3b/benchmark.py --benchmarks . --count 6 --workers 2 \
  --configs zap_fix spacer_only eldarica_only --output ../Flex/evaluation/results/RQ3b/smoke
# full: 1,730 tasks x 3 arms (resume with the same command plus --resume)
python3 -B ../Flex/evaluation/RQ3b/benchmark.py --benchmarks . --count 0 --workers 5 \
  --configs zap_fix spacer_only eldarica_only --output ../Flex/evaluation/results/RQ3b/full
python3 -B ../Flex/evaluation/RQ3b/report.py ../Flex/evaluation/results/RQ3b/full
```

## 7. RQ4: qualifier scraping (`evaluation/RQ4/README.md`)

Run from `flex-benchmarks/`. RQ4 needs Z3 but neither Eldarica nor Java.

```sh
cd ../flex-benchmarks
# smoke: 3 queries (one per corpus) x the five scraping configurations
python3 -B ../Flex/evaluation/RQ4/benchmark.py --benchmarks . --smoke \
  --output ../Flex/evaluation/results/RQ4/smoke
python3 -B ../Flex/evaluation/RQ4/report.py --results ../Flex/evaluation/results/RQ4/smoke
# full: the paper's 391 CHCs x 5 configurations (resume with the same command plus --resume)
python3 -B ../Flex/evaluation/RQ4/benchmark.py --benchmarks . --workers 1 \
  --output ../Flex/evaluation/results/RQ4/full
python3 -B ../Flex/evaluation/RQ4/report.py --results ../Flex/evaluation/results/RQ4/full
```

Timings depend on the machine and on the number of workers; coverage numbers should match
the paper up to timeouts near the budget.
