#!/bin/zsh
# run.sh LIST OUTDIR [REPO] [JOBS]: probe every "VC ROOT" line of LIST with the Flex build in REPO
# (default: this checkout), JOBS at a time. Resumable: VCs whose log has a PROBE line are skipped.
D=${0:A:h}
if [[ $1 == --one ]]; then
  # Internal: run.sh --one VC ROOT, with CHC_BENCH_OUT and CHC_BENCH_REPO set.
  vc=$2 root=$3 out=$CHC_BENCH_OUT key=${${2#*/flex-benchmarks/}//\//_}
  grep -q "PROBE" $out/$key.log 2>/dev/null && exit 0
  python3 $D/flat.py $vc $root $out/$key || exit 0
  cd $CHC_BENCH_REPO
  timeout 600 lake --log-level=error lean $out/$key > $out/$key.log 2>&1 || echo "EXIT $?" >> $out/$key.log
  exit 0
fi
list=${1:A}; out=${2:A}; repo=${${3:-$D/../..}:A}; jobs=${4:-6}
mkdir -p $out
export CHC_BENCH_OUT=$out CHC_BENCH_REPO=$repo
# One process per VC; xargs bounds the parallelism.
awk '{print $1, $2}' $list | xargs -n 2 -P $jobs $D/run.sh --one
echo "$(grep -l PROBE $out/*.log | wc -l | tr -d ' ') of $(wc -l < $list | tr -d ' ') probed in $out"
