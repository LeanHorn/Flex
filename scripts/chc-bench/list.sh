#!/bin/zsh
# list.sh [BENCH_DIR]: print "VC ROOT" for every κ VC in the four CHC suites.
B=${1:-${0:A:h}/../../../flex-benchmarks}; B=${B:A}
kappa='∃ \(?k[A-Za-z0-9_]* *:'
for f in $(grep -lE "$kappa" $(find $B/flux_tests -path '*/Flux/VC/*.lean') | sort); do echo "$f $B/flux_tests"; done
for p in $B/flux-medium/*(/); do
  for f in $(grep -lE "$kappa" $(find $p -path '*/Flux/VC/*.lean') | sort); do echo "$f $p"; done
done
for f in $(grep -lE "$kappa" $(find $B/wave -path '*/Flux/VC/*.lean') | sort); do echo "$f $B/wave"; done
for f in $(grep -lE "$kappa" $(find $B/liquid-fixpoint/lean-chc-queries/tests -name '*.lean') | sort); do echo "$f ${f:h}"; done
