#!/bin/sh
# Try to prove the speed claim wrong. Claim: on every workload in falsify.cpp, the generated (proved) loop is
# no more than 5% slower than the faster of two hand-written C++ loops: the plain `if` loop and the
# branch-free loop (bf*). Builds falsify.cpp with every compiler found below, plus GCC profile-guided
# optimisation, runs each pinned to one core, and prints FALSIFIED for every row where the claim fails.
# Usage: sh falsify.sh [items]   (default 1,000,000)
cd "$(dirname "$0")" || exit 2
N=${1:-1000000}
OUT=.lake/build/falsify; mkdir -p "$OUT"
PIN=; command -v taskset >/dev/null && PIN='taskset -c 2'
run() {  # tag, then compiler and flags
  tag=$1; shift
  command -v "$1" >/dev/null || { echo "SKIP $tag ($1 not found)"; return; }
  "$@" -std=c++20 -w -o "$OUT/$tag" falsify.cpp || { echo "BUILD_FAIL $tag"; return; }
  $PIN "$OUT/$tag" "$N" | sed "s/^/$tag /" >> "$OUT/all.txt"
}
: > "$OUT/all.txt"
run gcc11_O2 g++-11 -O2
run gcc11_native g++-11 -O3 -march=native
run gcc12_O2 g++-12 -O2
run gcc12_native g++-12 -O3 -march=native
run clang15_O2 clang++-15 -O2
run clang15_native clang++-15 -O3 -march=native
if command -v g++-11 >/dev/null; then  # PGO: train on a smaller run, then rebuild with the profile
  rm -f "$OUT"/*.gcda
  g++-11 -O2 -std=c++20 -w -fprofile-generate -fprofile-dir="$OUT" -o "$OUT/pgo_gen" falsify.cpp &&
    $PIN "$OUT/pgo_gen" 200000 > /dev/null &&
    run gcc11_pgo g++-11 -O2 -fprofile-use -fprofile-dir="$OUT" -fprofile-partial-training
fi
python3 - "$OUT/all.txt" <<'PY'
import re, sys, collections
t = collections.defaultdict(dict); bad = []
for line in open(sys.argv[1]):
    if 'results_equal=false' in line: bad.append(line.split()[0])
    m = re.match(r'(\S+) BENCH (\S+)/(\S+) median_ns_per_item_x100=(\d+) min=(\d+) max=(\d+)', line)
    if m: t[(m[1], m[2])][m[3]] = (int(m[4]) / 100, int(m[5]) / 100, int(m[6]) / 100)
print('| build | pipeline | plain hand | branch-free hand | ours | ours / best hand | verdict |')
print('|---|---|---:|---:|---:|---:|---|')
fails = 0
for (build, pipe), v in t.items():
    hands = [v[k][0] for k in ('hand', 'bf') if k in v]
    best = min(hands); r = v['ours'][0] / best
    verdict = 'FALSIFIED' if r > 1.05 else ('win' if r < 0.95 else 'tie')
    fails += verdict == 'FALSIFIED'
    f = lambda k: f"{v[k][0]:.2f}" if k in v else '-'
    print(f"| {build} | {pipe} | {f('hand')} | {f('bf')} | {f('ours')} | {r:.2f} | {verdict} |")
print(f"FALSIFY rows={len(t)} falsified={fails} wrong_results={len(bad)}")
sys.exit(1 if bad else 0)
PY
