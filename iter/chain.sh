#!/bin/sh
# Result chains across compilers: results must be equal before timing; prints ns per call and
# the instruction count of each function. Usage: sh iter/chain.sh
cd "$(dirname "$0")"
OUT=${OUT:-/tmp/chain}; mkdir -p "$OUT"
run() {
  tag=$1; shift
  command -v "$1" >/dev/null || { echo "skip $tag: no $1"; return; }
  "$@" -std=c++20 -w -o "$OUT/$tag" chain.cpp || { echo "skip $tag: build failed"; return; }
  "$@" -std=c++20 -w -S -o "$OUT/$tag.s" chain.cpp
  echo "== $tag"
  taskset -c 1 "$OUT/$tag" | sed 's/median_ns_per_item_x100=\([0-9]*\).*/ns_per_call_x100=\1/'
  for f in handCheck handEq expFlat expNested provedCheck; do
    sym=$(grep -o "^_Z[A-Za-z0-9_]*$f[A-Za-z0-9_]*:" "$OUT/$tag.s" | head -1 | tr -d :)
    [ -n "$sym" ] || sym=$(grep -o "^_ZL[A-Za-z0-9_]*$f[A-Za-z0-9_]*:" "$OUT/$tag.s" | head -1 | tr -d :)
    cnt=$(awk -v s="$sym:" 'index($0,s)==1{on=1;next} on&&/^\.LFE|^\.Lfunc_end|^\t\.cfi_endproc/{exit} on&&/^\t[a-z]/&&!/^\t\./{c++} END{print c+0}' "$OUT/$tag.s")
    echo "INSNS $tag $f $cnt"
  done
}
run gcc12_O2 g++-12 -O2
run gcc12_native g++-12 -O3 -march=native
run clang15_O2 clang++-15 -O2
run clang15_native clang++-15 -O3 -march=native
