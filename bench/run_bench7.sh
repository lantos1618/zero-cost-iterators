#!/usr/bin/env bash
# 5-kernel generated-vs-handwritten benchmark (definition: PLAN_bench7.md, fixed before timing).
# usage: bench/run_bench.sh --dataset PATH/siftsmall.tgz [--rounds 31] [--cpu 2] [--out DIR]
set -euo pipefail
cd "$(dirname "$0")"
DS=; ROUNDS=31; CPU=2; OUT=$PWD/results
while [ $# -gt 0 ]; do case $1 in --dataset) DS=$2; shift 2;; --rounds) ROUNDS=$2; shift 2;; --cpu) CPU=$2; shift 2;; --out) OUT=$2; shift 2;; *) echo "bad arg $1"; exit 2;; esac; done
fail() { echo "BENCH FAIL: $*"; exit 1; }
[[ "$ROUNDS" =~ ^[0-9]+$ ]] && [ "$ROUNDS" -ge 1 ] && [ "$ROUNDS" -le 1000 ] || { echo "rounds must be 1..1000"; exit 2; }
[ -f "$DS" ] || { echo "--dataset PATH required"; exit 2; }
PIN=df5907f88abf25ea8a4ead853266f8405b27f43e64bc306be32dc5531d1e7a93
[ "$(sha256sum < "$DS" | cut -d' ' -f1)" = "$PIN" ] || fail "dataset sha256 != pin $PIN"
rm -rf work "$OUT"; mkdir -p work/data "$OUT"
tar xzf "$DS" -C work/data || fail "extract dataset"
sha256sum -c dataset_members.sha256 || fail "dataset member drift"
python3 prep.py | tee "$OUT/prep.txt" || fail "dataset check"
{ lscpu | grep -E "Model name|^CPU\(s\)|Thread|MHz"; uname -srm; gcc --version | head -1; clang --version | head -1
  echo "pinning: taskset -c $CPU; rounds=$ROUNDS"; cat /sys/devices/system/cpu/cpu$CPU/cpufreq/scaling_governor 2>/dev/null || echo "governor: n/a"; } > "$OUT/host.txt"
cat "$OUT/host.txt"
K="dot l1 l2 ham osl"; declare -A V=([dot]=dot [l1]=l1 [l2]=l2 [ham]=ham [osl]=osl)
CHK=../bridge/.lake/build/bin/i8check
# the compiled C/Bend must be what the .loop() front door emits now, and what was locked by hash
../bridge/.lake/build/bin/pipegen work/pipegen > "$OUT/pipegen.txt" || fail "pipegen"
for k in $K; do for f in i8dot.c prog.bend; do cmp work/pipegen/$k/$f ../gen7/$k/$f || fail "gen7/$k/$f is not the current pipegen output"; done; done
(cd ../gen7 && sha256sum -c SHA256SUMS) > "$OUT/gen7_lock_check.txt" || fail "gen7 differs from the hash lock"
for k in $K; do $CHK exact ../gen7/${V[$k]}/i8dot.c ../gen7/${V[$k]}/prog.bend > "$OUT/gate_$k.txt" || fail "exact gate $k"; tail -1 "$OUT/gate_$k.txt"; done
sha256sum ../gen7/{dot,l1,l2,ham,osl}/i8dot.c ../gen7/{dot,l1,l2,ham,osl}/prog.bend hand_*.c bench.c > "$OUT/compiled_sources.sha256"
for cc in gcc clang; do for fl in "-O3" "-O3 -march=native"; do
  cfg=${cc}_$(echo "$fl" | tr -dc 'a-zA-Z0-9'); B=work/$cfg; mkdir -p $B
  for k in $K; do
    $cc $fl -std=c11 -c -o $B/gen0_$k.o ../gen7/${V[$k]}/i8dot.c
    objcopy --redefine-sym i8dot=gen_$k $B/gen0_$k.o $B/gen_$k.o
    $cc $fl -std=c11 -c -o $B/hand_$k.o hand_$k.c
    for f in gen hand; do objdump -d --no-show-raw-insn $B/${f}_$k.o | grep -P '^\s+[0-9a-f]+:' | sed -E 's/^\s+[0-9a-f]+:\s+//; s/<[^>]*>//g; s/\b[0-9a-f]{2,}\b/ADDR/g' > $B/${f}_$k.s; done
    if cmp -s $B/gen_$k.s $B/hand_$k.s; then sh=identical; else sh="differs($(diff $B/gen_$k.s $B/hand_$k.s | grep -c '^[<>]') lines; gen $(wc -l < $B/gen_$k.s) hand $(wc -l < $B/hand_$k.s) insns)"; fi
    echo "$cfg $k normalized-asm gen-vs-hand: $sh" | tee -a "$OUT/codeshape.txt"
    cp $B/gen_$k.s "$OUT/asm_${cfg}_gen_$k.s"; cp $B/hand_$k.s "$OUT/asm_${cfg}_hand_$k.s"
  done
  for o in $B/gen_*.o $B/hand_*.o; do u=$(nm -u $o | awk '{print $2}' | tr '\n' ' '); echo "$cfg $(basename $o) undefined: [$u]" >> "$OUT/imports.txt"; [ -z "$u" ] || fail "$o imports $u"; done
  $cc $fl -std=c11 -c -o $B/bench.o bench.c
  $cc $fl -o $B/bench_A $B/bench.o $B/gen_*.o $B/hand_*.o
  $cc $fl -o $B/bench_B $B/bench.o $B/hand_*.o $B/gen_*.o
  for L in A B; do
    nm -n $B/bench_$L | grep -E ' T (gen|hand)_' > "$OUT/layout_${cfg}_$L.txt"
    taskset -c $CPU $B/bench_$L correct > "$OUT/correct_${cfg}_$L.txt" || fail "correctness $cfg $L"
    taskset -c $CPU $B/bench_$L time $ROUNDS > "$OUT/raw_${cfg}_$L.csv" || fail "timing $cfg $L"
    [ "$(wc -l < "$OUT/raw_${cfg}_$L.csv")" = $((ROUNDS * 10 + 1)) ] || fail "incomplete $cfg $L"
    echo "timed $cfg layout $L"
  done
done; done
cat "$OUT/correct_gcc_O3_A.txt"
for f in "$OUT"/correct_*.txt; do cmp -s <(grep -v '^$' "$f") <(grep -v '^$' "$OUT/correct_gcc_O3_A.txt") || fail "correctness output differs: $f"; done
sha256sum -c "$OUT/compiled_sources.sha256" > "$OUT/compiled_sources_recheck.txt" || fail "compiled sources changed during the run"
python3 analyze.py "$OUT" | tee "$OUT/summary.txt"
