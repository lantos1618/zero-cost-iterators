#!/usr/bin/env bash
# Full replay of the `Iter` library and the `tasks` CLI, Devin VM / any machine with elan.
# Build, axiom audit, theorem list, no-sorry scan, 300 generated inputs per task, 34 fixture
# commands, and the emitted-C allocation check. BENCH=1 also runs the Lean and C++ benchmarks (not gated).
# Raw outputs + exit codes -> results/*.txt. Exit 0 iff no row is unexpected.
set -u
cd "$(dirname "$0")"
export PATH=$HOME/.elan/bin:$PATH
UNEXPECTED=0; TOTAL=0
R=$PWD/results; rm -rf "$R"; mkdir -p "$R"
run() { local n=$1 d=$2 want=$3; shift 3; (cd "$d" && "$@") > "$R/$n.txt" 2>&1; local s=$?
  echo "exit=$s" >> "$R/$n.txt"; TOTAL=$((TOTAL+1)); local tag=ok; [ "$s" = "$want" ] || { tag=UNEXPECTED; UNEXPECTED=$((UNEXPECTED+1)); }
  printf '%-16s exit=%-3s want=%-3s %-10s %s\n' "$n" "$s" "$want" "$tag" "$(grep -E 'audited|all listed|MISSING|TASKCHECK fails|TASKS_REPLAY|CHECK_C|up to date|differ|error' "$R/$n.txt" | tail -1 | cut -c1-90)"; }
run build iter 0 lake build
run audit iter 0 lake env lean TaskAudit.lean
run theorems . 0 sh -c 'for n in Iter.denotes_array Iter.Denotes.take Iter.Denotes.enumerate Iter.Denotes.foldl Iter.Denotes.find? Iter.Denotes.forIn Iter.Denotes.groupFold Iter.Cost.lower_result Iter.Cost.lower_allocs Iter.Cost.lower_pulls_le Iter.Cost.lower_pulls Iter.Cost.lower_calls Iter.Cost.lower_eq_hand Iter.Cost.mut_staged Iter.Cost.mut_dup Iter.Cost.mut_noexit Iter.Rewrite.u64Laws Iter.Rewrite.sum_select Iter.Rewrite.select_mask Iter.Rewrite.sum_lanes Iter.Rewrite.chain_lanes Iter.Gen.opt_correct Iter.Gen.wordPipe_gen Iter.Rewrite.sum_mul Iter.Rewrite.chain_lanes_mul Iter.Rewrite.find_blocks Iter.Rewrite.chain_find_blocks Iter.Rewrite.summary_split Iter.Rewrite.head_filter Iter.Rewrite.getLast_filter Tasks.logPipe_spec Tasks.salesPipe_spec Tasks.salesPipe_keys Tasks.manifestPipe_spec; do grep -qF "AUDIT $n " results/audit.txt || { echo MISSING $n; exit 1; }; done; echo all listed'
run no_sorry . 1 grep -rnwE "sorry|admit|native_decide|axiom" iter --include=*.lean --exclude-dir=.lake
run taskcheck . 0 iter/.lake/build/bin/taskcheck
run fixtures . 0 tasks/replay.sh
run check_c iter 0 python3 check_c.py
run gen_fresh iter 0 sh -c '.lake/build/bin/gencpp | cmp - gen/proved_gen.hpp && echo generated header up to date'
[ "${BENCH:-0}" = 1 ] && { run bench iter 0 .lake/build/bin/bench
  run bench_cpp iter 0 sh -c 'g++ -O2 -std=c++20 -o .lake/build/bench_cpp bench.cpp && .lake/build/bench_cpp'
  run bench_cpp_native iter 0 sh -c 'g++ -O3 -march=native -std=c++20 -o .lake/build/bench_cpp_native bench.cpp && .lake/build/bench_cpp_native'
  grep -h BENCH "$R/bench.txt" "$R/bench_cpp.txt" "$R/bench_cpp_native.txt"; }
echo "TOTAL=$TOTAL UNEXPECTED=$UNEXPECTED"
[ $UNEXPECTED = 0 ]
