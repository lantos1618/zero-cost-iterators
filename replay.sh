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
  printf '%-16s exit=%-3s want=%-3s %-10s %s\n' "$n" "$s" "$want" "$tag" "$(grep -E 'audited|all listed|MISSING|TASKCHECK fails|TASKS_REPLAY|CHECK_C|up to date|differ|error|fuzz' "$R/$n.txt" | tail -1 | cut -c1-90)"; }
run build iter 0 lake build
run audit iter 0 lake env lean TaskAudit.lean
run theorems . 0 sh -c 'for n in Iter.denotes_array Iter.Denotes.take Iter.Denotes.enumerate Iter.Denotes.foldl Iter.Denotes.find? Iter.Denotes.forIn Iter.Denotes.groupFold Iter.Denotes.takeWhile Iter.Denotes.drop Iter.Denotes.dropWhile Iter.Denotes.stride Iter.denotes_iterFrom Iter.denotes_iterIdx Iter.Denotes.zip Iter.Denotes.count Iter.Denotes.any Iter.Denotes.all Iter.Denotes.contains Iter.Denotes.min? Iter.Denotes.max? Iter.Cost.lower_result Iter.Cost.lower_allocs Iter.Cost.lower_pulls_le Iter.Cost.lower_pulls Iter.Cost.lower_calls Iter.Cost.lower_eq_hand Iter.Cost.mut_staged Iter.Cost.mut_dup Iter.Cost.mut_noexit Iter.Rewrite.u64Laws Iter.Rewrite.sum_select Iter.Rewrite.select_mask Iter.Rewrite.sum_lanes Iter.Rewrite.chain_lanes Iter.Gen.opt_correct Iter.Gen.wordPipe_gen Iter.Gen.count_correct Iter.Gen.cRun_eq Iter.Gen.printed_correct Iter.Gen.printed_count Iter.Gen.cRed_eq Iter.Gen.printed_red Iter.Gen.cRunS_eq Iter.Gen.printed_summary Iter.Gen.cAdapt_eq Iter.Gen.printed_adapt Iter.Gen.mod_zero_iff_mul Iter.Gen.nodiv_ok Iter.Gen.P.nodiv_eval Iter.Gen.nodiv_run Iter.Gen.nodiv_red Iter.Gen.nodiv_count Iter.Gen.wordPipe_nodiv Iter.Gen.wordPipe_nodiv_count Iter.Gen.wordPipe_nodiv_max Iter.Gen.aBlocks_fst Iter.Gen.cLoop_trans Iter.Gen.cRunR_eq Iter.Gen.printed_range Iter.Gen.printed_range_count Iter.Gen.E.toC_eval Iter.Gen.P.toC_eval Iter.Gen.X.toC_eval Iter.Gen.Q.toC_eval Iter.Gen.word_step Iter.Gen.red_step Iter.Gen.rec_step Iter.Gen.red_correct Iter.Gen.wordPipe_count Iter.Gen.wordPipe_max Iter.Gen.fast1_correct Iter.Gen.step1_filter Iter.Gen.fast2_correct Iter.Gen.step1_dropWhile Iter.Gen.step1_step2 Iter.Gen.recPipe_gen Iter.Gen.fast3_correct Iter.Gen.stepB_step2 Iter.Gen.foldl_mix Iter.Gen.recPipe_adapt Iter.Gen.q6_gen Iter.Gen.q6_adapt Iter.Gen.q6_total Iter.Rewrite.sum_mul Iter.Rewrite.chain_lanes_mul Iter.Rewrite.find_blocks Iter.Rewrite.chain_find_blocks Iter.Rewrite.summary_split Iter.Rewrite.head_filter Iter.Rewrite.getLast_filter Tasks.logPipe_spec Tasks.salesPipe_spec Tasks.salesPipe_keys Tasks.manifestPipe_spec; do grep -qF "AUDIT $n " results/audit.txt || { echo MISSING $n; exit 1; }; done; echo all listed'
run no_sorry . 1 grep -rnwE "sorry|admit|native_decide|axiom" iter --include=*.lean --exclude-dir=.lake
run taskcheck . 0 iter/.lake/build/bin/taskcheck
run fixtures . 0 tasks/replay.sh
run check_c iter 0 python3 check_c.py
run gen_fresh iter 0 sh -c '.lake/build/bin/gencpp | cmp - gen/proved_gen.hpp && echo generated header up to date'
FZ='B=.lake/build; $B/bin/fuzzcpp cpp 300 > $B/fuzz.cpp && $B/bin/fuzzcpp expect 300 > $B/fuzz_expect.txt'
UB='g++ -std=c++20 -O1 -w -fsanitize=undefined -fno-sanitize-recover=all'
run fuzz_cpp iter 0 sh -c "$FZ && $UB -o \$B/fuzz \$B/fuzz.cpp && \$B/fuzz | cmp - \$B/fuzz_expect.txt && echo fuzz: \$(wc -l < \$B/fuzz_expect.txt) printed-C++ results equal Lean"
run fuzz_mutant iter 1 sh -c "$FZ && sed 's/lp = kb ? \&e : lp;/lp = \&e;/' \$B/fuzz.cpp > \$B/fuzz_mut.cpp && ! cmp -s \$B/fuzz.cpp \$B/fuzz_mut.cpp && { $UB -o \$B/fuzz_mut \$B/fuzz_mut.cpp || exit 3; } && \$B/fuzz_mut | cmp -s - \$B/fuzz_expect.txt; r=\$?; echo fuzz: last-row mutant caught=\$r; exit \$r"
run fuzz_mutant2 iter 1 sh -c "$FZ && sed 's/{ starts += lp + 1 != &e; cnt += 1;/{ starts += lp + 1 != \&e;/' \$B/fuzz.cpp > \$B/fuzz_mut2.cpp && { $UB -o \$B/fuzz_mut2 \$B/fuzz_mut2.cpp || exit 3; } && \$B/fuzz_mut2 | cmp -s - \$B/fuzz_expect.txt; r=\$?; echo fuzz: branchy-count mutant caught=\$r; exit \$r"
run fuzz_mutant3 iter 1 sh -c "$FZ && sed 's/ | (b - 1ULL))/ | (0ULL - b))/' \$B/fuzz.cpp > \$B/fuzz_mut3.cpp && grep -q '| (0ULL - b))' \$B/fuzz_mut3.cpp && { $UB -o \$B/fuzz_mut3 \$B/fuzz_mut3.cpp || exit 3; } && \$B/fuzz_mut3 | cmp -s - \$B/fuzz_expect.txt; r=\$?; echo fuzz: min-mask mutant caught=\$r; exit \$r"
run fuzz_policy iter 0 sh -c "$FZ && sed 's/masked = starts \* \([0-9]*\) > w;/masked = !(starts * \\1 > w);/' \$B/fuzz.cpp > \$B/fuzz_pol.cpp && grep -q 'masked = !(' \$B/fuzz_pol.cpp && $UB -o \$B/fuzz_pol \$B/fuzz_pol.cpp && \$B/fuzz_pol | cmp - \$B/fuzz_expect.txt && echo fuzz: inverted switch policy gives the same results"
export PIN=; command -v taskset >/dev/null && PIN='taskset -c 2'
[ "${BENCH:-0}" = 1 ] && { run bench iter 0 .lake/build/bin/bench
  run bench_cpp iter 0 sh -c 'g++ -O2 -std=c++20 -o .lake/build/bench_cpp bench.cpp && $PIN .lake/build/bench_cpp'
  run bench_cpp_native iter 0 sh -c 'g++ -O3 -march=native -std=c++20 -o .lake/build/bench_cpp_native bench.cpp && $PIN .lake/build/bench_cpp_native'
  run falsify iter 0 sh falsify.sh
  run ablate_cpp iter 0 sh -c 'g++ -O2 -std=c++20 -o .lake/build/ablate_cpp ablate.cpp && $PIN .lake/build/ablate_cpp'
  grep -h BENCH "$R/bench.txt" "$R/bench_cpp.txt" "$R/bench_cpp_native.txt" "$R/ablate_cpp.txt"; grep -h FALSIFY "$R/falsify.txt"; }
echo "TOTAL=$TOTAL UNEXPECTED=$UNEXPECTED"
[ $UNEXPECTED = 0 ]
