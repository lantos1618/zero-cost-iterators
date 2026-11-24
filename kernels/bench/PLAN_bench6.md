# i8red6 benchmark plan (written before any i8red6 timing)

Identical protocol to i8red5 `bench/PLAN_bench.md` (copied unchanged in this directory). The only intended
difference is in the generated sources: `variants/l1/i8dot.c` now spells the absolute value
`r0 = r0 < 0 ? -r0 : r0;` (IR op AbsT) and `variants/ham/i8dot.c` spells the nonzero test
`r0 = r0 != 0;` after the signed int32 subtraction (IR op Ne0). dot, squared L2 and one-sided L1 are
byte-identical to i8red5. Hand-written baselines `hand_*.c`, `bench.c`, `prep.py`, `analyze.py`,
guards, ABI, flags, pinning (taskset -c 2), 31 rotated rounds, two link layouts and the
compiler matrix (gcc 11.4 / clang 14 x -O3 / -O3 -march=native) are unchanged.

Added fail-closed steps (no effect on timing): before compiling, `run_bench.sh` runs the exact gate
(`bridge/.lake/build/bin/i8check exact`) on each of the five `variants/*/i8dot.c` + `prog.bend`
pairs it then compiles, records their sha256 in `compiled_sources.sha256`, and re-checks the hashes
after timing.

Primary: gcc -O3. Per kernel pass: generated/manual median ratio in [0.95, 1.05] in BOTH layouts.
All-five success: all five pass in both layouts under gcc -O3. Run 1 is the result of record; run 2
uses the identical protocol to check reproducibility. Both are reported. No other run is discarded.
