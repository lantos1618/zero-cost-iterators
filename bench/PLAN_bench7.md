# i8red7 benchmark plan (written before any i8red7 timing)

Identical protocol to i8red6 `PLAN_bench6.md` / i8red5 `PLAN_bench.md` (both kept in this directory).
The only intended difference is where the generated sources come from: the five timed generated
kernels are `gen7/{dot,l1,l2,ham,osl}/i8dot.c`, emitted by the `.loop()` front door
(`bridge/.lake/build/bin/pipegen`, chains in `bridge/Pipe/Chains.lean`). Their bytes equal i8red6's
`variants/{pos,l1,l2,ham,osl}/i8dot.c` except line 1 (the provenance comment). Hand-written baselines
`hand_*.c`, `bench.c`, `prep.py`, `analyze.py`, guards, ABI, flags, separate translation units, no LTO,
pinning (taskset -c 2), 31 rotated rounds, two link layouts (A gen-first, B hand-first), dataset pin
(SIFT10K siftsmall.tgz sha256 df5907f8...7a93, centered x-128, 100x10000 pairs at n=128) and the compiler
matrix (gcc 11.4 / clang 14 x -O3 / -O3 -march=native) are unchanged.

Fail-closed steps before compiling (no effect on timing): rerun pipegen into `work/pipegen` and require
byte equality with `gen7/`; check `gen7/SHA256SUMS` (the hash lock); run `i8check exact` on each of the five
gen7 pairs; record sha256 of every compiled source; re-check those hashes after timing.

Primary: gcc -O3. Per kernel pass: generated/manual median ratio in [0.95, 1.05] in BOTH layouts.
All-five success: all five pass in both layouts under gcc -O3. Other configs reported in full, not used
for the verdict. Run 1 is the result of record; run 2 uses the identical protocol to check
reproducibility. Both are reported; no run is discarded. A miss is investigated (code shape, noise), not
re-defined.
