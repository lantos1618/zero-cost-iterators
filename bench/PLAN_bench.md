# Benchmark plan (written and saved BEFORE any timing run)

Question: is each of the 5 generated kernels within 5% of an independently hand-written C kernel?

- Workload (all 5 kernels): pinned SIFT10K (siftsmall.tgz sha256 df5907f8...), coordinates checked to be
  exact integers in [0,255], centered x-128 to int8. 100 queries x 10,000 base vectors, n = 128:
  1,000,000 calls per kernel per trial. Norms, loading, validation and correctness are excluded from timing.
- Candidate: the byte-identical emitted `variants/<k>/i8dot.c`; symbol renamed on the object file only
  (`objcopy --redefine-sym i8dot=gen_<k>`). Hand-written: `hand_<k>.c`, idiomatic, allocation-free, same
  signature, same length guard value, int32_t accumulator. Each function in its own translation unit; all
  called through the same `volatile` function-pointer table from `bench.c`; no LTO.
- Correctness (untimed, fail closed): generated == hand-written == independent int64 reference for all
  1,000,000 pairs per kernel; per-kernel checksums; squared L2 only: top-1/top-10 ordered (index tie-break) and
  tie-aware top-100 vs the published ground truth.
- Timed trial: one pass over all 1M pairs for one (kernel, form) cell, summing outputs into an int64 that must
  equal that kernel's checksum (else exit 3). One untimed warm-up pass per cell. 31 rounds per binary; in round r
  the 10 cells run in order rotated by r.
- Configs: gcc 11.4 and clang 14, each with `-O3` and `-O3 -march=native`; link layouts A (generated objects
  first) and B (hand-written first) = 8 binaries. Pinned with `taskset -c 2`.
- PRIMARY configuration (fixed now): gcc -O3, both layouts.
- Statistic: per cell median ms over 31 rounds; spread = IQR and min-max. Ratio = median(gen)/median(hand);
  signed % = (ratio-1)*100. Strict pass: 0.95 <= ratio <= 1.05.
  Flags: "faster-only miss" (ratio < 0.95); "layout-sensitive" (pass in one layout, fail in the other).
- All-five success = all 5 kernels pass in BOTH layouts in the primary configuration. Other configs are
  reported in full but do not change the verdict.
- If any primary cell misses: inspect normalized assembly and spread, then rerun the whole protocol once.
  Both runs are reported; the first run is kept.
