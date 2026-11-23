# i8red5: one gate, one shared proof, five scalar signed-INT8 reductions, benchmarked against hand-written C

Private milestone in `~/i8red5` (a copy of the three-kernel `~/i8red`). `~/i8red`, r5 (`i8dot-bend-r5.tar.gz`,
sha256 `a6bec014…`), SIFT10K replay v2 (`1ddc9293…`), Zen and every earlier directory and archive are untouched
(both archive sha256s re-checked; `~/i8red` still matches its verified scratch copy).

**Verdict on the 5% target: NOT MET.** Under the primary configuration fixed before timing (gcc 11.4 `-O3`,
both link layouts), dot, squared L2 and one-sided L1 are within 5% of hand-written C. L1 is about 2.05× slower
and Hamming about 5.2× slower, in both layouts and in both runs. The cause is the C statement form the emitter
uses, not the proof, the ABI or the call path (section 7). Under clang 14 all five are within 5% in every
configuration, layout and run, and the generated and hand-written machine code is identical.

| item | where |
|---|---|
| correctness replay | `./run_i8red5.sh` -> `results_i8red5/*.txt`; clean run in `~/i8red5-scratch` (no inherited `.lake`) |
| benchmark | `bench/run_bench.sh --dataset siftsmall.tgz`; plan `bench/PLAN_bench.md` (written before timing) |
| benchmark records | `bench/results_run1/` (first result), `bench/results_run2/` (one fair rerun), `bench/diag/` |
| evidence log | `EVIDENCE_i8red5.txt` |

Toolchain: bend 2.0.40, Lean `leanprover/lean4:v4.15.0` (core only), gcc 11.4.0, clang 14.0.0, Linux 6.8 x86-64
(AWS, "Intel(R) Xeon(R) Processor", 8 vCPUs, 1 thread per core).

## 1. Per-operation numeric contract

Signature (all five): `int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out)`.
Caller assumptions: `a`, `b` each readable for `n` elements, `out` valid, elements in [-128, 127].
Accumulator, registers and temporaries are explicit `int32_t`. `n > guard` returns -1 and leaves `*out`
unchanged; `n = 0` returns 0 with `*out = 0`. INT32_MAX = 2147483647.

| reduction | loop body (IR) | element C after the two loads | element range | guard | worst case N·M |
|---|---|---|---|---|---|
| exact dot | `LdA LdB Mul Acc` | `r0 = r0 * r1;` | [-16256, 16384] | 131071 | 2147467264 |
| L1, sum of absolute differences | `LdA LdB Sub Abs Acc` | `r0 = r0 - r1;` `if (r0 < 0) r0 = -r0;` | [0, 255] | 8421504 | 2147483520 |
| squared L2 | `LdA LdB Sub Sq Acc` | `r0 = r0 - r1;` `r0 = r0 * r0;` | [0, 65025] | 33025 | 2147450625 |
| Hamming, count of a[i] ≠ b[i] | `LdA LdB Sub Abs Bit Acc` | `r0 = r0 - r1;` `if (r0 < 0) r0 = -r0;` `if (r0 > 0) r0 = 1;` | [0, 1] | 2147483647 | 2147483647 |
| one-sided L1, sum of max(a[i]−b[i], 0) | `LdA LdB Sub Pos Acc` | `r0 = r0 - r1;` `if (r0 < 0) r0 = 0;` | [0, 255] | 8421504 | 2147483520 |

New in this milestone: two IR ops, `Pos` (`r0 := max(r0, 0)`) and `Bit` (`r0 := 1 if r0 > 0`), and two C lines.
No new C construct was needed: both lines are instances of the existing `if (v < k) v = e;` / `if (v > k) v = e;`.

**Hamming guard: the proved exact guard 2147483647**, not a conservative one. With element bound M = 1 any
n ≤ INT32_MAX is safe, and `guard_tight` shows 2147483648 would not be. On LP64 `size_t` this is a real
check: lengths ≥ 2^31 return -1. Native strategy (section 5): every build runs with arrays capped at 1 MiB
(over-limit calls never read, in-range lengths beyond the cap are counted as skipped); one gcc -O2 build
additionally allocates two 2 GiB arrays and runs n = N−1 and n = N, where the extreme pairs reach exactly
INT32_MAX.

Each guard is the largest n with n·M ≤ INT32_MAX (`guard_tight`), and each M is attained by admitted bytes
(`elem_bound_attained`), so no larger guard is safe with this accumulator. The gate requires the emitted
`#define` to equal `bound p` for the parsed program.

## 2. What is machine-checked (Lean, `bridge/`)

Same architecture as the three-kernel milestone; per kernel only a certificate was added.

- `structure Cert`: loop body, guard N, element bound M with N·M ≤ INT32_MAX, element function f, and a per-element `step` fact (no fault, element in [−M, M]).
- `cert_loop`: **the single induction** for all five exact reductions. After i iterations the accumulator lies in [−i·M, i·M]; for n ≤ N the C loop never faults and tracks the IR state.
- `cert_total`, `cert_gate`: for any certificate, the rendered file returns −1 with `*out` unchanged when n > N, otherwise 0 with `*out` = Σ f(aᵢ, bᵢ).
- Per kernel: `certDot`, `certL1`, `certL2`, `certHam`, `certOsl`, plus `refRed_dot/l1/l2/ham/osl` tying Σ f to the independent references `refDot`, `refL1`, `refL2`, `refHam` (counts `x ≠ y`) and `refOsl` (`if y < x then x − y else 0`).
- `op_sim`, `op_total`: two new cases each, for `Pos` and `Bit`.
- `gate_total`: one theorem for both gates over the 6 certified programs. The five exact ones are each one line, `exact cert_gate certX xIR rfl (by decide) hr env out0 ha`; wrap keeps r5's `cRun_wrap`.
- `exact_gate_sound` (**main theorem**). Premise: PASS of `Check.gate … true`, the function `i8check exact` runs on the actual file bytes. Conclusion: prog.bend's term is posIR, l1IR, l2IR, hamIR or oslIR. On every admitted input, n = 0 and extreme bytes included, the C semantics returns −1 with `*out` unchanged when n > `bound p`, and otherwise returns 0 with `*out` = `refOf p` of the first n elements, without faulting.
- `exact_gate_zero`, `exact_gate_requires_exact`, `exactCert_wrap`, `gate_requires_certified`, `bound_values`, `guard_tight`, `elem_bound_attained`.

Proof chain: `exact_gate_sound` → `gate_total` → `cert_gate` → `cert_total` → `cert_loop`.

Bend link (`Bridge/BendLink.lean`, over the trusted translation of the actual `kernel.bend` and
`variants/*/prog.bend`):
- `zpos_v`, `zbit_v`: decoding Z{p,n} as p−n turns the translated `zpos`/`zbit` into the IR's `Pos`/`Bit`.
- `exec_v` / `run_v` cover the new ops (whole-state correspondence for every program and input).
- `prog_ham_v`, `prog_osl_v`: the translated actual terms decode to hamIR / oslIR.
- `hamd_v`, `posd_v`, `bend_ham_eq_hamd`, `bend_osl_eq_posd`: the translated evaluator on those terms equals Bend's independent references `hamd`/`posd`, which equal `refHam`/`refOsl`.
- `exact_gate_bend`: PASS ⇒ C result = p−n of `K.acc_of(K.run(q, xs, ys))` for all five translated actual terms.

Audit: `bridge/Audit.lean` lists every `theorem` in both proof files, 110 entries. Axioms used: 30 use
`propext`, `Classical.choice`, `Quot.sound`; 34 `propext`, `Quot.sound`; 24 `propext`; 22 none.
No `sorry`, `admit`, `native_decide` or `axiom`.

## 3. Bend checks (separate checker, `--verdict`)

`variants/{l1,l2,ham,osl}/PROOF_RED.bend` import the actual `kernel.bend` and `prog.bend` and prove, for all
inputs, that `run(prog)` equals `sad`/`ssd`/`hamd`/`posd`. All print `ALL PROOFS CHECK`, exit 0; r5's pos
`PROOF.bend` is rerun too.

## 4. Gate replay on actual emitted files

Exit codes: 0 PASS, 2 C REJECT, 3 IR MISMATCH, 4 Bend REJECT, 5 UNCERTIFIED. The runner compares each actual
exit code with the expected one and fails if any differs. Clean run: **TOTAL=118 UNEXPECTED=0**, script exit 0.

| run | exit | reason |
|---|---|---|
| dot, L1, L2, Hamming, one-sided L1: exact and match, own prog.bend | 0 | PASS |
| wrap exact / match | 3 / 0 | not an exact reduction / certified total |
| product or difference buffer (r5 buf, L2, one-sided L1) | 2 | `stdlib.h` outside subset |
| L2 guard 131071; Hamming guard 2147483648; one-sided L1 guard 8421505 | 2 | `#define` must equal the certified bound |
| L2 or one-sided L1 with the guard line deleted | 2 | statement 0 must be the guard |
| L1 `if (r0 > 0) r0 = -r0;`, Hamming `if (r0 > 0) r0 = 2;`, one-sided L1 `if (r0 < 0) r0 = 1;` | 2 | line outside grammar |
| in-grammar but uncertified: L1 without `Abs`, Hamming without `Abs`, one-sided L1 with `Pos` before `Sub` | 3 exact / 5 match | not exact / uncertified |
| the same three against the real kernel's prog.bend | 3 | IR mismatch |
| C of one kernel against another kernel's prog.bend (8 pairs) | 3 | IR mismatch |
| L2, Hamming, one-sided L1 prog.bend with renamed `prog` def | 4 | not the generated file |
| r4 overflow program (match) | 5 | uncertified |

All emitted files are regenerated by `gen.py` and compared byte for byte; the pos C file is byte-identical to r5's.

## 5. Negative controls on the evaluator, and finite native tests

Each control changes one primitive in `kernel.bend`. In every case the Bend law still passes, because its
reference shares the changed primitive. The regenerated Lean differs, and `BendLink.lean` fails to build.

| change | Bend law | Lean link build |
|---|---|---|
| `zsub` a−b → a+b | L1 `PROOF_RED` passes, exit 0 | fails, line 94 (`zsub_v`) |
| `zpos` max(a,0) → max(−a,0) | one-sided L1 `PROOF_RED` passes, exit 0 | fails, line 109 (`zpos_v`) |
| `zbit` nonzero → 2 | Hamming `PROOF_RED` passes, exit 0 | fails, line 120 (`zbit_v`) |

Native tests (`native/test.c`, finite evidence, not proof) check each emitted kernel against an independent
`int64_t` reference. Cases: n = 0, 1, 2, N−1, N, N+1, N+2 on all four constant extreme pairs (−128/127),
xorshift data at fixed lengths, and 2000 random lengths and offsets. Over-limit calls must return −1 and
leave `*out` unchanged. Builds: gcc -O2, gcc -O3 -march=native, clang -O3, gcc and clang -O1 with
`-fsanitize=undefined -fno-sanitize-recover=all`.

| kernel | calls per build | result |
|---|---|---|
| dot, L1, L2, one-sided L1 | 2045 × 5 builds each | 0 failures, no UBSan report |
| Hamming, 1 MiB cap | 2035 run + 10 skipped, × 5 builds | 0 failures, no UBSan report |
| Hamming, full 2 GiB arrays, gcc -O2 | 2045 | 0 failures; n = N gives 2147483647 |

None of the five objects imports a symbol (no allocator).

## 6. Benchmark definition (fixed in `bench/PLAN_bench.md` before timing)

- **Workload:** pinned SIFT10K (`siftsmall.tgz` sha256 `df5907f8…` and member pins checked, else stop), coordinates checked to be integers in [0,255], centered x−128. 100 queries × 10,000 base vectors at n = 128 = 1,000,000 calls per kernel per trial.
- **Candidate:** the byte-identical emitted `variants/<k>/i8dot.c`, symbol renamed on the object (`objcopy --redefine-sym`).
- **Baseline:** `bench/hand_<k>.c`, idiomatic, allocation-free, same signature, guard value and `int32_t` accumulator.
- **Call path:** every function in its own translation unit, called through one `volatile` function-pointer table; no LTO.
- **Correctness (untimed, fail closed):** generated = hand-written = independent int64 reference on all 1,000,000 pairs per kernel. For squared L2 only, the published ground truth also gives top-1 100/100, top-10 100/100 and tie-aware top-100 100/100 (91/100 identical ordered id lists).
- **Checksums:** dot 1339476007622, L1 4184838222, L2 299992732756, Hamming 117675068, one-sided L1 2058208211.
- **Trial:** one pass over all 1M pairs for one (kernel, form) cell. Its sum must equal the checksum or the run stops; this also prevents dead-code elimination. One warm-up per cell, then 31 rounds per binary with the 10 cells rotated each round.
- **Configs:** gcc 11.4 and clang 14 × `-O3` and `-O3 -march=native` × layout A (generated objects linked first) and B (hand-written first) = 8 binaries, `taskset -c 2`. CPU governor not exposed by this VM.
- **Rule:** ratio = median(gen) / median(hand); pass if 0.95 ≤ ratio ≤ 1.05. Primary = gcc `-O3`. All-five success = all 5 pass in both layouts under the primary config.
- If a primary cell misses: inspect assembly and spread, rerun the whole protocol once, report both runs.

## 7. Benchmark results

Primary config, gcc 11.4 `-O3`: ratio of medians (signed %), run 1 = first result, run 2 = the one rerun.

| kernel | run 1 A | run 1 B | run 2 A | run 2 B | verdict |
|---|---|---|---|---|---|
| dot | 1.049 (+4.9%) | 0.983 (−1.7%) | 1.007 (+0.7%) | 1.002 (+0.2%) | pass |
| L1 | 2.031 (+103%) | 2.070 (+107%) | 2.048 (+105%) | 2.057 (+106%) | **miss, slower** |
| squared L2 | 0.954 (−4.6%) | 1.013 (+1.3%) | 0.980 (−2.0%) | 1.006 (+0.6%) | pass |
| Hamming | 5.247 (+425%) | 5.280 (+428%) | 5.207 (+421%) | 5.405 (+441%) | **miss, slower** |
| one-sided L1 | 0.982 (−1.8%) | 0.994 (−0.6%) | 1.000 (+0.0%) | 1.006 (+0.6%) | pass |

Primary verdict: 6 of 10 kernel-layout cells pass in each run; **all-five target not met**. Neither miss is
layout-sensitive or a faster-only miss.

All configs, kernel-layout cells within 5% (run 1 / run 2):

| config | cells within 5% | misses |
|---|---|---|
| gcc -O3 (primary) | 6/10 / 6/10 | L1 2.03–2.07×, Hamming 5.21–5.41× |
| gcc -O3 -march=native | 6/10 / 6/10 | L1 1.40–1.55×, Hamming 2.01–2.06× |
| clang -O3 | 10/10 / 10/10 | none; ratios 0.982–1.025 |
| clang -O3 -march=native | 10/10 / 10/10 | none; ratios 0.991–1.007 |

Spread: run 1 was noisier. In gcc -O3 layout A, per-cell IQR reached 6.9 ms, and two passing cells sat near
the edge: dot +4.85% and L2 −4.62%. Their gcc machine code is identical (L2) or differs only in register
allocation (dot), so those two values are noise. Run 2 IQRs in the primary config were 0.23–1.97 ms, and the
two misses reproduced within 0.2 of their run-1 ratios. Full medians, IQRs and min–max for all 80 cells per run
are in `bench/results_run*/summary.txt`; raw per-trial times are in `raw_*.csv`.

Code shape (`bench/results_run1/codeshape.txt`, normalized `objdump`):

| config | dot | L1 | L2 | Hamming | one-sided L1 |
|---|---|---|---|---|---|
| clang, both flag sets | identical | identical | identical | identical | identical |
| gcc -O3 | same up to register names | 263 vs 228 | identical | 332 vs 177 | identical |

**Diagnosis (gcc only).** Both forms are vectorized, but in different lane widths:
- The hand-written L1 `acc += d < 0 ? -d : d;` is vectorized in 16-bit lanes (`psubw`). The emitted `if (r0 < 0) r0 = -r0;` stays in 32-bit lanes (`psubd`, `pcmpgtd`).
- The hand-written Hamming `acc += a[i] != b[i];` compares bytes (`pcmpeqb`). The emitted Sub/Abs/Bit chain computes in 32-bit lanes with two compare-and-select steps.

Compile-only checks in `bench/diag/` (normalized gcc -O3 assembly, no timing) pin this on the statement form:
- a hand-written L1 using an `if (d < 0) d = -d;` statement compiles to exactly the generated code;
- the generated L1 with only that line rewritten as `r0 = r0 < 0 ? -r0 : r0;` compiles to exactly the hand-written code;
- the generated Hamming with its two `if` lines replaced by `r0 = r0 != 0;` compiles to exactly the hand-written code.

So the gap comes from how gcc 11 treats a conditional-assignment statement, not from the proof, the guard, the
ABI or the separate translation units. Closing it would mean emitting a ternary or `!=` form, which adds a C
construct to the grammar and two `op_sim` cases. That is not done here, and the first results above stand.

Benchmark run history, all kept: attempt 1 stopped at the dataset member check (tar extraction path bug in
the script, before any build); attempt 2 stopped compiling `bench.c` (`CLOCK_MONOTONIC` hidden by `-std=c11`,
before any timing). Neither produced a timing. Run 1 is the first measured result.

## 8. Trusted boundary

| link | status |
|---|---|
| gate PASS ⇒ C-subset result = IR result = exact reference, all admitted inputs | machine-checked (Lean) |
| IR semantics = translated actual Bend evaluator (incl. Pos, Bit) | machine-checked on the translation |
| `bend2lean.py` construct mapping; its Op whitelist gained `Pos`, `Bit` | **trusted** (regenerated + byte-compared) |
| gate's prog.bend parser vs translator's parser | tied by definitional equality on committed terms + replay, not proved |
| Bend laws (`PROOF_RED.bend`) | checked by Bend, not imported into Lean |
| C-subset fidelity to ISO C (incl. `-x`, comparisons, int8→int32 conversion) | **trusted** |
| headers, flags, ABI, C compilers, machine code | **trusted**; native tests and the benchmark are finite evidence |
| benchmark harness, centering, checksums, ranking check | **trusted** test code, not proved |
| Lean/Bend toolchains, `i8check` binary | **trusted** |

## 9. Toward the reviewer targets

- **Utility.** Five kernels pass one checker, and one induction `cert_loop` covers them. Per kernel: a certificate (element semantics + bound), a `bound` entry and, for new ops, `op_sim` cases. The ≤5% target is met with clang but **not** with the pre-declared primary gcc -O3 configuration (L1, Hamming).
- **Rigor.** The translator is still trusted. Allocation is checked by import inspection, by the gate rejecting `stdlib.h`, and by the buffer controls.
- **Novelty.** Only one transformation shape (scalar fused load–element–accumulate). No SIMD or tiling.

This is **not** a shape-agnostic validator: the gate accepts exactly the canonical rendering of six certified
IR programs.

## 10. Learned vs proposed

- **Learned:** adding two kernels needed two IR ops, two C lines, two certificates and their Bend/Lean link cases. No new induction.
- **Learned:** proof-preserving does not imply performance-preserving across compilers. With gcc 11 the statement form of the emitted C matters (2× and 5×); with clang 14 it does not.
- **Learned:** every evaluator-primitive mutation tried (zsub, zpos, zbit) passes Bend's own law and is caught only by the Lean link.
- **Proposed next:** emit `r0 = r0 < 0 ? -r0 : r0;` and a `!=` form for Bit (grammar + `op_sim` cases), then rerun the same benchmark; a verified translator; a second transformation with memory bounds.

## Files

- `gen.py`, `ir/*.json`: emitter and IR inputs; `kernel.bend`: evaluator plus `sad`/`ssd`/`hamd`/`posd`.
- `variants/{pos,wrap,buf,l1,l2,ham,osl}/`: emitted C, prog.bend, Bend proofs. `red/`, `controls/`: mutants.
- `bendlink/`: trusted translator, pinned `base.bend`. `bridge/`: Lean checker, proofs, `Audit.lean`.
- `native/test.c`; `run_i8red5.sh`; `bench/` (plan, hand-written C, harness, runner, analysis, records).
- `README_i8red.md`, `run_i8red.sh`: the three-kernel milestone text and runner, kept for comparison.
