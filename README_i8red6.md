# i8red6: certified ternary-L1 and `!=`-Hamming spellings; five signed-INT8 reductions vs hand-written C

Private milestone in `~/i8red6`, a copy of `~/i8red5`. `~/i8red5` (code, README and both timing runs),
`~/i8red`, r5 (`i8dot-bend-r5.tar.gz`, sha256 `a6bec014…`), SIFT10K replay v2 (`1ddc9293…`) and Zen are
untouched: both archive sha256s re-checked, and no file in those directories is newer than this session's
first edit.

**Verdict on the 5% target: MET.** Under the primary configuration fixed before timing (gcc 11.4 `-O3`,
both link layouts), all five kernels are within 5% of hand-written C in run 1 (the result of record) and
in run 2 (identical protocol): ratio 0.9885–1.0137 in run 1 and 0.9919–1.0067 in run 2 over all 40 cells
(4 configs × 2 layouts × 5 kernels). The i8red5 misses are fixed by the emitted spelling: with gcc, generated
and hand-written L1 and Hamming now compile to identical normalized machine code at both flag sets.

| item | where |
|---|---|
| correctness replay | `./run_i8red6.sh`; clean run in `~/i8red6-scratch` (no `.lake`, no records) -> `REPLAY_clean.txt` |
| benchmark plan (before timing) | `bench/PLAN_bench6.md` (points to the unchanged i8red5 `bench/PLAN_bench.md`) |
| benchmark records | `bench/results_run1/` (result of record), `bench/results_run2/` (reproducibility) |
| evidence log | `EVIDENCE_i8red6.txt` |

Host unchanged from i8red5 (`host.txt` byte-identical): AWS "Intel(R) Xeon(R) Processor", 8 vCPUs, 1 thread
per core, Linux 6.8.0-1060-aws x86-64, gcc 11.4.0, clang 14.0.0, `taskset -c 2`, governor not exposed.
Toolchain: bend 2.0.40, Lean 4.15.0.

## 1. What changed

Two new IR ops, each with one new C line; the old ops stay in the IR, grammar and proofs with their old meaning.

| op | IR meaning (`IR.exec`) | the one C line | used by |
|---|---|---|---|
| `AbsT` | `r0 := if r0 < 0 then -r0 else r0` | `r0 = r0 < 0 ? -r0 : r0;` | L1: `LdA LdB Sub AbsT Acc` |
| `Ne0` | `r0 := if r0 = 0 then 0 else 1` | `r0 = r0 != 0;` | Hamming: `LdA LdB Sub Ne0 Acc` |

- **C subset:** two new expression forms, `condLt c k t e` (`c < k ? t : e`, only the selected operand is
  evaluated, so `-r0` can only fault when `r0 < 0`) and `ne l r` (`l != r`, int 0 or 1). The parser accepts
  exactly the two lines above; nothing else about ternaries or `!=` is admitted.
- **Not silently equated.** `AbsT` and `Abs` are distinct ops; `absT_eq_abs` proves they have the same IR
  meaning on every state, but their C lines differ and the gate tells them apart. `Ne0` is not `Bit`:
  `ne0_eq_bit_abs` proves `Ne0 = Bit ∘ Abs` on every state, and `ne0_ne_bit` proves `Ne0 ≠ Bit` on
  `r0 = -1` (Bit leaves -1, Ne0 gives 1). The Hamming certificate uses `Ne0` directly:
  `f x y = if x - y = 0 then 0 else 1`, so a negative nonzero difference counts 1.
- **Retired spellings.** The i8red5 L1 (`if (r0 < 0) r0 = -r0;`) and Hamming (`Abs; Bit`) programs are no longer
  certified exact programs. Their files still parse, but their uncertified IR gets the default guard 131071,
  so they are rejected (exit 2).
- **Unchanged:** dot, squared L2 and one-sided L1 emitted C and prog.bend (byte-identical to i8red5), all guards,
  the hand-written baselines, the harness, the analysis script and the protocol.

## 2. Numeric contract (all five)

`int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out)`; `a`, `b` readable for `n` elements;
explicit `int32_t` registers and accumulator; `n > guard` returns -1 and leaves `*out` unchanged; `n = 0`
returns 0 with `*out = 0`.

| reduction | loop body | element range M | guard N | N·M |
|---|---|---|---|---|
| dot | `LdA LdB Mul Acc` | [-16256, 16384] | 131071 | 2147467264 |
| L1, sum of absolute differences | `LdA LdB Sub AbsT Acc` | [0, 255] | 8421504 | 2147483520 |
| squared L2 | `LdA LdB Sub Sq Acc` | [0, 65025] | 33025 | 2147450625 |
| Hamming, count of a[i] ≠ b[i] | `LdA LdB Sub Ne0 Acc` | [0, 1] | 2147483647 (exact) | 2147483647 |
| one-sided L1, sum of max(a[i]−b[i], 0) | `LdA LdB Sub Pos Acc` | [0, 255] | 8421504 | 2147483520 |

Each guard is the largest n that cannot overflow (`guard_tight`). Hamming keeps the exact guard: native tests use
1 MiB arrays in all builds plus one gcc -O2 run at n = N−1 and N on 2 GiB arrays, where n = N sums to INT32_MAX.

## 3. Proof (Lean, `bridge/`)

Same chain for all five, unchanged: `exact_gate_sound` → `gate_total` → `cert_gate` → `cert_total` →
`cert_loop` (the one induction). `gate_total` selects `certDot`, `certL1`, `certL2`, `certHam`, `certOsl`
(`Proofs.lean` lines 797–802). Per-op work added in this milestone:

- `op_sim`: two new cases. AbsT: the ternary faults only if `r0 < 0` and `-r0` overflows; otherwise the C state
  matches `IR.exec .AbsT`. Ne0: never faults; result `if r0 = 0 then 0 else 1`.
- `op_total`: one more closing alternative (case split on `r0 = 0`).
- `certL1`: ops now use `AbsT`; element function, bound and guard unchanged. `certHam`: ops `Sub, Ne0`, M = 1,
  N = 2147483647, `f = if x - y = 0 then 0 else 1`; `refRed_ham` links it to `refHam` (`if x = y then 0 else 1`).
- `absT_eq_abs`, `ne0_eq_bit_abs`, `ne0_ne_bit` as above.
- Bend link: `zne0_v` (the new Bend `zne0` = `if zv a = 0 then 0 else 1`), new `exec_v` cases, `hamd_v` now via
  `zne0`; `bend_l1_eq_sad`, `bend_ham_eq_hamd`, `exact_gate_bend` rebuilt unchanged in statement.
- Audit: 114 theorems (110 + 4), each printed by `Audit.lean`; the runner checks the count equals the number of
  `theorem` declarations. Axioms used: only `propext`, `Classical.choice`, `Quot.sound` (22 use none). No
  `sorry`/`admit`/`native_decide`/`axiom`.

## 4. Bend (actual `kernel.bend` + actual `prog.bend`)

- `kernel.bend` gains `AbsT{}` (evaluates with `zabs`), `Ne0{}` and `zne0`, written with two `Nat.is_le`
  selections (not via `zbit`/`zabs`). The reference `hamd` now adds `zne0(zsub(x, y))`.
- `--verdict`: `ALL PROOFS CHECK` for all five (`PROOF.bend`, four `PROOF_RED.bend`).
- `bend2lean.py` (trusted) whitelist gained `AbsT`, `Ne0`; regenerated `BendKernel.lean`/`BendProgs.lean` are
  byte-identical to the committed ones in the clean replay.
- Evaluator mutations: `zne0` (both branches 1) and `zabs` (both branches `n − p`) still pass the Bend laws, which
  share the primitive; the Lean link build fails (`BendLink.lean:131`, `:103`). `zsub`, `zpos` as before.

## 5. Clean replay (`~/i8red6-scratch`, `./run_i8red6.sh`): `TOTAL=155 UNEXPECTED=0`, `SCRIPT_EXIT=0`

Every row asserts its expected exit code (0 PASS, 2 grammar/guard reject, 3 IR mismatch, 4 Bend reject,
5 matching but uncertified). The 118 i8red5 checks are all retained. New i8red6 rows:

| control (C vs prog.bend) | want = got |
|---|---|
| L1 inverted `r0 < 0 ? r0 : -r0` / `r0 > 0 ? -r0 : r0` / `r0 <= 0 ? -r0 : r0` / `? -r0 : -r0` | 2 |
| L1 missing guard; guard 8421505 (exact and match) | 2 |
| Hamming `r0 == 0` / `r0 > 0` (sign-sensitive) / `r0 != 1`; missing guard; guard 2147483648 | 2 |
| L1 `AbsT` buffer; Hamming `Ne0` buffer (stdlib.h + temporary array) | 2 |
| Hamming `Sub; Bit` without Ne0 (sign-sensitive, in grammar): exact / match | 3 / 5 |
| Hamming without `Sub` (`a[i] != 0`): exact own / match own / vs Hamming prog.bend | 3 / 5 / 3 |
| retired i8red5 L1 and Hamming spellings: own (exact, match) / vs new prog.bend | 2 / 2 |
| new L1 / Hamming C vs retired prog.bend (`Abs` vs `AbsT`, chain vs `Ne0`) | 3 |
| Hamming C vs L1, dot, osl prog.bend; L1 C vs dot, Hamming, osl prog.bend | 3 |
| tampered L1 and Hamming prog.bend | 4 |
| evaluator mutation `zne0`, `zabs`: Bend law / Lean differs / link build | 0 / 1 / 1 |

Native differential tests (finite evidence): 5 kernels × 5 builds (gcc -O2, gcc -O3 -march=native, clang -O3,
gcc and clang -O1 UBSan) against an independent exact reference: n = 0, 1, 2, extreme byte pairs, N−1..N+2,
deterministic random; 0 failures, no UBSan report; plus the 2 GiB Hamming edge run. All five objects import no
symbols. The first replay attempt failed 8 rows on a path my script rename broke (`REPLAY_attempt1_badpath.txt`);
the clean replay above is after fixing the path only.

## 6. Benchmark

Protocol identical to i8red5 (`bench/PLAN_bench.md`, `bench/PLAN_bench6.md`): pinned SIFT10K
(`df5907f8…`, members pinned), centered x−128, 100 × 10,000 pairs at n = 128 = 1,000,000 calls per kernel per
trial; generated and hand-written in separate TUs, same ABI/guard/int32 contract/flags, same function-pointer
call; no LTO; 31 rounds with the 10 cells rotated; layouts A (generated objects first) and B (reversed);
per-trial checksums must match; loading, validation and the correctness pass are not timed.

**Gated bytes = compiled bytes.** Before compiling, `run_bench.sh` runs `i8check exact` on the same five
`variants/*/i8dot.c` + `prog.bend` it compiles (5 × PASS), records their sha256 and re-checks them after timing
(all OK in both runs). The hashes equal those in the clean replay.

Correctness (both runs, every config/layout identical): 0 mismatches vs int64 reference on 1,000,000 pairs per
kernel; checksums dot 1339476007622, L1 4184838222, squared L2 299992732756, Hamming 117675068,
one-sided L1 2058208211 (same as i8red5). Squared L2 vs published: top-1 and top-10 ordered 100/100, top-100
tie-aware distances 100/100, identical ordered top-100 ids under index tie-break 91/100.

### Primary gcc 11.4 -O3: median ms [IQR], ratio = generated / hand-written

| kernel | run 1 A | run 1 B | run 2 A | run 2 B | verdict |
|---|---|---|---|---|---|
| dot | 14.131 [0.81] / 13.940 [0.39] = 1.0137 | 14.168 / 14.333 = 0.9885 | 14.147 / 14.097 = 1.0036 | 14.078 / 14.193 = 0.9919 | PASS |
| L1 | 16.857 [0.89] / 16.896 [1.43] = 0.9977 | 16.934 / 17.006 = 0.9958 | 16.927 / 16.955 = 0.9983 | 16.901 / 16.903 = 0.9999 | PASS |
| squared L2 | 9.159 / 9.108 = 1.0055 | 9.479 / 9.471 = 1.0008 | 9.383 / 9.414 = 0.9967 | 9.273 / 9.285 = 0.9988 | PASS |
| Hamming | 9.159 / 9.101 = 1.0063 | 9.492 / 9.466 = 1.0027 | 9.430 / 9.396 = 1.0036 | 9.278 / 9.250 = 1.0030 | PASS |
| one-sided L1 | 15.065 / 15.022 = 1.0028 | 15.307 / 15.383 = 0.9951 | 15.228 / 15.183 = 1.0030 | 15.152 / 15.262 = 0.9928 | PASS |

All-five verdict: **MET** in run 1 and run 2 (10/10 cells each). No cell is a miss, so no "faster only" or
layout-sensitive flag applies. The other three configurations (gcc -O3 -march=native, clang -O3,
clang -O3 -march=native) are also 10/10 in both runs; all rows with IQR and min–max are in
`results_run*/summary.txt` and in the evidence log. Largest per-cell IQR: 1.43 ms in run 1 (gcc -O3, hand L1,
layout A) and 0.73 ms in run 2. Single outlier rounds reach 42 ms (run 1) and 77 ms (run 2); the medians absorb them.

Compared with i8red5 under gcc -O3: L1 went from 2.03–2.07× to 0.996–1.000×, Hamming from 5.21–5.41× to
1.003–1.006×. The hand-written medians are also somewhat lower than in i8red5 run 1 (e.g. hand L1 16.9 vs 18.6 ms,
hand Hamming 9.1 vs 10.0 ms) with byte-identical sources and host; i8red5 run 1 was the noisier run (IQR up to 6.9 ms).

### Code shape (normalized `objdump`, addresses masked)

| kernel | gcc -O3 | gcc -O3 -march=native | clang -O3 / -march=native |
|---|---|---|---|
| dot | same 174 instructions; byte-load destination registers swapped | same 202; same kind of register swaps | identical |
| L1, squared L2, Hamming, one-sided L1 | identical | identical | identical |

The dot listings are the same as in i8red5. In i8red5, gcc L1 and Hamming differed (32-bit lanes vs the
hand-written 16-bit and byte lanes); now they are identical. This is an observation about gcc 11.4/clang 14 on
these two spellings, not a verified vectorizer or a proof about machine code.

## 7. Trusted boundary

| link | status |
|---|---|
| gate PASS ⇒ C-subset result = IR result = exact reference, all admitted inputs and lengths | machine-checked (Lean) |
| IR semantics = translated actual Bend evaluator (incl. AbsT, Ne0, zne0) | machine-checked on the translation |
| `bend2lean.py`; its Op whitelist gained `AbsT`, `Ne0` | **trusted** (regenerated + byte-compared) |
| gate's prog.bend parser vs translator's parser | tied on committed terms + replay, not proved |
| Bend laws (`PROOF_RED.bend`) | checked by Bend, not imported into Lean |
| C-subset fidelity to ISO C, now incl. `?:` (selected operand only) and `!=` (int 0/1) | **trusted** |
| headers, flags, ABI, compilers, machine code | **trusted**; native tests and benchmark are finite evidence |
| harness, centering, checksums, ranking check, analysis | **trusted** test code |
| Lean/Bend toolchains, `i8check` binary | **trusted** |

Not a shape-agnostic validator: the gate accepts exactly the canonical renderings of six certified IR programs.

## 8. Toward the reviewer targets

- **Utility:** five kernels, one checker, one induction, and the pre-declared ≤5% target met on the defined
  setup (one host, gcc 11.4 and clang 14, SIFT10K at n = 128, scalar source). Each new spelling cost one IR op,
  one C line, one `op_sim` case and certificate edits; no new induction.
- **Rigor:** translator still trusted; allocation checked by imports, the gate's `stdlib.h` rejection and buffer controls.
- **Novelty:** unchanged; one transformation shape, no SIMD/tiling certification.

## Files

- `gen.py`, `ir/*.json`, `kernel.bend`, `variants/*/`, `red/`, `controls/` (new: `l1t_*`, `ham_eq`, `ham_gt`,
  `ham_ne1`, `ham_noguard`, `l1t_noguard`, `ham_nosub`, `l1_retired`, `ham_retired`), `bendlink/`, `bridge/`,
  `native/test.c`, `run_i8red6.sh`, `bench/`. Earlier READMEs and runners are kept for comparison.
