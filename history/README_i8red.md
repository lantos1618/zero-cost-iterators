# i8red: one gate, one shared proof, three scalar signed-INT8 reductions

Private milestone, standalone copy of r5 at `~/i8red`. r5 (`i8dot-bend-r5.tar.gz`, sha256 `a6bec014…`), the
SIFT10K replay v2 (`1ddc9293…`), Zen and every earlier directory/archive are untouched (archive sha256s
re-checked; a fresh extract of the r5 archive is identical to `~/i8dot-bend-r5`).

Replay: `./run_i8red.sh` -> `results_i8red/*.txt` (raw output + `exit=`), console log `EVIDENCE_i8red.txt`.
Last run: **TOTAL=64 UNEXPECTED=0**.
Toolchain: bend 2.0.40, Lean `leanprover/lean4:v4.15.0` (core only), gcc 11.4.0, clang 14.0.0, x86-64 Linux.

## 1. Per-operation numeric contract

Signature (all three): `int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out)`.
Caller assumptions: `a`, `b` each readable for `n` elements (equal readable prefixes), `out` valid,
elements in [-128, 127]. Accumulator, registers and temporaries are explicit `int32_t`.

| reduction | loop body (IR) | emitted element C | element range | guard `I8DOT_MAX_N` | worst case N·M |
|---|---|---|---|---|---|
| exact dot | `LdA LdB Mul Acc` | `r0 = r0 * r1;` | [-16256, 16384] | 131071 | 2147467264 |
| L1 (sum of absolute differences) | `LdA LdB Sub Abs Acc` | `r0 = r0 - r1;` `if (r0 < 0) r0 = -r0;` | [0, 255] | 8421504 | 2147483520 |
| squared L2 | `LdA LdB Sub Sq Acc` | `r0 = r0 - r1;` `r0 = r0 * r0;` | [0, 65025] | 33025 | 2147450625 |

Common lines: `r0 = (int32_t)a[i];`, `r1 = (int32_t)b[i];`, `acc = acc + r0;`, then `*out = acc; return 0;`.
`n > guard` returns -1 with `*out` unchanged. INT32_MAX = 2147483647.
Guards are per reduction, not shared: one shared guard of 33025 would be simpler but would cap dot and L1
far below their proved limits. Each guard is the largest n with n·M ≤ INT32_MAX (`guard_tight`) and each M
is attained by admitted bytes (`elem_bound_attained`), so with this accumulator no larger guard is safe.
The gate requires the emitted `#define` to equal `bound p` for the parsed program.

## 2. What is machine-checked (Lean, `bridge/`)

One small grammar: IR ops `Sub`, `Abs`, `Sq` added beside r5's `LdA LdB Mul Acc Wrap StT LdT`; the C
subset gains `-e` (`neg`, faults on overflow) and `if (v < k) v = e;` (`ifLt`) and parses any
`#define I8DOT_MAX_N <digits>u`.

Shared proof (`Bridge/Proofs.lean`):
- `op_sim` (extended by 3 cases): each op's C fragment agrees with the IR op or faults.
- `op_total`, `body_total`: if every intermediate IR state has int32 registers (`BodyOK`), the C body does not fault and tracks the IR state.
- `structure Cert` = loop body, guard N, element bound M with N·M ≤ INT32_MAX, element function f, and a per-element `step` fact.
- `cert_loop`: **the single induction** for all certified exact reductions. After i iterations the accumulator lies in [-i·M, i·M]; for n ≤ N the C loop never faults.
- `cert_total`, `cert_gate`: for any certificate, the rendered file returns -1 with `*out` unchanged when n > N. Otherwise it returns 0 with `*out` = Σ f(aᵢ, bᵢ) over the first n elements.
- Per kernel, only primitive semantics + bounds: `certDot`, `certL1`, `certL2` (using `prod_bound`, `sq_bound`), and `refRed_dot/l1/l2` tying Σ f to the independent references `refDot`, `refL1`, `refL2`.
- `exact_gate_sound` (**main theorem**). Premise: PASS of `Check.gate … true`, the same function `i8check exact` runs on the actual file bytes. Conclusion:
  - prog.bend's term is posIR, l1IR or l2IR;
  - on every admitted input the C semantics returns -1 with `*out` unchanged when n > `bound p`;
  - otherwise it returns 0 with `*out` = `refOf p` (dot / L1 / squared L2) of the first n elements, with no fault.
- `exact_gate_zero`: n = 0 gives return 0 and `*out = 0`.
- `gate_total`: one public theorem for both gates over the 4 certified programs (wrap keeps r5's proof `cRun_wrap`).
- `recovered_shape` now pins `f.dirs = dirsFor (bound p)`: every accepted file carries its own proved guard.
- `exact_gate_requires_exact`, `exactCert_wrap`: the exact gate never passes wrap.
- `gate_requires_certified`: the gate never passes an uncertified program.
- `bound_values`, `guard_tight`, `elem_bound_attained`.

Casts and evaluation order: the C subset reads `int8_t` → `int32_t` (always in range), evaluates
statements in file order, and faults on any out-of-range signed result or `-INT32_MIN`. The proofs show
no fault occurs on admitted inputs.

Bend link (`Bridge/BendLink.lean`, over the trusted mechanical translation of the actual `kernel.bend` and
`variants/{pos,wrap,buf,l1,l2}/prog.bend`):
- `zsub_v`, `zabs_v`: decoding Z{p,n} as p−n turns the translated `zsub`/`zabs` into `-` and the IR's abs.
- `exec_v` / `run_v` extended to the new ops: whole-state correspondence for every program and input.
- `prog_l1_v`, `prog_l2_v`: the translated terms decode to l1IR / l2IR (definitional).
- `sad_v`, `ssd_v`, `bend_l1_eq_sad`, `bend_l2_eq_ssd`: the translated evaluator on the actual l1/l2 terms equals Bend's independent references `sad`/`ssd`.
- `gate_total_bend` and `exact_gate_bend`: PASS ⇒ C result = p−n of `K.acc_of(K.run(q, xs, ys))` for the translated actual prog.bend term q.

Audit: `bridge/Audit.lean` is generated from every `theorem` in both proof files. It has 100 entries, all using only
`propext`, `Classical.choice` or `Quot.sound` (20 use none). No `sorry`/`admit`/`native_decide`/`axiom`.

## 3. Bend checks (separate checker, `--verdict`)

- `variants/l1/PROOF_RED.bend`, `variants/l2/PROOF_RED.bend` import the actual `kernel.bend` and `prog.bend`.
- They prove, for all inputs, that the evaluator's loop equals `sad`/`ssd` and that `run(prog)` equals `sad`/`ssd` from zero.
- Verdict: `ALL PROOFS CHECK`, exit 0. r5's pos `PROOF.bend` is also rerun: exit 0.

## 4. Gate replay on actual emitted files

Exit codes: 0 PASS, 2 C REJECT, 3 IR MISMATCH, 4 Bend REJECT, 5 UNCERTIFIED.

| run | exit | reason |
|---|---|---|
| dot / L1 / L2, exact and match, own prog.bend | 0 | PASS |
| wrap exact / match (own prog.bend) | 3 / 0 | not an exact reduction / certified total |
| r5 buf (product buffer) | 2 | `#include <stdlib.h>` outside subset |
| L2 with a differences/squares buffer (gen.py, `alloc` + `StT`/`LdT`) | 2 | same |
| L2 emitted with guard 131071 (exact and match) | 2 | `#define` must equal certified bound 33025 |
| L2 with the guard line deleted | 2 | statement 0: expected the guard |
| L1 arithmetic mutant `if (r0 > 0) r0 = -r0;` | 2 | line outside grammar |
| L1 without `Abs` (in-grammar, gen.py): exact own / match own / vs l1 prog | 3 / 5 / 3 | not exact; uncertified; mismatch |
| L1 C vs L2 prog, L2 C vs L1 prog, dot C vs L2 prog | 3 | IR mismatch |
| L2 prog.bend with renamed `prog` def | 4 | not the exact generated file |
| r4 overflow program (match) | 5 | uncertified |

The emitted files are regenerated by `gen.py` and compared byte for byte with the committed ones. The pos C file is byte-identical to r5's.

## 5. Negative control on the evaluator

`zsub` in `kernel.bend` is changed from a−b to a+b.
- Bend `PROOF_RED.bend` for l1 **still passes** (exit 0): `sad` and the evaluator share `zsub`, so the Bend law cannot see the change.
- The regenerated Lean differs (exit 1), and `Bridge/BendLink.lean` fails to build (exit 1, in `zsub_v`).

So the mutated subtraction is caught only by regenerating the Lean translation and rebuilding the Lean link
(`zsub_v` no longer proves a−b), even though the Bend L1 law, whose reference `sad` shares the mutated
`zsub`, still passes. This mirrors r5's `w8.nat` control.

## 6. Finite native tests (evidence, not proof)

`native/test.c` checks each emitted kernel against an independent `int64_t` reference:
- n = 0, 1, 2, N−1, N, N+1, N+2 for all four constant extreme array pairs (−128/127);
- deterministic xorshift data at fixed lengths including N−1, N, N+1;
- 2000 random lengths and offsets.

Over-limit calls must return −1 and leave `*out` unchanged. Builds: gcc -O2, gcc -O3 -march=native, clang -O3, and gcc/clang -O1 with
`-fsanitize=undefined -fno-sanitize-recover=all`. 3 kernels × 5 builds × 2045 calls: **0 failures, no
UBSan report**. The guard-boundary sums at n = N reach 2147467264 / 2147483520 / 2147450625. None of the three objects has an undefined (imported) symbol, so no allocator. No timing was run;
SIFT10K was not reused here (its published Euclidean rankings would only apply to squared L2).

## 7. Trusted boundary (unchanged in kind from r5)

| link | status |
|---|---|
| gate PASS ⇒ C-subset result = IR result = exact reference, all admitted inputs | machine-checked (Lean) |
| IR semantics = translated actual Bend evaluator (incl. Sub/Abs/Sq) | machine-checked on the translation |
| `bend2lean.py` construct mapping. Its Op whitelist was extended by `Sub`, `Abs`, `Sq` (one line) | **trusted** (regenerated + byte-compared) |
| gate's prog.bend parser vs translator's parser | tied by definitional equality on committed terms + replay, not proved |
| Bend laws (`PROOF_RED.bend`) | checked by Bend, not imported into Lean |
| C-subset fidelity to ISO C (incl. `-x`, `<` comparisons, int8→int32 conversion) | **trusted** |
| headers, no `-D` flags, ABI, C compiler, machine code | **trusted**; native runs are finite evidence |
| Lean/Bend compilers and runtimes, `i8check` binary | **trusted** |

## 8. What this does and does not do toward the reviewer targets

- **Rigor (verified translator + native allocation checks).** The translator is still trusted. Allocation is checked by undefined-symbol inspection and by the gate rejecting any `stdlib.h`/buffer program. Not done: a verified translator.
- **Utility (≥ 5 kernels, one checker, no per-kernel proof edits, within 5% of handwritten).** 3 kernels share one checker and one induction. Each new kernel still needs a small certificate (element semantics + bound) and a `bound` table entry. Not done: 5 kernels, speed measurements.
- **Novelty (semantics + memory bounds across two structurally different transformations).** Only one transformation shape (scalar fused load–element–accumulate loop). Not done: SIMD, tiling.

This is **not** a shape-agnostic validator. The gate accepts exactly the canonical rendering of four
certified IR programs and nothing else.

## 9. Learned vs proposed

- **Learned:** one parametric induction (`cert_loop`) covers all three reductions. Adding a kernel needed only primitive op cases, a bound lemma and a certificate.
- **Learned:** the per-reduction guard is necessary. The L2 file with r5's 131071 guard is rejected, and 131071 · 65025 overflows int32.
- **Learned:** a Bend law that relates two definitions sharing a primitive (`zsub`) cannot detect a change to that primitive. The Lean link to the decoded integer semantics does.
- **Proposed next:** two more kernels via certificates only; a verified or proof-producing translator; a timing study against handwritten C; a second transformation (vectorized or tiled) with memory bounds.

## Files

- `gen.py`, `ir/*.json`: emitter and IR inputs.
- `kernel.bend`: actual evaluator plus `sad`/`ssd` references.
- `variants/{pos,wrap,buf,l1,l2}/`: emitted C, prog.bend, Bend proofs.
- `red/`, `controls/`: mutants and controls.
- `bendlink/`: trusted translator and pinned `base.bend`.
- `bridge/`: Lean checker and proofs, `Audit.lean`.
- `native/test.c`: native differential test.
- `run_i8red.sh`, `results_i8red/`, `EVIDENCE_i8red.txt`: replay script and raw results.
- r5's `run_all.sh`, `check_c.py` and README remain as r5 comparison material.
