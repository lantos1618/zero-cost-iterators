# i8red7: a fluent `.loop()` front door that generates all five fused signed-INT8 kernels

```lean
def dot : Reduced := BytePairs.loop multiply |>.loop sum
def l1  : Reduced := BytePairs.loop subtract |>.loop abs |>.loop sum
def l2  : Reduced := BytePairs.loop subtract |>.loop square |>.loop sum
def ham : Reduced := BytePairs.loop subtract |>.loop nonzero |>.loop sum
def osl : Reduced := BytePairs.loop subtract |>.loop clampNeg |>.loop sum
```

These are the real calls in `bridge/Pipe/Chains.lean`. In Lean, `x.loop s` is a method call, and
`|>.loop s` chains the next call onto the previous result. So `BytePairs.loop subtract |>.loop abs |>.loop sum` is
Lean's spelling of `BytePairs.loop(subtract).loop(abs).loop(sum)`.

`pipegen` lowers the `l1` chain to one loop. It emits `gen7/l1/i8dot.c` (shown below) plus the matching `gen7/l1/prog.bend`:

```c
/* emitted by pipegen from chain l1 -- do not edit */
#include <stddef.h>
#include <stdint.h>
#define I8DOT_MAX_N 8421504u

int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {
  if (n > I8DOT_MAX_N) return -1;
  int32_t acc = 0;
  int32_t r0 = 0;
  int32_t r1 = 0;
  for (size_t i = 0; i < n; i++) {
    r0 = (int32_t)a[i];
    r1 = (int32_t)b[i];
    r0 = r0 - r1;
    r0 = r0 < 0 ? -r0 : r0;
    acc = acc + r0;
  }
  *out = acc;
  return 0;
}
```

The guard `8421504` is derived from the chain's stage bounds: `subtract` gives [-255, 255], `abs` gives [0, 255], and
2147483647 / 255 = 8421504. The existing checker then re-checks it against its proved tight bound.

## Verdict

- **Clean replay:** run in a fresh copy with no `.lake` output or old records. `run_i8red7.sh` exited 0 with
  `TOTAL=268 UNEXPECTED=0`.
- **Proofs:** 162 theorems audited, with only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
  There is no `sorry`, `admit`, `native_decide` or `axiom`.
- **Actual Bend verifier:** `ALL PROOFS CHECK` for all five generated `prog.bend` files, plus the renamed one.
- **Benchmark:** the 5% target is **met**. Under the primary configuration fixed before timing (gcc 11.4 `-O3`), all five kernels
  pass in both link layouts in run 1 (the result of record) and in run 2 (identical protocol).
  - gcc `-O3` ratios: 0.9909–1.0083 in run 1 and 0.9941–1.0105 in run 2.
  - The other three configurations also pass every cell. Over all 40 cells, ratios were 0.9909–1.0083 in run 1
    and 0.9801–1.0311 in run 2.

## Replay

```sh
bash run_i8red7.sh | tee REPLAY.txt          # generation, Bend, Lean build + audit, gate, all controls, native tests
bench/run_bench7.sh --dataset PATH/siftsmall.tgz --rounds 31 --cpu 2 --out bench/results_runN
bridge/.lake/build/bin/pipegen OUTDIR         # just the .loop() generation (writes OUTDIR/<chain>/{i8dot.c,prog.bend})
```

Requirements:
- Bend 2.0.40 at `~/.bend/bin/bend`;
- elan with Lean `v4.15.0`;
- gcc 11.4 and clang 14;
- python3;
- about 5 GiB RAM, for the full Hamming edge test.

The dataset is pinned to sha256 `df5907f8…7a93`, and the bench refuses any other.

## What the front door is

**Stage domain (explicit, closed).** The "functions" are stage descriptions, not arbitrary callbacks:
- zip stages `multiply` and `subtract`, which turn a pair of signed bytes into an element;
- map stages `abs`, `square`, `nonzero` and `clampNeg`, from element to element;
- the terminal reduction `sum`.

A lambda is rejected by typing (`ty_unsupported_callback`).

**Typing enforces composition order.** The order comes from `Pairs.loop`, `Elems.loop` and the `LoopStage` instances:
- `BytePairs` accepts only a zip stage;
- elements accept map stages or `sum`;
- a reduced chain has no `.loop`, so nothing can follow `sum`;
- the generator accepts only a reduced chain.

These ill-typed chains do not elaborate (Lean exit 1):
- missing zip;
- map before zip;
- missing terminal;
- stage after terminal;
- two zips;
- terminal first;
- double terminal;
- callback.

**Independent source meaning (`Reduced.den`).** It is ordered staged list semantics:
1. `List.zip a b` mapped by the zip function;
2. then each map stage as a separate whole-list `List.map`, in the order given;
3. then a left fold `foldl (+) 0`.

Abs is defined with `Int.natAbs` and clamp with `max v 0`, independently of the IR's `if` forms.

**Lowering (`lower`).** It walks the stages in order:
- `[LdA, LdB, zip.op] ++ maps.map op ++ [Acc]`, as one `Loop`;
- with `abs ↦ AbsT`, `nonzero ↦ Ne0`, `clampNeg ↦ Pos`, `square ↦ Sq`, `multiply ↦ Mul` and `subtract ↦ Sub`.

It never looks at a chain's name and never reads `ir/*.json` or the old IR constants. The replay checks this with a
grep (`generation_reads_no_old_IR`), and the renamed chain `qz7` (built from the aliases `minus` and `magnitude`)
produces the same loop as `l1`.

**Emission (`Pipe/Emit.lean`).** It is a trusted text printer:
- Each loop line is the checker-grammar line whose parse is exactly the op's rendered C statement.
- The guard is the stage-bound derivation (`Reduced.guard`).
- The Bend term is `BendP.showProg (lower r)`.

## Theorem chain (user chain → lowered loop → verified actual files)

| theorem | file | statement |
|---|---|---|
| `Pipe.fusion` | Pipe/Core.lean | for every chain `r` and all `Int` lists: `(IR.run (lower r) xs ys).acc = r.den xs ys` (staged zip/map/fold = one fused loop, same left-to-right order) |
| `Pipe.lower_fused` | Pipe/Core.lean | `lower r` is one `Loop`; its body uses only `LdA LdB Mul Sub AbsT Sq Ne0 Pos Acc`; no `Alloc`, `StT`, `LdT` or `Wrap` |
| `GenLink.chain_run_nobuf` | Pipe/GenLink.lean | buffer counter `mats = 0` for every lowered chain |
| `Pipe.chain_gate_sound` | Pipe/Core.lean | if the exact gate passes C bytes `cs` and Bend bytes `bs` with term `lower r`, then for every admitted input the parsed C returns −1 for `n > bound`, else returns 0 with `*out = r.den (a.take n) (b.take n)`; it reuses `exact_gate_sound` → `gate_total` → `cert_gate` → `cert_total` → `cert_loop` |
| `Facts.lower_{dot,l1,l2,ham,osl}` | Pipe/Facts.lean | the five chains lower to `posIR`, `l1IR`, `l2IR`, `hamIR` and `oslIR` (`rfl`); `lower_qz7 : lower qz7 = lower l1` |
| `Facts.guard_*` | Pipe/Facts.lean | the derived guard equals the checker's `bound` for each of the five (`decide`) |
| `Facts.den_*` | Pipe/Facts.lean | each chain's meaning equals the independent reference (`refDot`, `refL1`, `refL2`, `refHam`, `refOsl`) for all `Int` lists |
| `GenLink.bend_chain`, `bend_chain_nobuf` | Pipe/GenLink.lean | any translated Bend term decoding to `lower r` computes `r.den` with `mats = 0` |
| `GenLink.gen_*_term`, `gen_*_den` | Pipe/GenLink.lean | the actual generated `gen7/*/prog.bend`, translated to `BK.P_g*.prog`, decodes to `lower <chain>` and computes `<chain>.den` |
| `GenLink.gen_same_terms` | Pipe/GenLink.lean | those translated terms equal the i8red6 terms (`rfl`) |

The C file is tied to the chain at runtime: `pipegen` runs the gate in process and requires `.pass p` with
`p = lower r`, and `i8check exact` then re-runs the gate on the written files. `chain_gate_sound` is the theorem that
gives the C meaning from that pass.

## Controls (all asserted by `run_i8red7.sh`)

**Valid chains that change the program.** A well-typed edit can compile to a different, legitimate operation, so this
is not a corruption.

| edited chain | lowered body | exact / match exit | intended-kernel contract |
|---|---|---|---|
| `l1` with abs dropped | Sub | 2 / 2: derived guard 8421504 ≠ checker bound 131071 | FAIL |
| `l1` with abs replaced by square | Sub Sq (= squared L2) | 0 / 0: a valid squared-L2 kernel; against the L1 `prog.bend`: 3 | FAIL (`l1_abs_to_sq_differs`) |
| `l1` plus a square stage | Sub AbsT Sq | 2 / 2 | FAIL |
| `dot` with subtract as zip | Sub | 2 / 2 | FAIL |
| `dot` plus an abs stage | Mul AbsT | 3 / 5 (uncertified); against the dot `prog.bend`: 3 | FAIL |
| `ham` with abs before nonzero | Sub AbsT Ne0 | 2 / 2 | OK: same meaning (`ham_swap_same_meaning`), but an uncertified program, rejected conservatively |
| `ham` with multiply as zip | Mul Ne0 | 2 / 2 | FAIL |
| `osl` with clamp replaced by abs | Sub AbsT (= L1) | 0 / 0: a valid L1 kernel; against the one-sided L1 `prog.bend`: 3 | FAIL (`osl_to_abs_differs`) |
| `osl` with clamp twice | Sub Pos Pos | 2 / 2 | OK, but uncertified, rejected |
| `l2` with multiply as zip | Mul Sq | 2 / 2 (derived guard 7) | FAIL |

**Other new rows.**
- Generated L1 C against generated squared L2 Bend, and generated Hamming C against generated one-sided L1 Bend: exit 3.
- Tampered generated Bend: exit 4.

**Kept from i8red6.** All earlier rows, unchanged and with the same expected codes:
- arithmetic, sign-flip and inverted-ternary mutants;
- wrong or missing guards;
- buffer forms;
- C/Bend swaps and tampered Bend;
- retired spellings;
- the four Bend evaluator mutations that pass Bend's own law but fail the rebuilt Lean link.

## Byte comparison with i8red6

Each generated `gen7/{dot,l1,l2,ham,osl}` file (`i8dot.c` and `prog.bend`) equals i8red6's `variants/{pos,l1,l2,ham,osl}` file
**except one provenance comment line**: line 1 of the C, line 4 of the Bend. The replay checks every other byte
and also that exactly that one line differs. `qz7` equals `l1` in the same way.

The emitted programs are therefore the same. What changed is where they come from: the `.loop()` chains instead
of `ir/*.json` plus `gen.py`.

The gcc and clang normalized assembly of every generated object is byte-identical to i8red6's (20 of 20 listings).

## Benchmark (pinned centered SIFT10K, 1,000,000 n=128 pairs per kernel per trial)

**Protocol.** `bench/PLAN_bench7.md` was written before timing and is the i8red6 protocol unchanged:
- the same `hand_*.c`, `bench.c`, ABI, guards and flags;
- separate translation units, no LTO;
- `taskset -c 2`, 31 rotated rounds, layouts A (generated first) and B (hand-written first).

**Fail-closed checks before compiling:**
- regenerate with `pipegen` and require byte equality with `gen7/`;
- check `gen7/SHA256SUMS`;
- run `i8check exact` on each compiled pair;
- hash every compiled source, and re-check after timing (all OK in both runs).

**Host:** `host.txt` is byte-identical to i8red6's: Intel Xeon on AWS, 8 CPUs, Linux 6.8, gcc 11.4.0, clang 14.0.0, no governor exposed.

**Primary: gcc `-O3`**. Each cell is the generated median over the hand-written median, in ms, with the ratio.

| kernel | run 1 A | run 1 B | run 2 A | run 2 B |
|---|---|---|---|---|
| dot | 14.230/14.113 = 1.0083 | 13.787/13.913 = 0.9909 | 14.138/13.991 = 1.0105 | 13.861/13.924 = 0.9955 |
| L1 | 16.914/16.856 = 1.0034 | 16.636/16.665 = 0.9983 | 16.856/16.799 = 1.0034 | 16.652/16.637 = 1.0010 |
| squared L2 | 9.348/9.347 = 1.0001 | 9.050/9.052 = 0.9999 | 9.246/9.302 = 0.9941 | 9.021/9.036 = 0.9983 |
| Hamming | 9.372/9.382 = 0.9990 | 9.040/9.011 = 1.0032 | 9.264/9.273 = 0.9991 | 9.034/9.008 = 1.0030 |
| one-sided L1 | 15.256/15.246 = 1.0006 | 14.962/14.985 = 0.9984 | 15.175/15.145 = 1.0020 | 14.932/14.936 = 0.9997 |

- **Verdict:** all five kernels pass in both layouts in both runs (10/10 cells per run).
- **Other configs:** gcc `-O3 -march=native`, clang `-O3` and clang `-O3 -march=native` also pass 10/10 cells in both runs.
  The run 2 extremes are both gcc `-O3 -march=native`: L1 layout B at 1.0311 and dot layout A at 0.9801.
- **Spread:**
  - gcc `-O3`: largest per-cell IQR 0.29 ms (run 1) and 0.25 ms (run 2).
  - All configs: largest IQR 1.76 ms (run 1, clang `-O3` L2 B) and 4.37 ms (run 2, clang `-O3` L2 A). The run 2 value
    comes from a burst of slow rounds; single-round maxima reach 55 ms and 84 ms.
- **Correctness:**
  - 0 mismatches against the int64 reference.
  - Checksums: dot 1339476007622, L1 4184838222, squared L2 299992732756, Hamming 117675068, one-sided L1 2058208211.
  - The `correct_*` output is byte-identical to i8red6's.
  - Squared L2 against the published rankings: top-1 100/100, top-10 100/100, tie-aware top-100 100/100,
    identical ordered top-100 id lists 91/100.
- **Assembly, generated vs hand-written:**
  - identical for L1, squared L2, Hamming and one-sided L1 under all four configs, and for dot under clang;
  - dot under gcc still differs only in the register allocation and order around the byte loads, with equal instruction counts (174/174 and 202/202), as in i8red6.

Raw records are in `bench/results_run{1,2}/`. i8red5 and i8red6 measurements are untouched in their own directories.

## What "zero cost" means here

In scope:
- **Proved.** Lowering a supported chain adds no intermediate collection, allocation, buffer store/load or wrap step.
  The staged meaning (each map a whole-list pass) equals one fused loop with the same left-to-right accumulation.
- **By construction.** There is no runtime adapter dispatch: stages are resolved during elaboration, and the C grammar
  contains no calls.
- **Checked.** No generated object has any undefined symbol, including allocator symbols.
- **Measured.** On this host, the generated C is within 5% of idiomatic hand-written C under all four configurations.

Not claimed:
- a cost bound for arbitrary callbacks or user-defined stages;
- a verified C compiler, vectorizer, assembly or timing guarantee;
- anything beyond this host and dataset.

## Trusted boundary

- **Emission:** `Pipe/Emit.lean` is a text printer, re-checked byte-for-byte by the exact gate, which is in turn covered by `chain_gate_sound`.
- **Derived guard:** an interval analysis, not trusted for safety. The gate requires it to equal the proved `bound`.
- **Translator:** `bend2lean.py` (Bend → Lean) remains trusted. The evaluator is proved equivalent after translation, and
  `GenLink` uses the translated generated files.
- **C model:** the restricted C subset's fidelity to ISO C (including `?:` and `!=`), headers, the ABI, gcc and clang, and the
  machine code.
- **Measurement:** the benchmark harness, `analyze.py` and the host.
- **Bend:** Bend's own checker, which is a separate checker.
- **Bend proof files:** the `PROOF*.bend` files in `gen7/` are copies of the per-kernel i8red6 Bend proof files. They are
  not generated by `pipegen`; they check the generated `prog.bend` against Bend's independent references.

## Toward the reviewer targets (targets, not achieved results)

- **Utility:** 5 useful kernels generated from user-facing chains by one generator and one checker, without
  per-kernel proof edits, and within 5% of hand-written C on a defined setup.
- **Rigor:** the translator is still unverified.
- **Novelty:** only one transformation (fusion) is covered; there is no second structural transformation such as
  vectorization or tiling.

Next steps:
- user-defined stages with proof obligations;
- a validator that does not depend on the loop shape;
- a verified or proof-producing translator;
- SIMD/tiling.
