# i8dot-bend r5: an exact, buffer-free signed INT8 dot product with Bend laws, a machine-checked total C↔IR acceptance bridge, and an all-input link to the actual Bend evaluator

## 0. In plain terms

A dot product of two byte vectors `a`, `b` is built from these pieces:

| term | meaning here |
|---|---|
| **zip** | pair the inputs element by element: `(a[0],b[0]), (a[1],b[1]), …` (the C kernel reads the first `n` of each; only the Bend model truncates unequal lists) |
| **map** | apply a function to each pair: here multiply, `a[i]*b[i]` |
| **fold / reduce** | combine the results left to right into one value: here sum, starting from 0 |
| **fusion** | run zip, map and fold inside **one loop**, so no list of pairs or products is ever stored |

The three forms in this artifact:

| form | what it computes | intermediate array? | how it is checked |
|---|---|---|---|
| staged reference / temporary-products (`buf`) | exact sum: first loop writes every product into `t[]`, second loop sums `t[]` | **yes** (`malloc`, `t[i]` writes/reads; IR `Alloc`/`StT`, `mats = 2` on `[1]·[1]`) | Bend refutes the no-buffer law at `[1]·[1]`; Python baseline says BUFFER; `i8check` REJECT (outside the subset); same exact value only on finite witnesses/native runs |
| one-loop exact form (`pos`) | exact integer \(\sum_{i<n} a_i b_i\) in an `int32_t` accumulator (no overflow for \(n \le 131071\)) | no | Bend LAW 1 + LAW 2 (`--verdict`); Lean `gate_total` / `exact_gate_bend_pos` from `i8check exact` PASS; r5 link to the translated Bend evaluator; native differential runs |
| wrapping negative control (`wrap`) | one loop, but the accumulator is reduced to signed 8 bits after each step: `[12]·[11]` gives −124, not 132 | no | Bend refutes LAW 1 at `[12]·[11]` and proves LAW 2; `i8check exact` = MISMATCH; `i8check match` = PASS with `gate_total` = the wrap IR result; native runs show the wrong value |

**r5 (link to the actual Bend evaluator, this revision).** r4's `gate_total` was stated against `IR.run`, a hand
transcription of the Bend evaluator. In r5, `bendlink/bend2lean.py` **mechanically translates** the actual
`kernel.bend`, the exact generated `variants/*/prog.bend` files, and a fixed whitelist of `Nat`/`Cmp`/`Pair`
definitions from the **pinned** `base.bend` into Lean (`Bridge/BendKernel.lean`, `Bridge/BendProgs.lean`). It is a narrow, fail-closed, syntax-directed translator; that bend 2.0.40 opens exactly this `base.bend` was observed with `strace`.

`Bridge/BendLink.lean` then proves, for **all inputs**:
* the translated `Nat.add/sub/mul/mod/is_lt/is_eq/is_le` equal Lean's;
* \(Z\{p,n\} \mapsto p-n\) turns `zadd`/`zmul`/`wrap8` into `+`/`*`/`IR.wrap8`;
* decoding the translated `K.run` gives `IR.run`, as **full state correspondence** for every program: registers, accumulator, `mats`, buffer contents (`run_v`).

So `gate_total_bend` restates the public guarantee directly in terms of `zv (K.acc_of (K.run q xs ys))` of the translated actual evaluator. Lean also re-proves Bend LAW 1 (as structural `Z` equality) and LAW 2 on the translation.

`run_all.sh` regenerates the translation and byte-compares it with the committed Lean. A deliberate evaluator change (`w8.nat`: `128n` → `127n`) **passes** Bend's pos `PROOF`, wrap `REFUTE` and wrap `NOBUF` under `--verdict`. But it changes the regenerated Lean, and the link proofs then fail to build. What remains trusted is the translator and its construct mapping (§3c), not a hand-written evaluator.

**r4 (total public guarantee).**

**r4 (total public guarantee, this revision).** A reviewer generated
`{"loop":["LdA","LdB","Mul","Mul","Mul","Mul","Acc"]}` with the shipped `gen.py`. r3's `i8check match`
said PASS, yet the Lean C semantics faults on an admitted input. That was sound under r3's partial
theorem, but PASS did not mean "same result".

r4 makes PASS total:
* The match gate now passes only **certified** programs, `posIR` and `wrapIR`, whose no-fault proofs exist.
* A program that matches its prog.bend but is not certified gets a distinct verdict, **UNCERTIFIED (exit 5)**.
* The exact gate is still restricted to `posIR`.
* One public theorem, **`gate_total`**, takes PASS of the same executable `Check.gate` as its premise. It guarantees the IR result on every admitted in-range input, and `-1` with `*out` unchanged when `n > 131071`.
* The general conditional simulation stays as an internal theorem (`sound_render`, `gate_pass_conditional_sim`).
* The overflow program is now a generated control (`ir/overflow.json` → `checker_tests/overflow/`). It is never compiled or run natively, since it would be signed-overflow UB.
* `Audit.lean` is now generated from every `theorem` in `Proofs.lean`. It includes `Ag.bind` and `drop_take_len`, which r3's hand list missed.

r3 is unchanged in `~/i8dot-bend-r3` and its archive.

**r3 (machine-checked acceptance bridge).**

This is a private, standalone research note. It is not tied to any language or compiler, and nothing was pushed or published.
The question: can one scalar kernel be shown, with checked laws, to (1) compute the **exact integer**
dot product of two signed byte vectors and (2) **never materialize an intermediate buffer**? And can
both facts be tied to the actual emitted C rather than to a declared flag?

**r3 (machine-checked acceptance bridge, this revision).** The authoritative checker is now
`bridge/.lake/build/bin/i8check`, compiled from Lean 4.15.0 (core only). It reads the actual `.c` and
`prog.bend` file bytes. Lean theorems take that **same function's** PASS verdict (`Check.gate cs bs ex = .pass p`)
as the premise. They recover the concrete C program and prove that its execution, in an independently
written semantics of the C subset, equals the IR program parsed from the exact `prog.bend` that
`bend --verdict` checks. For the exact gate the result is the exact integer dot product, with no
fault on any admitted input (§3b). The early-store and early-return regressions are rejected; no theorem
premise mentions them, but `recovered_shape` makes them impossible. The r2 Python validator is kept as an
**unproved baseline** and regression fixture. Bend, kernel, emitter, Lean safety and emitted C files are
byte-identical to r2.

**r2 (bridge fix).** The r1 validator matched each C statement against a template but never
checked order or scope. A reviewer moved the single `*out = acc;` line before the loop: r1 still
lifted the right IR and said PASS, while native `[12]·[11]` returned 0 instead of 132. r2 replaces it
with a complete, ordered, fail-closed grammar over the whole file (§3). The new early-store,
early-return, missing-guard, trailing-statement and line-splice controls are all rejected (§5).
`run_all.sh` now asserts the expected exit code of every run and takes `BEND=...`. Nothing else changed:
the Bend, Lean and emitter files and the three emitted C files are byte-identical to r1.

## 1. What is fixed

| item | value |
|---|---|
| Bend | `bend 2.0.40` at `~/.bend/bin/bend`. The binary sha256 and the cached `bendtt` kernel path are in `EVIDENCE.txt` |
| Lean | `leanprover/lean4:v4.15.0`, core only: `lean/lean-toolchain` (safety lemma) and `bridge/lean-toolchain` (r3 checker + bridge theorems, `lake build`) |
| C compilers | gcc 11.4.0, Ubuntu clang 14.0.0, x86-64 Linux |
| C data model assumed | `int8_t` inputs, `int32_t` scalars `acc`, `r0`, `r1`; `int` is 32-bit (so `int32_t*int32_t` is `int` arithmetic) |
| kernel | `int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out)`; both arrays have `n` readable elements; returns -1 if `n > 131071` |

## 2. Laws (exact statements, `LAWS.bend`)

```
law exact:                       # LAW 1, exact integer sum
  for xs: K.Zs
  for ys: K.Zs
  {K.acc_of(K.run(P.prog(), xs, ys)) == K.dot(xs, ys, K.z0()) : K.Z}

law nobuf:                       # LAW 2, zero intermediate materialization
  for xs: K.Zs
  for ys: K.Zs
  {K.mats_of(K.run(P.prog(), xs, ys)) == 0n : Nat}
```

* **Integers.** `K.Z{p, n}` stands for the mathematical integer `p - n`, with unbounded `Nat` parts, so there is
  no width at all. The laws use equality of these pairs, which implies equality of the integers.
  The representation is not canonical: the buffer mutant's −19 comes out as `Z{7, 26}`.
* **Reference.** `K.dot` (`kernel.bend`) is the independent reference: an exact left-to-right sum of
  `zmul(x, y)`. It knows nothing about the IR.
* **IR.** `K.run` is an **executable** evaluator for a small lowered IR:
  * `Op = LdA | LdB | Mul | Acc | Wrap | StT | LdT`;
  * `Stmt = Alloc | Loop(Ops)`;
  * state `St{r0, r1, acc, mats, tout}`.
  `LdA`/`LdB` read `a[i]`/`b[i]`. `StT` appends `r0` to the buffer `tout`. `LdT` reads `tin[i]`, the buffer written by the previous loop. `Alloc` allocates. `mats` counts executed `Alloc` and `StT` operations.
  So **the buffer operations are real IR operations that change the evaluator's state**. A program that writes and reads a buffer computes through it, and `mats` counts those operations; it is not a declared flag.
* **Lengths.** Only the Bend model handles unequal lists: `K.run` and `K.dot` stop at the shorter one.
  The C kernel never sees list lengths. Its contract is that the caller supplies `n` and that **both** `a` and `b`
  have at least `n` readable elements; it reads exactly `a[0..n)` and `b[0..n)`. The bridge therefore
  covers equal-length inputs of length `n`, which are the lists the C reads.
* **The program.** `P.prog()` (`prog.bend`) is **generated** from `ir/<variant>.json` by `gen.py`. The same JSON is emitted as `i8dot.c`.
* **Proofs.** `PROOF.bend` proves both laws for the positive program by structural induction on
  the inputs, with two helper laws, `loop_exact` and `loop_mats`.

**Native exactness contract** (Lean, `lean/Safety.lean`, run with `lean Safety.lean`):
* `prod_bound`: for `x, y ∈ [-128, 127]`, `x*y ∈ [-16256, 16384]`.
* `prefixes_bound`: every prefix sum after k steps lies in `[-16256·k, 16384·k]`.
* `int32_prefix_safe`: for `n ≤ 131071`, **every prefix sum** of `acc := acc + a[i]*b[i]` lies in `[-2^31, 2^31-1]`.
* `int32_product_safe`: every product fits in int32.
* `bound_tight`: 131071 is the largest n this argument allows, since 131072·16384 = 2^31.

`#print axioms` reports `propext`, `Classical.choice` and `Quot.sound` for these (core `omega`/`simp`), and none for `bound_tight`.
So in C, every `r0*r1` and every `acc + r0` is an exact `int32_t` operation, and **no step relies on signed overflow**.

## 3. How the laws reach the emitted C

```
ir/<v>.json ──gen.py (TRUSTED)──► prog.bend ──► LAWS.bend / PROOF.bend   (bend --verdict)
            └──────────────────► i8dot.c ──► check_c.py (independent; reads only the .c, plus the JSON for comparison)
                                               ├─ buffer scan on C tokens → BUFFER/no buffer
                                               ├─ r2: lexical gate + complete ordered grammar over the whole file → IR ops (anything else → REJECT)
                                               └─ lifted IR == ir/<v>.json ?
```

**`check_c.py` (r2)** is an independent validator that rejects anything it cannot confirm (fail-closed). It does not import `gen.py`. It has three gates:
* **`--gate nobuf FILE`**: a buffer scan, then the grammar. Exit codes: 0 PASS, 1 BUFFER, 2 REJECT.
* **`--gate exact FILE ir/pos.json`**: the grammar, then the lifted IR must equal the IR whose `PROOF.bend`
  passed. Exit codes: 0 PASS, 2 REJECT, 3 IR MISMATCH. This is the exact-sum gate.
* **`--gate match FILE ir/<v>.json`**: emitter consistency only.

1. **Lexical gate**, on the raw bytes including comments:
   * no backslash, so no line splices (a `// … \` would comment out the next line);
   * no `??`, so no trigraphs;
   * every block comment opens and closes on one line.

   Comments are then removed by a left-to-right scan; lines are trimmed and empty lines dropped.
2. **Grammar.** It is complete and ordered, every item is one exact line, and the parse must reach EOF:
   ```
   file  := "#include <stddef.h>" "#include <stdint.h>" "#define I8DOT_MAX_N 131071u"
            SIG "if (n > I8DOT_MAX_N) return -1;"
            "int32_t acc = 0;" "int32_t r0 = 0;" "int32_t r1 = 0;"
            loop+ "*out = acc;" "return 0;" "}" EOF
   loop  := "for (size_t i = 0; i < n; i++) {" item+ "}"
   item  := "r0 = (int32_t)a[i];" -> LdA | "r1 = (int32_t)b[i];" -> LdB | "r0 = r0 * r1;" -> Mul
          | "acc = acc + r0;" -> Acc
          | "acc = (int32_t)((uint32_t)acc & 0xFFu);" "if (acc > 127) acc = acc - 256;" -> Wrap
   ```
   As a result:
   * the guard, the declarations, the loops, the single output store **after** the last loop, the terminal return and the closing brace are each forced into position;
   * a known statement in the wrong place is rejected, as is an extra or unmatched item, a premature return, or any trailing content;
   * there are no nested loops, branches or calls apart from the fixed wrap pair.
3. **Meaning.** A file that parses is a straight-line prologue, a sequence of `for i in [0, n)` loops whose bodies are op sequences, then `*out = acc; return 0;`.
   That is exactly the shape `K.run_prog` evaluates. The per-item C meaning (each item ↔ its IR op, under §2's contract) is **trusted by inspection, not proved**.

## 3b. r3: the machine-checked acceptance-to-semantics bridge (`bridge/`)

```
variants/<v>/i8dot.c (bytes) ──► C.parseFile ──► CFile AST ──► Check.validate ──► p  ┐
variants/<v>/prog.bend (bytes, the file bend --verdict checks) ──► BendP.parseBend ──► q ┴─► Check.gate: p = q (exact: ∧ q = posIR)
i8check (lean_exe, Main.lean) prints the verdict; exit 0 PASS / 2 C REJECT / 3 IR MISMATCH / 4 prog.bend REJECT / 5 UNCERTIFIED (r4)
```

**Modules** (all of them are in the `lake build`):

| module | role |
|---|---|
| `Bridge/CSyntax.lean` | C AST; lexical gate (no `\`, `"`, `'`, `%`, CR/TAB, `??`); left-to-right comment removal (a block comment may not span lines); the **line table** mapping each exact trimmed line to an AST node; a parser that builds the tree in file order. The parser accepts known lines **in any order**, so an early store or early return still parses. |
| `Bridge/CSem.lean` | an independent big-step semantics of that AST (`C.cRun`). It never mentions the IR. |
| `Bridge/IR.lean` | a line-by-line Lean transcription of the `kernel.bend` evaluator over `Int`; `posIR`/`wrapIR`/`bufIR`; the Lean reference `refDot`. |
| `Bridge/BendParse.lean` | parses the exact generated `prog.bend`: the fixed preamble, `#` comments, and one `K.PCons…` term. It accepts only if re-printing the parsed term reproduces the file's term line character for character. |
| `Bridge/Check.lean` | `validate f`: lift `f` to an IR `p`, then accept only if `render p = some f`, i.e. the file is exactly the canonical rendering of `p`. Also the `gate` used by both `i8check` and the theorems. r4: `certified p := p = posIR ∨ p = wrapIR`; the match gate returns `.uncertified` for a matching uncertified term. |
| `Bridge/Proofs.lean`, `Audit.lean` | the theorems and the `#print axioms` audit. |

**C-subset semantics (`C.cRun`), as modeled.**
* **Integer widths:** `int` = `int32_t` is 32-bit two's complement; `uint32_t` = `unsigned int` is 32-bit; `size_t` is 64-bit.
* **Values:** values are exact `Int`/`Nat`. Signed `*`, `+`, `-` fault when the mathematical result is outside \([-2^{31}, 2^{31}-1]\) (UB). `(uint32_t)x` is \(x \bmod 2^{32}\). `& 0xFFu` is bitwise and on `Nat`. `(int32_t)u` is defined only for \(u \le 2^{31}-1\); otherwise it faults, since the conversion is implementation-defined and refused.
* **Array reads:** `(int32_t)a[i]` faults if `i` is out of bounds or the element is not in \([-128,127]\). `i` exists only inside a `for`.
* **Loops:** `for (size_t i = 0; i < n; i++)` iterates `i = 0..n-1` (`loopK`, fuel `n − i`).
* **Other faults:** using an undeclared variable, redeclaring one, an undefined macro, and falling off the end of the function.
* **Guard:** `if (n > I8DOT_MAX_N) return -1;` resolves the macro from the parsed `#define`.
* **Observable effects:** the return value and the single `*out` cell (`none` means the kernel never wrote it; `out0` is the caller's prior content). The AST has no other writable memory: no array, pointer or allocation construct exists. `a` and `b` are read-only lists, so no write to them is expressible.
* **Admitted inputs (`C.Admitted`):** every element of `a` and `b` is int8; `n ≤ |a|` and `n ≤ |b|`, so **both** arrays are readable for `n` elements; `n < 2^64`. The C kernel never sees list lengths. Only the Bend/IR model truncates unequal lists; the theorems apply the IR to `a.take n`, `b.take n`.

**Theorems** (`Bridge/Proofs.lean`; every premise is the executable checker's own verdict):

| theorem | statement (informal) |
|---|---|
| `gate_pass` | `gate cs bs ex = .pass p` ⇒ `parseFile cs = .ok f`, `validate f = .ok p`, `parseBend bs = .ok p`, `render p = some f`, and `ex = true → p = posIR`. |
| `recovered_shape` | PASS ⇒ `f.dirs` = the fixed `#include <stddef.h>`, `#include <stdint.h>`, `#define I8DOT_MAX_N 131071u`. Also `f.body = [guard, int32_t acc=0, r0=0, r1=0] ++ ls ++ [*out = acc, return 0]`, with `ls` a non-empty list of non-empty `for` loops. So no store or return before or inside a loop, no missing guard, no trailing statement. |
| **`gate_total`** (r4, public) | `gate cs bs ex = .pass p` ⇒ `parseFile cs = .ok f`, `parseBend bs = .ok p`, `p = posIR ∨ p = wrapIR`, `ex = true → p = posIR`, and for **every** admitted input `cRun f = if 131071 < n then ret (-1) out0 else ret 0 (some (IR.run p (a.take n) (b.take n)).acc)`. No fault. One theorem for both gates. |
| `gate_requires_certified`, `overflowIR_not_certified` (r4) | the gate never passes a prog.bend term with `certified q = false`; the reviewer's overflow IR is such a term |
| `overflow_faults` (r4) | the overflow IR renders to valid subset C, and on the admitted in-range input `[-128,127,-128,127]·[-128,-128,127,127]` (n = 4) its C semantics **faults**. So certification is necessary, not cosmetic. |
| `zadd_val`, `zmul_val` (r4, optional) | for a Lean transcription of kernel.bend's `zadd`/`zmul` on Nat pairs, `zval (p,n) = p − n` is a homomorphism. This is a Lean lemma about the transcription, **not** a proof about Bend. |
| `sound_render` / `gate_pass_conditional_sim` (internal) | for **any** rendered program `p` and admitted input: if `n > 131071`, `cRun = ret (-1) out0` (`*out` untouched). If `n ≤ 131071`, `cRun` either faults or `= ret 0 (some (IR.run p (a.take n) (b.take n)).acc)`. This is partial correctness for arbitrary op sequences, such as a double `Mul`, that can overflow. |
| `pos_loop_total`, `wrap_loop_total` | C-level totality: with n ≤ 131071 every `pos` product and prefix sum is in int32 (product ∈ [−16256, 16384], prefix ∈ [−16256·i, 16384·i]). The `wrap` accumulator stays in [−128, 127]. |
| `ir_pos_exact` | `(IR.run posIR xs ys).acc = refDot xs ys`: the Lean-model counterpart of Bend LAW 1. |
| **`exact_gate_sound`** | `gate cs bs true = .pass p` ⇒ `p = posIR`, `parseBend bs = .ok posIR`, `parseFile cs = .ok posFile`, and for all admitted inputs `cRun posFile = if 131071 < n then ret (-1) out0 else ret 0 (some (refDot (a.take n) (b.take n)))`. No fault. |
| `wrap_match_sound` | PASS against a prog.bend whose term is `wrapIR` ⇒ `parseFile cs = .ok wrapFile`, and `cRun wrapFile` totally equals `IR.run wrapIR` (−1 path likewise). |
| `exact_gate_requires_pos`, `wrapIR_ne_posIR` | the exact gate can never pass against a prog.bend term ≠ `posIR`; in particular it rejects the wrap kernel. |
| `ir_witness_*` (`decide`) | the IR model gives wrap `[12]·[11]` = −124, pos `[3,−5,7]·[−2,4,1]` = −19, buf `[1]·[1]` mats = 2, buf exact = −19. These match Bend's own `REFUTE`/`demo` results (`Z{0,124}`, `Z{7,26}`, mats 2): an artifact comparison of the two evaluators. |

**Audit:**
* `lake build` is clean.
* `Audit.lean` is **generated** by `grep '^theorem'` over `Bridge/Proofs.lean` and (r5) `Bridge/BendLink.lean`: 72 entries in r5, 36 + 36. r3's hand-written list of 28 had missed `Ag.bind` and `drop_take_len`.
* `lake env lean Audit.lean` (r5: 72 entries) shows each theorem uses only a subset of `propext`, `Classical.choice` and `Quot.sound`. Of the 72, 14 use none, 18 use `propext` only, 21 use `propext` and `Quot.sound`, and 19 use all three. (r4: 36 entries, 9 with none.) `Ag.bind` uses none; `drop_take_len` uses `propext`.
* The word scan for `sorry`, `admit`, `native_decide`, `axiom`, `extern`, `unsafe`, `partial`, `opaque` and `implemented_by` in code is empty. "admitted" appears only in comments.

**What links which (r3):**

| link | status |
|---|---|
| bytes of `i8dot.c` → AST → accept/reject | **executable Lean function, the same one the theorems quantify over** (`Check.gate`). The compiled `i8check` binary trusts the Lean compiler/runtime and `IO.FS.readFile`. |
| accepted AST → C-subset semantics = IR semantics of the prog.bend term (all admitted inputs) | **machine-checked** (Lean, the theorems above) |
| bytes of `prog.bend` → IR term | **executable Lean parser + exact print round-trip**; the file path is the one `bend --verdict` checked in that variant directory |
| Lean IR evaluator `IR.run` ≡ Bend `K.run` (and `Z{p,n}` ≡ the Int `p−n`) | **not mechanized**: a line-by-line transcription, cross-checked at four witnesses against Bend's own checked results. There is no BendTT/Bend-to-Lean refinement proof. |
| Bend LAW 1 / LAW 2 over `K.run` | machine-checked **by Bend** (`--verdict`), a separate checker. In Lean, `ir_pos_exact` re-proves LAW 1 for the transcribed model. |
| the line table: each exact C line ↔ its AST node; the C-subset semantics ↔ ISO C for those lines | **trusted** (the semantics is written from the C rules listed above; there is no ISO C formalization) |
| the parsed file is what the C compiler compiles | **trusted**: no `-D`/`-include` flags; standard headers define none of the identifiers `a b n i out acc r0 r1`; the lexical gate plus comment stripping matches C translation phases 1–3 for files containing no `\`, `??`, quotes or `%` |
| ABI: `int8_t`/`int32_t` exist, `int` is 32-bit, `size_t` is 64-bit, caller's arrays and `out` are valid | **assumed** (x86-64 Linux, gcc 11.4 / clang 14) |
| native code = C semantics | **not covered**: compiler trusted; finite native runs only (§5) |

**Unsupported (rejected, by design):** any line outside the table (e.g. `#include <stdlib.h>`, `malloc`, any array or `static` declaration, calls, a second `a[i]` load), nested loops, and `return`/`*out`/declarations inside a loop. So the buffered mutant is a **C REJECT (exit 2)** under `i8check`; its BUFFER classification comes from the unproved Python baseline. No theorem says anything about rejected files.

## 3c. r5: the translated Bend evaluator and the all-input link (`bendlink/`, `Bridge/BendKernel.lean`, `Bridge/BendProgs.lean`, `Bridge/BendLink.lean`)

```
kernel.bend (actual) ─┐
base.bend (pinned; == ~/.bend/bend2/base.bend, which bend 2.0.40 opens) ─┼─ bend2lean.py (TRUSTED, fail-closed) ─► Bridge/BendKernel.lean  (namespace BK)
variants/{pos,wrap,buf}/prog.bend (actual, the files bend --verdict checks) ─┘                      └► Bridge/BendProgs.lean   (BK.P_pos.prog, …)
run_all.sh: regenerate → cmp with the committed .lean (must be identical) → lake build (proofs must check)
```

**Construct mapping** (`bend2lean.py` docstring). Each line is a trusted identification of Bend surface meaning with Lean meaning for this subset. Anything else exits 2.

| Bend 2.0.40 | Lean 4.15.0 |
|---|---|
| `type T is Data:` with `C{f: A, …}` lines | `inductive T` with `| C (f : A) …` |
| `Nat` (base `Zero{}`/`Succ{pred}`), `Bool` (`False{}`/`True{}`), `A & B` | Lean `Nat`, `Bool`, `A × B` (not translated; identified) |
| `def f(+x: A, -y: B) -> R:` | `def f (x : A) (y : B) : R` (linearity/erasure marks dropped) |
| `match a b:` / `case P Q:` | `match a, b with | P, Q =>` |
| `(a, b) = e` then a body | `let (a, b) := e; body` |
| `Kn`, `Kn+e` (pattern or expression) | `K`, `e + K` |
| `C{e,…}`, `f(e,…)`, `f()`, `K.` prefix in prog.bend | `T.C e …`, `f e …`, `f`, dropped |

The translated base whitelist is `Cmp`, `Pair.fst`, `Pair.snd`, `Cmp.is_lt/is_eq/is_le`, `Nat.add`, `Nat.sub`, `Nat.mul`, `Nat.divmod.go`, `Nat.divmod`, `Nat.cmp`, `Nat.is_lt/is_eq/is_le` and `Nat.mod`. These are the exact definitions from the installed base, not the repo-HEAD base (they differ; see `EVIDENCE.txt` for both sha256).

**Theorems** (`Bridge/BendLink.lean`, namespace `Link`):

| theorem | statement |
|---|---|
| `nat_add`, `nat_sub`, `nat_mul`, `divmod_go`, `nat_mod`, `cmp_spec`, `is_lt`, `is_eq`, `is_le` | the translated base primitives equal Lean `+`, truncated `-`, `*`, `%`, `<`, `=`, `≤` for all naturals |
| `zadd_v`, `zmul_v`, `wrap8_v` | with `zv (Z p n) = p − n`: `zv (zadd a b) = zv a + zv b`, `zv (zmul a b) = zv a * zv b`, `zv (wrap8 a) = ((zv a + 128) % 256) − 128` (through `w8.sel/nat/pos/neg/negr`) |
| `exec_v`, `exec_body_v`, `run_loop_v`, `start_v`, `run_prog_v`, **`run_v`** | decoding the translated evaluator equals `IR.exec`, …, `IR.run`, for every op, program and input, on the whole state |
| `prog_pos_v`, `prog_wrap_v`, `prog_buf_v` | the translated `prog.bend` terms decode to `posIR`, `wrapIR`, `bufIR` (`rfl`) |
| `bend_law_exact_on_translation`, `bend_law_nobuf_on_translation` | Lean re-proof on the translation of Bend LAW 1 (`acc_of(run(prog,xs,ys)) = dot(xs,ys,z0)`, structural `Z` equality) and LAW 2 (`mats_of = 0` for pos and wrap) |
| `dot_v`, `zsv_encs` | `zv (dot xs ys acc) = zv acc + refDot …`; every Int list is the decoding of some `Zs`, so the quantifiers below are not vacuous |
| **`gate_total_bend`** | `gate cs bs ex = .pass p` ⇒ for every Bend term `q` with `stmtsv q = p`, admitted input, and `xs`, `ys` decoding to `a.take n`, `b.take n`: `cRun f = if 131071 < n then ret (-1) out0 else ret 0 (some (zv (K.acc_of (K.run q xs ys))))` |
| `exact_gate_bend_pos` | exact-gate PASS ⇒ `parseBend bs` = the decoding of the translated actual `variants/pos/prog.bend`, and `*out` = `zv (K.acc_of (K.run P_pos.prog …))` = `zv (K.dot … z0)` |
| `match_gate_bend_wrap` | match-gate PASS against a prog.bend parsing to the translated wrap term ⇒ `*out` = `zv (K.acc_of (K.run P_wrap.prog xs ys))` |

The return value, the `n > 131071` guard (−1, `*out` unchanged) and the admitted-input assumptions (§3b) are unchanged from r4.

**Negative controls** (all asserted in `run_all.sh`):

| control | observation |
|---|---|
| A: `bendlink/neg/kernel_w8mut.bend` (`w8.nat`: `Nat.is_lt(r, 128n)` → `127n`) | Bend `--verdict` on pos `PROOF.bend`, wrap `REFUTE.bend` and wrap `NOBUF_WRAP.bend` with the mutated kernel: **all still exit 0**. The change is invisible to the existing Bend laws and witnesses: 127 would now wrap to −129, and none of them evaluates that case. The regenerated `BendKernel.lean` differs from the committed one (`cmp` exit 1). `lake build Bridge.BendLink` against the regenerated translation **fails** (exit 1) in `w8_nat_v`, the lemma `wrap8_v` uses: its `decide (r < 128)` rewrite no longer matches. |
| B: `bendlink/neg/kernel_unsupported.bend` (adds `x + 1`, an expression outside the subset) | the translator refuses it with exit 2, `UNSUPPORTED` |

**Proof links and remaining trust (r5):**

| link | status |
|---|---|
| C file bytes → accepted program → C-subset semantics = `IR.run` of the prog.bend term, total for certified terms | machine-checked (Lean, `gate_total`); premise = the executable gate |
| `IR.run` = decoded translated `K.run` (whole state, all programs, all inputs) | **machine-checked (Lean, `run_v`)**, against the mechanically translated actual `kernel.bend` and pinned `base.bend` |
| translated `K.run` = what bend 2.0.40 means by `kernel.bend` | **trusted**: `bend2lean.py` and its construct mapping (above), with Bend `Nat`/`Bool`/`&` identified with Lean `Nat`/`Bool`/`×`. Replay-checked: regeneration must reproduce the committed Lean byte for byte. Consistency evidence, not proof: Lean re-proves Bend LAW 1/LAW 2 on the translation, and the translated evaluator gives Bend's own checked values at the witnesses. |
| prog.bend bytes → IR term | two independent parsers on the same file: `BendP.parseBend` (used by the gate) and `bend2lean.py progs`. They are tied by `rfl` on the committed terms (`prog_*_v`) plus the regeneration replay. |
| Bend LAW 1/LAW 2 over `kernel.bend` | machine-checked by Bend `--verdict` (a separate checker, BendTT kernel); not imported into Lean |
| ISO C fidelity of the subset semantics, compile flags/headers/ABI, C compiler | trusted (§3b) |
| Lean compiler/runtime for `i8check` | trusted |
| Bend checker/runtime, BendTT kernel | trusted; general Bend semantics and Bend/Lean/native compiler verification are out of scope |

**Learned in r5:**
* The kernel plus the needed base primitives fit a translator of about 300 lines; the full state correspondence for every IR program was about 200 lines of Lean.
* The noncanonical `Z{p,n}` representation is harmless under decoding. `wrap8`'s Nat branching (`Nat.sub`, `Nat.mod` via `divmod.go`, `cmp`) reduces to one `%`-by-literal identity that `omega` closes.
* Bend's existing laws do not pin down `wrap8` at all for `pos`, and the witnesses miss the 127/128 boundary. A semantic change there passes every Bend check but fails the Lean link. The cross-language link adds real coverage.
* The proof is a theorem about the translation. Its trust moved from "the hand-written `IR.run` is faithful" to "this narrow syntax-directed mapping is faithful". The latter is smaller and replayable, but still unproved.

## 4. Variants and negative controls

All three variants come from the same emitter (`gen.py ir/<v>.json variants/<v>`). The Bend files
`kernel.bend`, `LAWS.bend` and `PROOF.bend` are byte-identical across variants (sha256 in `EVIDENCE.txt`); only `prog.bend` differs.

| variant | IR | emitted loop body |
|---|---|---|
| `pos` | `[Loop[LdA, LdB, Mul, Acc]]` | `r0=(int32_t)a[i]; r1=(int32_t)b[i]; r0=r0*r1; acc=acc+r0;` |
| `wrap` | `[Loop[LdA, LdB, Mul, Acc, Wrap]]` | as pos, then `acc=(int32_t)((uint32_t)acc & 0xFFu); if (acc > 127) acc = acc - 256;` |
| `buf` | `[Alloc, Loop[LdA, LdB, Mul, StT], Loop[LdT, Acc]]` | `t = malloc(n·4)`; loop 1: `t[i] = r0`; loop 2: `r0 = t[i]; acc += r0`; `free(t)` |

**`wrap`** narrows the accumulator to 8 bits with defined C arithmetic:
* unsigned conversion and masking, then a sign fix;
* `acc + r0` stays within ±16511, so there is no signed overflow and no implementation-defined narrowing.

8 bits rather than 16 because Bend `Nat` is unary: `Nat.mul(128n, 128n)` already overflows the checker/runtime
stack, so a 16-bit witness (≥ 32768) cannot be evaluated in Bend. The native mutant uses the same 8-bit operation.

**`buf`** really writes the temporary array and folds it, and gives the exact sum.

## 5. Commands and outcomes

Run `./run_all.sh > EVIDENCE.txt` (set `BEND=/path/to/bend` to override the default `~/.bend/bin/bend`). Every run has an asserted expected exit code; the script ends with `REPLAY OK` (exit 0) or `REPLAY FAILED` (exit 1). Raw output plus exit code for every check is in `results/<name>.txt`.

| check (command) | pos | wrap | buf |
|---|---|---|---|
| `bend PROOF.bend` | ALL PROOFS CHECK, 0 | SOME PROOFS FAIL, 1 | SOME PROOFS FAIL, 1 |
| `bend PROOF.bend --verdict` | ALL PROOFS CHECK, 0 | SOME PROOFS FAIL, 1 | SOME PROOFS FAIL, 1 |
| first Bend failure | none | `L.exact`: the goal's loop body has `Wrap`; the proof's has none | `L.exact`: goal is `start(LdT;Acc, …, run_loop(LdA;LdB;Mul;StT, …, mats=1))` |
| `bend REFUTE.bend --verdict` | n/a | ALL PROOFS CHECK, 0: proves `acc(run [12]·[11]) == Z{0,124}` (= −124), `dot == Z{132,0}`, and **`≠`, i.e. ¬LAW 1** at the witness | ALL PROOFS CHECK, 0: proves `mats(run [1]·[1]) == 2`, **`≠ 0`, i.e. ¬LAW 2**, and the exact result `== dot` on `[3,-5,7]·[-2,4,1]` (−19) |
| `bend NOBUF_WRAP.bend --verdict` | n/a | ALL PROOFS CHECK, 0: **LAW 2 holds for all inputs** | n/a |
| `check_c.py --gate nobuf variants/<v>/i8dot.c` | PASS, 0 | PASS, 0: no buffer | **BUFFER, 1**: `stdlib.h`, `malloc` + pointer decl (line 12), `t[i] = r0` store (18), `t[i]` read (21), `free` (24) |
| `check_c.py --gate exact variants/<v>/i8dot.c ir/pos.json` (exact-sum gate) | PASS, 0: lifted `[Loop[LdA,LdB,Mul,Acc]]` == the Bend-proved IR | **IR MISMATCH, 3**: lifted IR has `Wrap` | **REJECT, 2**: line 4 `#include <stdlib.h>` is outside the grammar (its sum is exact, but this gate cannot validate it) |
| `check_c.py --gate match variants/<v>/i8dot.c ir/<v>.json` | PASS, 0 | PASS, 0 | REJECT, 2 is expected (grammar). Not asserted; only pos/wrap are matched |
| native, gcc and clang, -O0 and -O2 (`native/test.c` + independent `native/ref.c`) | all fixed cases OK; 100,000 random runs, 0 mismatches | **`[12]·[11]`: ref 132, emitted −124**; boundary-max: ref 2147467264, emitted 0; 98,100/100,000 random runs mismatch | all fixed cases OK; 0 mismatches |
| clang `-fsanitize=undefined`, and separately `-fsanitize=address` (-O1; ASan run under `setarch -R`) | 0 mismatches, no sanitizer report, exit 0 (each) | — | — |

The fixed native cases, with expected values computed separately in Python:

| case | expected |
|---|---|
| empty | 0 |
| mixed signs `[3,-5,7]·[-2,4,1]` | −19 |
| `[-128,127,-128,127]·[-128,-128,127,127]` | 1 |
| `[12]·[11]` | 132 |
| `[-128]³·[-128]³` | 49152 |
| accumulator boundary: n = 131071, all `-128·-128` | 2147467264 (INT32_MAX − 16383) |
| n = 131071, all `-128·127` | −2130690176 |
| n = 131072 | guard returns −1 |

**Validator controls**, made by hand-editing the concrete emitted `pos` file (`checker_tests/make.sh`):

| control (edit of emitted pos) | nobuf gate | exact gate | first reason | native gcc -O2 |
|---|---|---|---|---|
| `early_store`: the single `*out = acc;` moved before the loop (the reviewer's case) | REJECT, 2 | REJECT, 2 | line 11: expected `for (...) {`, found `*out = acc;` | **`[12]·[11]` → 0 (ref 132)**; mixed → 0 (ref −19); 98,520/100,000 random mismatches |
| `early_return`: `*out = acc; return 0;` inserted before the loop | REJECT, 2 | REJECT, 2 | line 11: same | `[12]·[11]` → 0; 98,520 mismatches |
| `comment_splice`: `// store result \` before `*out = acc;` (the splice comments the store out) | REJECT, 2 | REJECT, 2 | line 17: backslash not allowed | `[12]·[11]` → 0; 98,520 mismatches |
| `missing_guard`: length guard deleted | REJECT, 2 | REJECT, 2 | line 7: expected length guard | not run (n = 131072 would overflow) |
| `trailing_stmt`: extra `acc = acc + r0;` after the loop | REJECT, 2 | REJECT, 2 | line 17: expected final output store | not run |
| `unknown_call`: `acc = mystery(acc);` in the loop | REJECT, 2 | REJECT, 2 | not a loop item | — |
| `double_load`: second `a[i]` load | REJECT, 2 | REJECT, 2 | not a loop item | — |
| `stack_vla`: `int32_t t[n]` written and read, same sum | **BUFFER, 1** | REJECT, 2 | array declaration, `t[i]` store/read | — |
| `static_arr`: `static int32_t t[131071]`, same sum | **BUFFER, 1** | REJECT, 2 | static storage, array declaration | — |

For the record, `run_all.sh` also runs the r1 validator (`checker_tests/check_c_r1.py`) on `early_store.c`, and it still says PASS, exit 0.

**How to read the Bend failures.**
* A failing proof is not by itself evidence that a law is false. Bend stops at the first failing
  def, and for **both** mutants that def is `L.exact`, the universal proof written for the positive body.
  For `buf`, LAW 1 is in fact true; only the proof does not apply.
* The decisive results are the **checked refutations** in `REFUTE.bend`, checked by `--verdict`:
  * `wrap` falsifies LAW 1 on `[12]·[11]`;
  * `buf` falsifies LAW 2 on `[1]·[1]`;
  * `NOBUF_WRAP.bend` proves `wrap` still satisfies LAW 2 universally.
* The buffer rejection of the emitted C is independent: it comes from `check_c.py` on the file itself.

### 5b. r3 replay: `i8check` (authoritative, Lean) on the actual files

Exit codes: 0 PASS, 2 C REJECT, 3 IR MISMATCH, 4 prog.bend REJECT, 5 UNCERTIFIED (r4). Raw outputs are in `results/i8check_*.txt`; every exit code is asserted by `run_all.sh`.

| C file | prog.bend | gate | exit | reason (diagnostic text from `Check.explain`; the verdict itself is the proved `gate`) |
|---|---|---|---|---|
| `variants/pos/i8dot.c` | `variants/pos/prog.bend` | exact | **0 PASS** | IR `[Loop [LdA, LdB, Mul, Acc]]` = prog.bend term = `posIR` |
| `variants/pos/i8dot.c` | `variants/pos/prog.bend` | match | 0 PASS | |
| `variants/wrap/i8dot.c` | `variants/pos/prog.bend` | exact | **3 MISMATCH** | C lifts to `[Loop [LdA, LdB, Mul, Acc, Wrap]]`; prog.bend is posIR |
| `variants/wrap/i8dot.c` | `variants/wrap/prog.bend` | match | **0 PASS** | C lift = wrap prog.bend term (`wrap_match_sound` applies) |
| `variants/wrap/i8dot.c` | `variants/wrap/prog.bend` | exact | 3 MISMATCH | term ≠ posIR (`exact_gate_requires_pos`) |
| `variants/buf/i8dot.c` | pos / buf prog.bend | exact / match | **2 REJECT** | line 4: unrecognised line `#include <stdlib.h>` (subset has no allocation/array constructs) |
| `early_store.c` | pos | exact, match | **2 REJECT** | statement 4: expected `for (size_t i = 0; i < n; i++) {`, found `*out = acc;` |
| `early_return.c` | pos | exact, match | **2 REJECT** | statement 4: expected `for (…) {`, found `*out = acc;` (then `return 0;`) |
| `comment_splice.c` | pos | exact | 2 REJECT | backslash (line splice) not allowed |
| `missing_guard.c` | pos | exact | 2 REJECT | statement 0: expected `if (n > I8DOT_MAX_N) return -1;`, found `int32_t acc = 0;` |
| `trailing_stmt.c` | pos | exact | 2 REJECT | statement 5: expected `*out = acc;` (after the last loop), found `acc = acc + r0;` |
| `unknown_call.c`, `double_load.c`, `stack_vla.c`, `static_arr.c` | pos | exact | 2 REJECT | unrecognised line (`mystery(acc)`, second `a[i]` load, `int32_t t[n ? n : 1];`, `static int32_t t[131071];`) |
| `checker_tests/overflow/i8dot.c` (generated by `gen.py`) | its generated `prog.bend` | match | **5 UNCERTIFIED** (r3: 0 PASS) | C lift = prog.bend term = `[Loop [LdA, LdB, Mul, Mul, Mul, Mul, Acc]]`, but this IR has no totality proof |
| `checker_tests/overflow/i8dot.c` | its generated `prog.bend` | exact | 3 MISMATCH | term ≠ posIR |
| `checker_tests/overflow/i8dot.c` | `variants/pos/prog.bend` | match | 3 MISMATCH | C lift ≠ pos term |
| `variants/pos/i8dot.c` | `prog_renamed.bend` (`def prog2`) / `prog_extra.bend` (extra def) | exact | **4 REJECT** | not exactly the generated preamble + `def prog() -> K.Stmts:` + one term |

The r2 Python baseline **accepts** the overflow control (`--gate match`, exit 0), because it has no totality notion; it stays unproved and advisory.
The r2 Python baseline still gives its own verdicts in the same run (`results/check_*.txt`): `buf` is BUFFER (1) under `--gate nobuf`, and the other controls are as in §5.

**Lean C-subset semantics executed on the parsed files** (`i8check csem FILE`, `results/csem_*.txt`). These are finite witnesses, not theorems. They also show that the semantics is not rigged to agree: the parser accepts the misordered files, and `C.cRun` computes their real (wrong) behaviour.

| parsed file | `[3,−5,7]·[−2,4,1]` (ref −19) | `[12]·[11]` (ref 132) |
|---|---|---|
| pos | ret 0, out −19 | ret 0, out 132 |
| wrap | ret 0, out −19 | ret 0, out **−124** (= IR wrap, = Bend `Z{0,124}`, = native) |
| early_store | ret 0, out **0** | ret 0, out **0** (matches native 0) |
| early_return | ret 0, out **0** | ret 0, out **0** |
| trailing_stmt | ret 0, out **−12** | ret 0, out **264** |
| overflow (r4) | ret 0, out −1225 (= its own IR; uncertified) | extremes `[-128,127,-128,127]·[-128,-128,127,127]`: **fault**; `[-128]³·[-128]³`: **fault** |

## 6. What is proved, what is checked, what is trusted

| claim | kind | scope |
|---|---|---|
| LAW 1 and LAW 2 for `pos` | **symbolic, universal** (Bend, `--verdict`) | all pairs of finite integer sequences, over the IR term generated from `ir/pos.json` |
| ¬LAW 1 for `wrap`, ¬LAW 2 for `buf` | symbolic refutation at a concrete witness (Bend, `--verdict`) | IR level |
| LAW 2 for `wrap` | symbolic, universal (Bend, `--verdict`) | IR level |
| `buf` gives the exact sum | finite only: one Bend witness, native runs | **not** proved universally |
| int32 safety of every product and prefix sum for int8 inputs and n ≤ 131071 | symbolic, universal (Lean) | over `Int` prefix sums of `acc := acc + x*y` |
| `i8check` PASS ⇒ C-subset semantics of the recovered program = IR semantics of the exact prog.bend term, **total** (r4 `gate_total`); exact gate ⇒ exact dot product; no writable memory but `*out` | **machine-checked (Lean, r3/r4)** with the executable `i8check` verdict as premise | every file `i8check` accepts; all admitted inputs; modulo the trusted line table, C-subset fidelity, and the IR-transcription link (§3b) |
| no buffer, single loop, one load each of `a[i]` and `b[i]`, lifted IR == JSON | **artifact check**, r2 Python baseline (`check_c.py`, unproved) | only these files |
| emitted results = reference | **finite native executions**, gcc/clang -O0/-O2, UBSan and ASan as separate builds. With ASLR on, the clang-14 ASan binary segfaulted at startup in 3 of 6 plain runs and 0 of 6 under `setarch -R`, so it is run with ASLR off; an r1 combined build failed the same way | these inputs, this machine |
| gcc -O2 `pos`: 24 instructions, 0 calls, 0 stack stores, scalar. clang -O2: 116 instructions, 0 calls, 0 stack stores, vectorized (`xmm`). `buf` -O2 calls `malloc`/`free` | **optimizer/code-shape observation** | x86-64, these compilers |

**Trusted, not proved:**
* `gen.py` emits the JSON consistently into both `prog.bend` and C. This is partly re-checked: the lifted IR from C is compared with the JSON, but nothing checks that `prog.bend` matches the JSON except the generator itself.
* r3 (`i8check`): the line table and the C-subset semantics' fidelity to ISO C for those lines; that the Lean IR transcription is the Bend evaluator; the Lean compiler/runtime for the `i8check` binary. Details in §3b.
* `check_c.py` (r2 baseline, now advisory): that its grammar items mean what the IR ops mean, and its lexical gate and comment stripping. Also that the standard headers define no macro named `a`, `b`, `n`, `i`, `t`, `out`, `acc`, `r0` or `r1`, and that the file is compiled as-is with no `-D` flags.
* That the Bend `Z` evaluator and the Lean `Int` prefix lemma describe the same arithmetic. They are separate models linked by reading them.
* The C compiler; `int` being 32-bit; callers passing `n` readable elements and a valid `out`.
* The Bend checker and the BendTT kernel, plus the caveat recorded earlier that the installed kernel/base files differ from repo HEAD.

**Native costs not modeled:**
* time, cache behaviour and vectorization;
* code size and register pressure;
* the `int32_t` widening loads;
* the length-guard branch;
* the stack frame.

`mats` counts buffer allocations and writes in the IR only. Registers and spills the compiler may introduce are invisible to the laws. The -O2 objdump shows no stack stores for these two builds, but that is an observation, not a guarantee.

**Open:**
1. ~~A verified lifter~~: done in r3 for the supported subset, relative to the C-subset semantics in `CSem.lean`. Still open are a proof against an ISO C formalization (e.g. CompCert Clight), a verified `gen.py`, and a mechanized Bend↔Lean IR refinement.
2. A universal exact law for `buf`, which needs an append/snoc lemma.
3. A 16-bit wrap witness inside Bend, blocked by unary `Nat`.
4. Linking the Lean safety lemma to the Bend `Z` semantics in one checker.
5. Machine-code-level no-buffer: what the compiler emits, not what the C says.
6. Scale/zero-point requantization ("before scale" is all that is covered here).

## 7. Relation to `zc-iter-cost`

`zc-iter-cost` (Lean) proved *modeled* zero overhead, meaning cost counters equal to a hand-written loop, for any map/filter/fold pipeline. But:
* its costs were ticks of IR events with no heap semantics;
* nothing linked the emitted C to the IR.

This artifact takes those two gaps head-on for one kernel:
* buffer operations change evaluator state and are counted;
* the no-buffer property is checked a second time, independently, on the **emitted C file**, with the C lifted back to the exact IR the laws are about.

It also adds a width contract (Lean) that the earlier pure model did not need.

**Learned (observed here):**
* Bend 2.0.40 checks universal inductive laws over a user-defined IR evaluator, and `{a != b}` refutations by `%h : disc(_)`, both under `--verdict`.
* `List<T>` is not Data-kinded, so a copyable sequence type was needed.
* A `match` on a later binder is refused; match the op first.
* Defs must be defined before use.
* Unary `Nat` limits concrete evaluation to small values.
* A failed proof run reports only the first failing def.

* r3: in Lean 4.15 core, "accept only if `render (lift f) = f`" makes the soundness proof independent of the lifter. The order and scope guarantee falls out of `render`'s fixed shape. The bridge is about 440 lines of proof (`Proofs.lean`), plus about 450 lines of checker, semantics and parsers.

**Proposed, not established:** that this render-equality pattern scales to richer kernels or vectorized lowering, or that the hand-written C-subset semantics could be replaced by an existing verified C semantics.

## 8. Files

* `kernel.bend` (Z, reference, IR, evaluator), `prog.bend`, `LAWS.bend`, `PROOF.bend`, `demo.bend` (runs pos on `[3,-5,7]·[-2,4,1]`: `Z{7n, 26n}` = −19)
* `ir/*.json`, `gen.py`, `check_c.py` (r2), `checker_tests/` (controls, `make.sh`, the r1 validator `check_c_r1.py`)
* `variants/{pos,wrap,buf}/` (emitted `i8dot.c`, generated `prog.bend`, copies of the shared Bend files, mutant `REFUTE.bend` / `NOBUF_WRAP.bend`)
* `native/ref.c`, `native/test.c`
* `lean/Safety.lean`
* `bridge/` (r3): `lakefile.lean`, `lean-toolchain`, `Bridge.lean`, `Bridge/{IR,CSyntax,CSem,BendParse,Check,Proofs}.lean`, `Main.lean` (the `i8check` exe), `Audit.lean`; `checker_tests/prog_renamed.bend`, `prog_extra.bend` (prog.bend negative controls)
* r5: `bendlink/bend2lean.py`, `bendlink/base.bend.pinned`, `bendlink/neg/{kernel_w8mut,kernel_unsupported}.bend`, generated `bridge/Bridge/{BendKernel,BendProgs}.lean`, `bridge/Bridge/BendLink.lean`
* r4: `ir/overflow.json`, `checker_tests/overflow/{i8dot.c,prog.bend}` (generated by `gen.py`; Lean-semantics and gate control only, never compiled natively)
* `run_all.sh`, `EVIDENCE.txt`, `results/` (raw verdicts with exit codes, objdumps)
