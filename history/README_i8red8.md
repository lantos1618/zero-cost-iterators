# i8red8: a typed lazy `.view()` with explicit `.fuse()` / `.parallelize(...)`, APL reference models, and one real path to C

Private local artifact (`~/i8red8`, copied from i8red7). The five `.loop()` INT8 kernels and every i8red7 check are
kept and replayed unchanged. Nothing here is an APL interpreter, a parallel or GPU backend, a verified vectorizer, or a
verified C compiler. No floating-point claim is made: every model is exact `Int` (Lean) or `Nat` (Bend).

## 1. The canonical form

```lean
-- generic typed lazy view (Lean model, bridge/Vw/Plan.lean, Vw/Par.lean)
xs.view.map f |>.filter p |>.fuse |>.foldl seed step
xs.view.map f |>.fuse |>.parallelize 4 |>.reduce Vw.intAdd      -- accepted: associative + identity, ordered
xs.view |>.fuse |>.parallelize 4 |>.foldl 0 (· - ·)             -- refused at the terminal: arbitrary foldl

-- the REAL C entry point over signed-byte pairs (bridge/Vw/PairView.lean -> existing Pipe IR -> emitter -> gate)
BytePairs.view.map multiply |>.fuse |>.accumulate 0                -- APL  A +.× B   (dot)
BytePairs.view.map subtract |>.map abs      |>.fuse |>.accumulate 0
BytePairs.view.map subtract |>.map square   |>.fuse |>.accumulate 0
BytePairs.view.map subtract |>.map nonzero  |>.fuse |>.accumulate 0
BytePairs.view.map subtract |>.map clampNeg |>.fuse |>.accumulate 0
```

* `xs.view` / `BytePairs.view` builds a plan only: no intermediate collection and no element pulls at construction.
* `map`, `filter`, `take`, `drop`, `enumerate`, `scan`, `flatMap`, `distinct`, `chunk`, `window`, `sortBy`, `groupBy`
  are adapters; `foldl`, `find`, `any`, `all`, `reduce`, `accumulate` are terminals. `accumulate(seed)` is ordered
  `foldl(seed, +)`.
* `.fuse()` requests order-preserving loop fusion; `.parallelize(k)` requests chunked scheduling. Both only annotate the
  plan; legality is checked when the terminal is chosen. Plain view use (no request) works and has the same result.
* Name overlap: Rust's `Iterator::fuse()` means "keep returning `None` after the first `None`". Here `.fuse()` means
  loop fusion. C++ analogue: `std::views::all(src) | std::views::transform(f) | std::views::filter(p)` then
  `std::ranges::fold_left`.

The five `.view()` byte-pair chains build the very same `Reduced` chains as the `.loop()` chains (`view_chains`, `rfl`).
The fresh pipegen run emits their C and Bend into `view/<k>/`. These files are **byte-identical** to the
`.loop()` output and to the committed `gen7/<k>` files that i8red7 gated and benchmarked. No new benchmark was run;
the earlier timings apply to these same bytes.

## 2. Replay

**Execution rule.** Every build, Lean/Bend proof check, test, replay and benchmark for this project runs only
inside the Devin workspace (Linux VM, `/home/ubuntu`). The user's Mac is used only to view and steer the
session. No step requires a local replay, and the earlier Mac Metal work is not rerun.

```sh
cp -a ~/i8red8 fresh  (excluding .lake / results_* ; the replay used tar --exclude)
cd fresh && ./run_i8red8.sh | tee REPLAY8_run.txt     # every check asserts its exit code; final TOTAL / UNEXPECTED
```

Clean replay from a fresh copy with no `.lake` output (`~/i8red8-scratch`): **TOTAL=319 UNEXPECTED=0, script exit 0** (`REPLAY8_clean.txt`). Lean axiom audit: i8red7's 162 theorems plus 352 `Vw.*` theorems (all 137 source-declared ones covered; the rest are compiler-generated auxiliaries), only `propext` / `Classical.choice` / `Quot.sound` or none; no `sorry`, `admit`, `native_decide` or `axiom` in the sources.

The runner first runs every i8red7 check (Bend `--verdict`, the trusted Bend→Lean translation, the Lean build and
axiom audit, the exact gate and all earlier mutants, native differential tests, pipegen regeneration). It then runs
the i8red8 sections: the Vw axiom audit, the `.view()` C path, view/APL Lean controls, Bend APL laws and mutants, and
the runtime tests.

## 3. Row matrix: what is actually covered

**Everything in sections 2–6 and 8 is Devin-verified:** it was produced and replayed in the Devin workspace by
`run_i8red8.sh` (log: `REPLAY8_clean.txt`). Section 7 is the only exception.

Legend: **P** = proved in Lean for all admitted inputs; **D** = concrete `decide`-checked Lean example or
counterexample; **R** = finite runtime test; **—** = none / not implemented.

| row | Lean source meaning | Lean lowering ⇒ meaning | Bend | generated C | tested runtime |
|---|---|---|---|---|---|
| byte-pair `.view()` dot, L1, L2, Hamming, one-sided L1 | P (`Pipe` zip/map/fold) | P: `view_chains` → `fusion` → `chain_gate_sound`; dot also `view_dot_gate` (C = APL `+.×`) | actual generated `prog.bend`, `--verdict` (same bytes as gen7) | **yes**: emitted, exact gate PASS | native differential (i8red7 suite, same bytes); i8red7 timings (same bytes) |
| generic `map`, `filter`, `take`, `drop`, `enumerate` | P (list functions) | P: `fused_eq_staged`, exact pull counts `pull_prefix` | — | — | D only |
| `scan` (inclusive: item i is the fold after input i; seed not emitted) | P (`prefixFolds`) | P | — (APL `+\` row only) | — | D |
| finite ordered `flatMap` | P | P | — | — | D |
| `find` / `any` / `all` (stop before the next pull) | P | P: `findRun_val`, `findRun_prefix` (exactly the observed prefix) | — (APL `∧/` row only) | — | D (e.g. `find_pulls` = 2) |
| `chunk k` (stride k, short tail dropped), `window k` (stride 1, short windows omitted) | P (index refs) | P; retained state: chunk < k items, window ≤ k items | — | — | D |
| `distinct` (global, first occurrence) | P (`dedupRef`) | P; retained state: list of all distinct values seen (unbounded) | — | — | R (2000 lists) |
| `sortBy` (stable), `groupBy` (consecutive runs) | **explicit barrier primitives** `List.mergeSort`, `List.splitBy` | barrier kept: segment boundary, materializes all n items (`sort_segments`) | — | — | R vs independent insertion sort / run grouping, fused and unfused |
| `.parallelize(k)` reduce | P (`Mon`: assoc + identity; commutativity separate) | P: `parReduce_eq` (ordered blocks), `parReduceAny_eq` (needs comm) | — | — (no parallel backend) | D refusals |
| pure lambda subset: Int/Bool, `x`, one captured immutable `c`, `+ - * max < = && !`, checked int32 (trap = `none`) | P (`Lam.eval`) | P: `compile_ok` / `lowered_eq` for every expression and all x, c | — | yes, by a **trusted printer** (not proved) | R: 1125 (x, c) edge pairs × 5 lambdas, Lean stack vs eval, C vs eval under gcc/clang/UBSan |
| UTF-8 bytes → Unicode scalars (invalid input rejected, no replacement) | P (`enc1` reference encoder) | P: `dec_encode` (every scalar list), `dec_string` (every Lean `String`); rejection D | — | — | R: `enc1` = `String.toUTF8` on all 1,112,064 scalars; `dec` = `String.fromUTF8?` on 300,000 byte strings |
| APL `M/Y` then `+/` | P (`compress`, right-fold `plusRed`, aligned extents) | P: `compress_sum` (view filter/map/fuse/accumulate) | **P** `mask_sum`, `plus_reduce` | — (model only) | D |
| APL `+\` | P (`scanPlus`: +/ of each prefix) | P: `scan_plus` | **P** `plus_scan` | — (model only) | D |
| APL `∧/` of a pure predicate | P (`andRed`, right fold) | P: `and_all` | **P** `and_reduce` | — (model only) | D |
| APL vector `A +.× B` | P (`ipVec` = `+/ A × B`, LENGTH ERROR on misaligned) | P: `ip_view`, `ip_dot` (= `.loop()` dot meaning and its one-loop IR) | **P** `inner_product` | **yes, via the dot `.view()` path only** (`view_dot_gate`) | as the dot row |
| APL matrix inner-product shape | `ipShape`: contracts left last axis with right first axis | — (shape model only) | — | — | D |

**Runs from the real entry point:** only the five byte-pair `.view()` chains, which go through pipegen, the emitter, the
exact gate and `i8check`. Of the APL rows, only vector `+.×` reaches C, and only through the dot chain, under the
existing int32 contract (admitted bytes, n ≤ 131071, else −1).

**Model-only:** compress + sum, `+\`, `∧/`, matrix shape, all generic Vw adapters, parallel planning, UTF-8 and
sort/group/distinct. The lambda subset has generated C, but its printer is trusted and only differentially tested.

## 4. APL semantics kept explicit

* **Order.** APL `f/` is a right fold. `-/ 10 3 2 = 10-(3-2) = 9`, while the left fold gives `(10-3)-2 = 5`
  (`minus_red_counter`, Lean; `minus_not_left`, Bend inequality). Exact `+` is associative, which is why the
  left-fold loop equals `+/` (`plusRed_eq`; Bend `sumL_acc` uses `add_assoc`).
* **Extents.** `compress`, `ipVec` and `viewZip` return `LENGTH ERROR` on misaligned lengths. A truncating zip is not
  an APL shape check (`zip_truncates`). In Bend, mask/value and A/B pairs are one aligned list type, so misalignment is
  unrepresentable.
* **Axis.** `ipShape [2,3] [3,4] = [2,4]` and `ipShape [2,3] [4,3]` is a `LENGTH ERROR` (`shape_ok`).
* **C overflow.** APL `+.×` on `Int` is exact. The C dot equals it only on the existing admitted domain; above the
  guard it returns −1.

## 5. Fusion, barriers, parallel legality

* **Stateless:** map, filter, enumerate, take/drop counters. Fusion is proved to equal the staged result, in order,
  pulling each item at most once.
* **Stateful but fusible:** scan (one accumulator), chunk (< k buffer), window (k buffer), distinct (seen-set).
  Fusion is proved, and the retained state is stated per adapter. "No extra storage" is not claimed for them.
* **Barriers:** `sortBy` and `groupBy` are named primitives. Lowering ends the fused segment, materializes the
  whole upstream, and starts a new segment. They are never fused across.
* **Refused or failing controls:** over-pull (`overpull_mutant`), last-match find (`findlast_mutant`), restarting
  scan per chunk (`scan_chunk_mutant`), padded chunk tails (`chunk_tail_mutant`), windows cut at chunk boundaries
  (`window_cross_mutant`), take-before-filter (`filter_take_reorder`), adjacent-only distinct
  (`distinct_adjacent_mutant`), subtraction chunking (`sub_chunk_mutant`, `sub_par_refused`), unordered list/string
  concatenation (`app_unordered_refused`, `app_reorder_mutant`), and earliest-find under parallelization
  (`find_par_refused`).
* **Effects:** a staged "map all, then filter all" trace differs from the fused interleaved trace
  (`effect_order_differs`). The fusion theorems are about the results of pure total callbacks. Arbitrary callbacks,
  effects and traps are not claimed equivalent. The lambda subset keeps traps as `none` values, in stream order.

## 6. Bend replay of the APL laws (this branch)

`apl_bend/AplView.bend` is checked by bend 2.0.40 and `--verdict` (BendTT). It contains typed proof defs for
`add_zero`, `add_assoc`, `sumL_acc`, `plus_reduce`, `mask_sum`, `snoc_sum`, `sumR_snoc`, `scan_gen`, `plus_scan`,
`all_false`, `and_reduce`, `dot_acc` and `inner_product`, plus the inequality `minus_not_left`. Six mutants must
be rejected: false reassociation, the false equation 9 = 5, a dropped mask-selected element, an exclusive scan, an
`∧/` that drops the predicate, and a dot product that adds instead of multiplying.

## 7. Historical Mac-only and user-reported results (NOT Devin-verified)

These results come from earlier, separate runs on the user's Mac. They were reported in chat. They were not
produced, replayed or checked in the Devin workspace, and nothing in sections 2–6 depends on them. Under the
execution rule they are not rerun; they are kept as historical, complementary evidence only.

* Bend 2.0.40 + BendTT accepted 10 declarations in the user's `AplLaws.bend`: exact Nat sum, aligned mask plus sum,
  prefix sum, pure Boolean all, vector dot, supporting lemmas, and the counterexample `-/ 10 3 2 = 9` vs left fold 5.
  The checker rejected a false reassociation law and a mutant that dropped a mask-selected element.
* Bend 2.0.40 + BendTT accepted 30 equality laws (including supporting lemmas) and 15 concrete inequalities, and
  rejected all 15 controls made by inverting each counterexample into a false equality.
* Lean 4.15 checked:
  * the ordered- vs commutative-monoid reducer gate, and `allAndFold`;
  * ordered tiling of matrix multiply and of 1D/2D cross-correlation;
  * disjoint row-major output stores;
  * exact signed-INT8 prefix bounds through 131071 terms.
* A handwritten Metal replay on an Apple M2 Pro matched an independent CPU reference on 418 outputs across nine
  cases. It rejected a skip-first-element-per-tile mutant and an ignore-convolution-column-stride mutant.
  No GPU performance or compiler-equivalence claim is made.

## 8. Trusted boundary

The following are trusted, as in i8red7:
* `bend2lean.py`;
* the C-subset model;
* the compilers, ABI and machine code;
* the benchmark harness and the host.

New in i8red8: the lambda C printer and the Lean compiled runtime used by `vwtest` are trusted. The external
references `String.toUTF8` / `String.fromUTF8?` are used only as runtime comparators. Bend APL models are over `Nat`
and are separate from the Lean `Int` models; no translator links them.

## 9. Files

* `bridge/Vw/`: `Machine`, `Adapters`, `Blocks`, `Plan`, `Par`, `Controls`, `Apl`, `Lam`, `Utf8`, `PairView`.
* `bridge/VwAudit.lean`, `bridge/VwTest.lean`, `bridge/PipeGen.lean` (view registry and refusals).
* `apl_bend/AplView.bend` and `apl_bend/neg/*.bend`.
* `view_controls/*.lean`.
* `run_i8red8.sh`, `REPLAY8_clean.txt`, `EVIDENCE_i8red8.txt`.
* i8red7 material is unchanged: `README_i8red7.md`, `gen7/`.
