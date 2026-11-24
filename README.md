# zero-cost-iterators

Chain `filter`, `map`, `take`, `takeWhile`, `drop`, `dropWhile`, `enumerate` and `zip` (with an array) over an
array or list, then finish with `foldl`, `find?`, `count`, `any`, `all`, `contains`, `min?`, `max?`,
`groupFold` or a plain `for` loop. The chain runs as one loop with no intermediate lists, and Lean proves it
computes exactly what the step-by-step list program computes.

```lean
import Iter

def paidRevenue (sales : Array Sale) : Nat :=
  sales.iter
    |>.filter (·.paid)
    |>.map (fun s => s.qty * s.unitCents)
    |>.foldl 0 (· + ·)

-- the proof is the same chain, written with the matching lemmas
example (sales : Array Sale) :
    paidRevenue sales = ((sales.toList.filter (·.paid)).map (fun s => s.qty * s.unitCents)).foldl (· + ·) 0 :=
  (((Iter.denotes_array sales).filter _).map _).foldl _ _
```

Callbacks can have effects. This loop keeps a symbol table and throws at the first duplicate; `Denotes.forIn`
proves it behaves exactly like the same `for` loop over the filtered list, including where it stops:

```lean
def declare (names : Array String) : Except String (List String) := do
  let mut table : List String := []
  for n in names.iter.filter (· != "_") do
    if table.contains n then throw s!"duplicate {n}"
    table := n :: table
  return table
```

## What "zero cost" means here

| claim | how it is established |
|---|---|
| a chain computes the staged list program, in any lawful monad, including early exit | Lean theorems, `iter/Iter/Basic.lean` |
| in a cost model: same result, **0 intermediate allocations**, at most one read per item, and exactly the staged program's callback calls | Lean theorems, `iter/Iter/Cost.lean` |
| three wasteful versions that give the same answers are rejected by their costs | Lean theorems, `iter/Iter/Cost.lean` |
| the C Lean emits for `filter`/`map`/`foldl` chains has no closures, no indirect calls and no more allocation sites than a hand-written loop | script over the emitted C, `iter/check_c.py` |
| speed against a hand-written loop | one benchmark on one VM (below) |

Benchmark: 1,000,000 items, the same data in both languages, nanoseconds per item. "Fused" is `Iter` in Lean
and a lazy `std::views` chain in C++; "staged" builds a new list or vector after every step.

| pipeline | Lean hand | Lean fused | Lean staged | C++ hand | C++ fused | C++ staged |
|---|---|---|---|---|---|---|
| `filter → map → fold` on 64-bit words | 1.86 | 2.16 | 30.3 | 0.78 | 3.51 | 4.19 |
| `filter → map → fold` on records | 8.42 | 8.61 | | 3.99 | 4.30 | 26.2 |
| `enumerate → find` (no match) | 1.98 | 14.6 | | 0.35 | 0.50 | 2.02 |

Lean 4.15 (its bundled clang) and g++ 11.4 `-O2 -std=c++20`, one 8-core VM, median of 5 batches of 20 calls.
Every variant returns the same checksum.

Not covered: the cost model is not formally linked to Lean's compiler, and `enumerate` and `take` still allocate
in compiled code (the last row). See `docs/DETAILS.md` for these limits.

## Beating C++: proved rewrites, pulled into C++

Lean is the prover, C++ the target. `iter/Iter/Gen.lean` turns two small pipeline languages into C++ loops and
proves each loop equal to the `Iter` chain; `iter/Iter/Rewrite.lean` holds the rewrites they use:

- `sum_select`, `select_mask`: the filter becomes a branch-free mask, `acc += v & -(keep ? 1 : 0)`;
- `sum_lanes`: `+` on 64-bit words is associative and commutative, so a sum can use `k` independent accumulators;
- `sum_mul`: `map (· * 2)` before a sum is one multiplication after it;
- `step1_filter`, `step1_dropWhile`, `step1_step2`, `summary_split`: a running (count, total, first, last)
  summary is a search for the first kept row, then one pass with masked count and total and `last` as a
  pointer select;
- `stepB_step2`, `foldl_mix`, `fast3_correct`: after the first kept row, any mix of the masked body and an
  ordinary branchy body, chosen per row in any way, gives the same summary. The printed loop picks per block
  of 256 rows from how often the keep test flipped, so it can follow the data;
- `find_blocks`: a search can test a block of 32 for "any match" without branching.

ns per item, 1,000,000 items, median of 11 batches (batch min–max in [docs/PROOFS.md](docs/PROOFS.md)):

| pipeline | data | `-O2`: hand | views | **ours** | `-O3 -march=native`: hand | views | **ours** |
|---|---|---|---|---|---|---|---|
| filter → map → sum, words | random | 1.30* | 3.21 | **0.68** | 0.80 | 3.46 | **0.60** |
| filter → map → summary, records‡ | random | 3.75 | 4.00 | **1.33** | 3.34 | 4.13 | **1.28** |
| filter → map → summary, records‡ | sorted | 1.51 | 1.14 | 1.15 | 2.87 | 1.08 | 1.06 |
| filter → map → summary, records‡ | runs† | 1.49 | 1.13 | 1.12 | 2.87 | 1.08 | 1.05 |
| filter → map → summary, records‡ | mixed† | 2.71 | 2.67 | **1.25** | 2.91 | 2.66 | **1.18** |
| enumerate → find, no match | random | 0.48 | **0.31** | 0.55 | 0.32 | 0.33 | **0.25** |

"hand" is a plain C++ `for` loop with `if`, "views" is `std::views::filter | transform`, both g++ 11.4, on
one VM pinned to one core, second of two rounds. Every variant returns the same results. *This batch was
noisy (min 1.09); round 1 gave 0.78. †"runs": runs of 256 rows, all kept or all dropped, spread through the
array; "mixed": 65,536-row stretches that alternate between random rows and runs. ‡Records rows are from a
later run, round 1 (in round 2 the VM slowed every `-O2` loop by 10–20%; the order did not change); "ours" is
the switching loop `adaptA`. Unbolded rows are ties within the noise.

- **Records, random order:** ours is 2.6–2.8× faster than the hand loop and 3.0–3.2× faster than `std::views`.
  The ablation shows the gain is the branch-free mask (the hand loop's `if` is taken for ~60% of rows in random
  order).
- **Records, sorted and runs:** a tie with `std::views` (1.12–1.15 vs 1.13–1.14 at `-O2`). When the keep test
  is predictable the switching loop runs the branchy body, which is the `std::views` loop. The masked-only loop
  (`provedA`, still generated) loses here: 1.32 vs 1.13 on runs.
- **Records, mixed:** ours is 2.1–2.3× faster than both. No fixed loop wins here: the masked loop is right for
  the random stretches and the branchy one for the runs; the masked-only loop reads 1.34 and 1.29.
- **What the switch costs:** within noise on random rows (1.33 vs 1.32 for masked-only). Prototypes that
  counted flips on every row cost 5–15%; counting over the first 32 rows of a masked block, and only on kept
  rows in a branchy block, is what made it free. At `-O3` GCC turned the branchy block back into selects
  (1.93 ns on runs); the printed `optimize("no-tree-loop-if-convert")` attribute stops that (1.22).
- **Words:** 1.1–1.3× over the hand loop. **Search:** a loss at `-O2`, a win at `-O3`.
- **"Faster than hand-written C++"** means faster than one plain hand loop. A person can write our loop by
  hand; the difference is that ours is generated and proved.
- **What the languages can express:** word pipelines `filter → map → sum` over the item and one parameter,
  with `+ * ^ %`, `== <` and `&`; record pipelines `filter → map → summary` over word fields and parameters,
  with `+ * /`, `!= 0 >=` and `&`. No other adapters, no strings, no user functions.
- **Proved vs trusted:** the loops are proved equal to the `Iter` chains (`opt_correct`, `fast2_correct`,
  `fast3_correct`). The C++ printers (about 100 lines) and GCC are trusted. The printers are fuzzed: 10,800
  results from 900 random loops, record ones with random block size, window and switch threshold, compiled with
  UBSan, must match Lean exactly. Planted bugs in the masked and branchy bodies must be caught, and inverting
  the switch policy must change nothing. The block
  search is still copied by hand and only result-checked.
- **How the proofs work, and the measurements behind each claim:** [docs/PROOFS.md](docs/PROOFS.md).

## Was this worth doing?

Partly. Honest accounting:

- **What it delivers.** Fusion is a theorem, not a hope: any `map`/`filter`/`take`/`enumerate` chain, in any
  lawful monad, with early exit, equals the step-by-step list program. The proof pattern (`Denotes`) is about
  200 lines and composes, so each new pipeline's correctness proof is one line.
- **Zero cost, for the common case.** A `filter → map → fold` chain compiles to the same loop a person would
  write in Lean: within 0–16% of the hand loop, and 14× faster than staged lists. In C++ the equivalent
  `std::views` chain was 4.5× slower than its hand loop on the same row: GCC turns the hand loop's `if` into a
  branch-free select (`cmov`) but keeps an unpredictable branch inside the view (checked in the assembly).
  Fused iterators are not free in C++ either.
- **What it does not deliver.** The zero-cost theorem is about a model; the compiled-code evidence is a script
  and a benchmark. `enumerate` costs 7× a hand loop. Lean itself is 2–20× slower than C++ on these loops,
  mostly from boxed array elements, reference counting and arbitrary-precision indices. So this is no
  reason to move hot loops from C++ to Lean.
- **The original question.** The C++ loop that started this already makes one pass, mutates a symbol table and
  throws at the first duplicate. Fusion has nothing to remove there, so it was right not to change it.
  `Denotes.forIn` now proves that writing such a loop as a chain would keep its behaviour, including where it
  stops, but there is no speed reason to.
- **Cost of getting here.** Most of the earlier work (INT8 kernels, Bend, APL, ten milestone reports) did not
  move this goal forward. It is now on the `archive` branch.

Worth it as a small verified library, a precise answer to "is fusion free, and when?", and a source of
proved loops printed as C++: on the record summary 2.6–3.2× faster than a hand loop and `std::views` in random
order, 2.1–2.3× faster than both on mixed data, and tied with `std::views` on sorted data and runs; 1.1–1.3×
faster on the word sum. The algebra is well known. What is less common is a loop that switches strategy on the
data with a proof that every switch is correct, so the choice can be tuned for speed alone. Not worth it as a way to make Lean code fast.

## Try it

You need Lean 4.15.0 through [elan](https://github.com/leanprover/elan). From the repository root:

```sh
(cd iter && lake build)
iter/.lake/build/bin/tasks sales tasks/fixtures/sales.csv
./replay.sh        # every proof and check; BENCH=1 ./replay.sh also runs both benchmarks (needs g++)
```

`tasks` is a small CLI built on the library. It summarises an access log, totals sales per product and finds
the first bad line in a file manifest.

## Layout

| path | contents |
|---|---|
| `iter/Iter/` | the library: `Basic` (iterators and their proofs), `More` (more adapters, `zip`, terminals), `Group` (`groupFold`), `Cost` (cost model), `Rewrite` (proved loop rewrites) |
| `iter/Iter/Gen.lean`, `iter/GenCpp.lean`, `iter/gen/` | proved word and record loop generators, their C++ printers, and the generated header |
| `iter/FuzzCpp.lean` | differential fuzz of the C++ printers against Lean |
| `iter/bench.cpp`, `iter/ablate.cpp` | C++ benchmark (hand, `std::views`, staged, ours) and the record-summary ablation |
| `iter/` | the `tasks` CLI, its generated-input checker, the axiom audit, `check_c.py`, and the Lean and C++ benchmarks (`Bench.lean`, `bench.cpp`) |
| `tasks/` | CLI fixtures, expected outputs and `replay.sh` |
| `docs/DETAILS.md` | theorem list, cost model, CLI formats and exit codes, limits |
| `docs/PROOFS.md` | how the rewrite proofs work, step by step |

Earlier experiments (the first `.view()` API, INT8 kernels, Bend and APL work) are on the `archive` branch.
