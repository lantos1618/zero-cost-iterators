# zero-cost-iterators

Chain `filter`, `map`, `take`, `takeWhile`, `drop`, `dropWhile`, `stride`, `enumerate` and `zip` (with an array) over an
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

## What this is for

A recipe others can copy: state the laws an abstraction must obey, prove that the abstraction equals the
plain program and costs nothing extra in a cost model, then print C++ from the proved form. `Iter` is the
worked example and C++ is the target. Speed is measured to check the method, not as the goal.

1. **Laws.** Give the abstraction a meaning: `Iter.Denotes it l` says iterator `it` behaves as list `l` for
   every lawful monad (state, exceptions, early exit). Each adapter gets one lemma (`Denotes.filter`, ...).
2. **Zero cost, as a theorem.** `iter/Iter/Cost.lean` counts reads, callback calls and intermediate
   allocations, proves a fused chain does no more than the hand loop, and rejects three wasteful versions.
3. **Proved rewrites.** Masks, split accumulators and block switching are lemmas over the list program
   (`opt_correct`, `fast3_correct`), so every rewrite keeps the result.
4. **Print C++ from the proof.** The generator builds C expression trees with a proved meaning and prints them
   with one rule per node; the trusted part is that printer and the compiler, and both are fuzzed.
5. **Try to break it.** Planted bugs must be caught, and `iter/falsify.sh` races the output against
   hand-written C++ under several compilers (below).

To reuse it, write your adapter, prove its `Denotes` lemma and its cost lemma, and the rest composes: each new
pipeline's correctness proof is one line.

## Scorecard

**What is proved** (Lean, standard axioms only; `replay.sh` lists and audits every theorem)

| claim | theorems | status |
|---|---|---|
| every `Iter` chain behaves as its list program, under any lawful monad (state, exceptions, early exit) | `Denotes.*` | proved |
| zero cost, in the cost model: 0 intermediate allocations, ≤ 1 read per item, same callback calls as the staged program; 3 broken versions rejected | `lower_allocs`, `lower_pulls_le`, `lower_calls`, `mut_*` | proved (model only) |
| word `filter → map → sum` = masked multi-lane loop | `opt_correct` | proved |
| word `count`, `min?`, `max?` = masked lane loops | `count_correct`, `red_correct` | proved |
| `x % d == 0` (odd `d`) = `x * inverse(d) < (2^64 - 1) / d + 1`, so the filter has no divide and can vectorise | `nodiv_ok`, `P.nodiv_eval`, `wordPipe_nodiv*` | proved |
| record summary = search + one masked pass | `fast1_correct`, `fast2_correct` | proved |
| record summary = search + any mix of masked and branchy rows, for every switch policy | `fast3_correct` | proved |
| TPC-H Query 6 (five range tests, revenue = Σ price × discount) as a record pipeline; both generated loops equal it | `q6_gen`, `q6_adapt`, `q6_total` | proved |
| the printed C++ loop structure (lanes, rounds, tail, `seen`, search) computes those loops | `printed_correct`, `printed_count`, `printed_red`, `printed_summary`, `printed_adapt` | proved, including the switching loop for every block size, window and threshold |
| `enumerate → find?` = block search (an `any` pass per block, then a scan of the block that hit), for every block size | `printed_find`, `findPipe_gen` | proved |
| the branchy and range-for word printers compute the same loops (so the tuner only changes speed) | `printed_range`, `printed_range_count` (same model as `cRun` for the branchy step) | proved |
| every printed expression (`E`, `P`, `X`, `Q`, masks, min/max identities) is a C syntax tree whose meaning is the Lean value and is never undefined (`/` and `%` by 0 are guarded) | `E.toC_eval`, `P.toC_eval`, `X.toC_eval`, `Q.toC_eval`, `word_step`, `red_step`, `rec_step` (`Iter/CExpr.lean`) | proved |
| tree → text (one fixed rule per node, `CE.print`); each printed loop line means its Lean step | 43,200-result fuzz under UBSan, 3 planted bugs caught | trusted, fuzzed |
| C++ → machine code | — | trusted (GCC) |
| zero cost in Lean's own compiled code | — | measured: holds for `filter → map → fold`; `enumerate`, `drop`, `dropWhile`, `zip` still allocate there (a Lean compiler matter, not our C++) |
| hand-written AVX2 and branch-free baselines | — | comparison code, result-checked only |
| speed; which candidate the tuner picks | — | measured only, below |

**Speed** (ns per item, 1M items, median of 11 batches pinned to one core, GCC 11.4 on one VM; `-O2` /
`-O3 -march=native`; "ours" is the generated loop, the switching one for records)

| pipeline | C++ hand loop | C++ `std::views` | ours | ours vs the faster C++ |
|---|---|---|---|---|
| words: filter → map → sum | 0.76 / 0.77 | 3.32 / 3.40 | **0.57 / 0.55** | 1.3× / 1.4× |
| words: filter → count | 0.38 / 0.39 | 3.15 / 3.19 | 0.39 / 0.42 | tie / 0.93× |
| words: filter → map → max | 3.68 / 3.23 | 3.41 / 3.37 | **0.91 / 0.78** | 3.7× / 4.1× |
| records, random rows | 3.78 / 3.15 | 4.04 / 4.13 | **1.32 / 1.35** | 2.9× / 2.3× |
| records, sorted rows | 1.50 / 2.83 | 1.11 / 1.16 | 1.10 / 1.21 | tie / 0.96× |
| records, dropped runs of 256 | 1.50 / 3.09 | 1.11 / 1.23 | 1.09 / 1.19 | tie |
| records, mixed stretches | 2.68 / 2.94 | 2.64 / 2.51 | **1.22 / 1.18** | 2.2× / 2.1× |
| enumerate → find, no match | 0.30 / 0.29 | 0.30 / 0.30 | 0.30 / **0.22** | tie / 1.3× |

"Ours" for words and search is picked by a tuner: the generator prints every proved candidate (masked or
branchy step, 1/2/4/8 lanes, or one range-for), and `bench.cpp` times them once on a separate sample (same
size and generator, different seed) and keeps the fastest. Because the candidates include the plain
hand-style loop, the tuner can at worst tie it, up to tuning noise. Count at `-O3 -march=native` is still 3–10%
behind across runs: the tuner picks the range-for loop, whose text matches the hand loop, so the remaining gap
is most likely code alignment or noise. Treat differences under about 5% as noise on this VM. The wins
come from branch-free masks where the keep test is unpredictable. Hardware counters are blocked here, so that
cause is inferred from timings.

**From proof to C++**

```
Iter chain ──Denotes──▶ list program ──opt_correct, fast*_correct──▶ fast loop
fast loop ──printed_*──▶ model of the printed loop structure
expressions ──*.toC_eval──▶ C expression tree (CE), never undefined
CE ──CE.print (trusted, 1 rule per node)──▶ C++ text ──GCC (trusted)──▶ machine code
```

Everything left of "trusted" is a Lean theorem. The trusted rest is small and fuzzed: the text rule for each
tree node, that each printed loop line means its Lean step, and GCC.

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

Measured speeds are in the scorecard above; `docs/PROOFS.md` has the batch spreads and the ablations behind
each rewrite. Earlier runs in this README disagreed with each other, so the scorecard is now the only table.

- **"Faster than hand-written C++"** means faster than one plain hand loop. A person can write our loop by
  hand; the difference is that ours is generated and proved.
- **What the languages can express:** word pipelines `filter → map → sum`, `filter → count` and
  `filter → map → min?`/`max?` over the item and one parameter,
  with `+ * ^ %`, `== <` and `&`; record pipelines `filter → map → summary` over word fields and parameters,
  with `+ * /`, `!= 0 >= <` and `&`. No other adapters, no strings, no user functions.
- **Proved vs trusted:** the loops are proved equal to the `Iter` chains (`opt_correct`, `fast2_correct`,
  `fast3_correct`, `count_correct`, `red_correct`). The loop structure the printers emit (lane rounds, inner loop, tail, lane fold, `seen`; the
  record search and masked pass) is modelled loop by loop in `iter/Iter/CLoop.lean` and proved equal too
  (`printed_correct`, `printed_count`, `printed_red`, `printed_summary`, `printed_adapt`). Every printed expression is built as a C syntax tree
  (`iter/Iter/CExpr.lean`) whose meaning is proved equal to the Lean value, with no undefined `/` or `%`
  (`E.toC_eval`, `P.toC_eval`, `X.toC_eval`, `Q.toC_eval`). Still trusted: the tree-to-text rule per node,
  that each printed loop line means its Lean step, and GCC.
  The printers are fuzzed: 43,200 results from random loops (each word pipeline as masked, branchy and range-for sum and count, `min?` and
  `max?`), record ones with random block size, window and switch threshold, compiled with
  UBSan, must match Lean exactly. Planted bugs in the masked and branchy bodies and in the `min` mask must be caught, and inverting
  the switch policy must change nothing. The block
  search is generated too, and `printed_find` proves it for every block size.
- **How the proofs work, and the measurements behind each claim:** [docs/PROOFS.md](docs/PROOFS.md).

## A real workload: TPC-H Query 6

[TPC-H](https://www.tpc.org/tpch/) Query 6 is the standard database benchmark scan: a conjunction of range
tests on one table, the kind of selection Ross (PODS 2002) studied for branchy versus branch-free code:

```sql
SELECT sum(l_extendedprice * l_discount) FROM lineitem
WHERE l_shipdate >= '1994-01-01' AND l_shipdate < '1995-01-01'
  AND l_discount BETWEEN 0.05 AND 0.07 AND l_quantity < 24
```

Written as a record pipeline it is `q6Pipe` in `iter/Iter/Gen.lean`. The only addition to the language was
`<`, with its tree proof in `Q.toC_eval`. `q6_total` proves that the pipeline's total is this sum, and
`q6_gen` and `q6_adapt` prove both generated loops equal it. Each is one line, reusing `fast2_correct` and
`fast3_correct`, which is the recipe working on a query it was not written for.

The data follows dbgen's layout: orders of 1–7 lines, ship date 1–121 days after a random order date,
discount 0–10%, quantity 1–50. About 1.8% of rows pass. It is timed in dbgen's order and sorted by ship date
(a clustered table). Every compiler and flag set in `falsify.sh` checks each loop against the hand loop
first, at the standard parameters, an empty date range, all rows kept, and short inputs.

| build | order | plain hand | branch-free hand | AVX2 hand | ours |
|---|---|---:|---:|---:|---:|
| GCC 11 `-O2` | dbgen | 3.24–3.45 | 1.89–2.00 | – | 1.91–2.05 (tie) |
| GCC 11 `-O2` | by date | 1.81–1.92 | 1.90–2.07 | – | 1.71–1.87 (tie/win) |
| GCC 12 `-O3 -march=native` | dbgen | 3.98–4.34 | 1.99–2.09 | 1.89–1.93 | 2.01–2.17 (**1.06–1.12× slower**) |
| GCC 12 `-O3 -march=native` | by date | 2.26–2.42 | 2.07–2.09 | 1.84–1.92 | 1.78–1.88 (tie/win) |
| clang 15 `-O3 -march=native` | dbgen | 3.66–3.73 | 2.04–2.05 | 2.23–2.27 | **1.92–1.96** |
| clang 15 `-O3 -march=native` | by date | 2.16–2.20 | 2.04–2.18 | 2.26–2.37 | **1.76–1.95** |
| GCC 11 profile-guided | dbgen | 3.41–3.59 | 1.99–2.13 | – | **1.92–2.02** |

ns per row, range over two runs; all builds are in `falsify.sh`'s output.

- **Against the plain hand loop,** the one most people write, ours is 1.7–2.0× faster in dbgen order.
  The five `&&` tests become a mask, and the unpredictable branch goes away.
- **Against a branch-free or AVX2 hand loop,** ours ties or wins, except with GCC `-O3 -march=native` in dbgen
  order, where the hand AVX2 loop is 6–12% faster.
- **Unlike the record benchmark,** the profile-guided build does not regress here.

## How to prove this wrong

Each claim has a cheap test that would break it.

| claim | cheapest way to break it | result |
|---|---|---|
| a chain equals its list program | find a chain and input where they differ: a counterexample would make the Lean proof impossible | `lake build` checks every proof; `replay.sh` audits the 373 theorems for `sorry` and non-standard axioms |
| zero cost in the model | write a wasteful lowering that the cost theorems accept | the 3 planted ones (extra list, double test, no early exit) are rejected |
| zero cost in compiled Lean | time a chain against its hand loop | **already broken** for `enumerate`, `drop`, `dropWhile`, `zip`: Lean boxes the counter (1.2–7× slower); holds for `filter → map → fold` |
| the printed C++ computes what Lean proved | plant a printer bug and see if anything notices | 43,200 fuzz results under UBSan; all 3 planted bugs caught |
| generated C++ is no more than 5% slower than the fastest hand loop: plain `if`, branch-free, and hand-written AVX2 where the build allows it | `sh iter/falsify.sh`: g++ 11 and 12, clang 15, `-O2` and `-O3 -march=native`, and GCC profile-guided builds | **broken in 11–14 of 70 rows** over three runs (below); no wrong results |

`falsify.sh` rows that broke in every run (ns per item; "best hand" is the fastest hand loop, "AVX2" is in
`iter/common.hpp`). A few other rows (count, max, Query 6 at GCC 12 `-O2`) broke by 5–11% in one run and not
the other, which is this VM's noise. In the latest run the search with no match broke at GCC 11 and clang 15 `-O2`
(1.3–1.7× slower) even though GCC 11 emits the same instructions for it as for the hand loop. With
`-falign-functions=64 -falign-loops=64` the gap closes (0.34 vs 0.34 and 0.31 vs 0.30), so it is code
placement, not the generated loop:

| build | pipeline | best hand | ours | ours / best hand |
|---|---|---:|---:|---:|
| GCC 11, profile-guided | records, random | 1.36 (branch-free) | 3.93 | 2.9× slower |
| GCC 11, profile-guided | records, mixed | 1.36 (branch-free) | 2.55 | 1.9× slower |
| GCC 11 and 12 `-O3 -march=native` | max | 0.54–0.60 (AVX2) | 0.66–1.16 | 1.2–1.9× slower |
| GCC 11 and 12 `-O3 -march=native` | sum | 0.39–0.41 (AVX2) | 0.44–0.46 | 1.1× slower |
| clang 15 `-O3 -march=native` | records, random | 1.33 (branch-free) | 1.46 | 1.1× slower |
| GCC 11 and 12 `-O3 -march=native` | TPC-H Query 6, dbgen order | 1.88–1.93 (AVX2) | 1.99–2.17 | 1.06–1.12× slower |

With clang 15 `-O3 -march=native`, ours beats the hand-written AVX2 loop on sum (0.31 vs 0.35), count (0.29
vs 0.32) and max (0.47 vs 0.51). That comes from a new proved rewrite: `x % d == 0` for odd `d` becomes
`x * inverse(d) < (2^64 - 1) / d + 1` (`nodiv_ok`, `P.nodiv_eval`), which has no divide, so the compiler can
vectorise the filter. GCC vectorises it less well, and there the AVX2 loop still wins.

- **Cause of the profile-guided loss:** the profile shows the keep test is taken about 60% of the time, and
  GCC then turns our `lp = kb ? &e : lp` select back into a branch, which mispredicts (checked in the
  assembly).
- **The fix that didn't stick:** a pointer mask in its place fixes the profile-guided build (4.0 → 1.5 ns) but
  costs 15% in normal builds (1.34 → 1.60). It is not applied.
- **What the table shows:** ours beats a *plain* hand loop in most rows, but a programmer who writes the mask
  by hand (`bfA`, `bfMax` in `iter/common.hpp`) gets about the same speed. The proofs make the rewrite safe;
  they do not make it faster than a good hand loop.

## Who already tried this

| idea | prior work |
|---|---|
| fused iterator chains | Haskell stream fusion (Coutts, Leshchinskiy, Stewart, ICFP 2007); Rust iterators; C++20 ranges |
| fused streams generated as C with no overhead | strymonas, "Stream Fusion, to Completeness" (Kiselyov et al., POPL 2017) |
| proved generators that print C with a small trusted printer | Fiat-Crypto (Erbsen et al., IEEE S&P 2019); whole proved compilers: CompCert, CakeML |
| branch-free selection | Ross, "Selection conditions in main memory" (TODS 2004) |
| divisibility by multiplying with the inverse | Granlund and Montgomery (PLDI 1994); Lemire, Kaser, Kurz, "Faster remainder by direct computation" (2019) |
| switching between branchy and branch-free code at run time | Vectorwise micro-adaptivity (Răducanu, Boncz, Zukowski, SIGMOD 2013) |
| schedules that change speed but not results; picking the fastest of equal plans by timing | Halide (Ragan-Kelley et al., PLDI 2013), Exo (Ikarashi et al., PLDI 2022), FFTW's planner |

What is left for this repo: a Lean proof that one law (`Denotes`) covers every adapter under effects and early
exit, zero cost stated as a theorem in a cost model, and a switching loop whose every switching policy is
proved correct. Each part on its own exists elsewhere.

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

Worth it as a small verified library, a precise answer to "is fusion free, and when?", and a worked recipe
for laws → proved zero-cost abstraction → C++. The algebra is well known (see above). What is less common is
a loop that switches strategy on the data with a proof that every switch is correct, so the choice can be
tuned for speed alone. Not worth it as a way to make Lean code fast.

## Status (v1.0)

Finished as a worked recipe. Every C++ loop the benchmarks call "ours" is printed from Lean, and its loop
structure and expressions are proved equal to the `Iter` chain (`printed_*`, `*.toC_eval`). What stays
trusted is the fixed text rule per tree node, that each printed loop line means its Lean step (both fuzzed),
and the C++ compiler. Out of scope, left as open problems:

- a formal C semantics for the printed lines, which would leave only the compiler trusted;
- zero cost in Lean's own compiled code for `enumerate`, `drop`, `dropWhile` and `zip` (needs compiler work);
- user-defined functions and strings in the pipeline language;
- proofs for the hand-written AVX2 baselines, and an ISPC comparison.

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
| `iter/Iter/CExpr.lean` | a small C expression tree (`CE`): 64-bit operators, `?:`, casts; its meaning (`/`, `%` by 0 undefined) and its one-rule-per-node printer |
| `iter/Iter/CLoop.lean` | the printed loops' C++ control flow modelled and proved equal to the proved loops; the printed expression trees proved equal to the Lean values |
| `iter/FuzzCpp.lean` | differential fuzz of the C++ printers against Lean |
| `iter/bench.cpp`, `iter/ablate.cpp` | C++ benchmark (hand, `std::views`, staged, ours) and the record-summary ablation |
| `iter/common.hpp`, `iter/falsify.cpp`, `iter/falsify.sh` | shared C++ workloads (including TPC-H Query 6 rows), plain, branch-free and AVX2 hand loops, timer and tuner; the multi-compiler "prove us wrong" race |
| `iter/` | the `tasks` CLI, its generated-input checker, the axiom audit, `check_c.py`, and the Lean and C++ benchmarks (`Bench.lean`, `bench.cpp`) |
| `tasks/` | CLI fixtures, expected outputs and `replay.sh` |
| `docs/DETAILS.md` | theorem list, cost model, CLI formats and exit codes, limits |
| `docs/PROOFS.md` | how the rewrite proofs work, step by step |

Earlier experiments (the first `.view()` API, INT8 kernels, Bend and APL work) are on the `archive` branch.
