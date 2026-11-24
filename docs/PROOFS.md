# How the proofs work

**Result.** Lean generates a C++ loop for the record summary below and proves it equal to the `Iter` chain.
On rows in random order it is 2.8× faster than a plain hand loop at `g++ -O2` (1.36 vs 3.86 ns per row) and
2.2× at `-O3 -march=native`. On sorted rows it ties `std::views` (1.19 vs 1.19 at `-O2`, 1.21 vs 1.20 at `-O3`)
and beats the hand loop by 1.3× and 2.4×. The C++ printer and GCC are trusted; the printer is fuzzed against Lean.

Measurements: one 8-vCPU VM (Intel Xeon, 2.4 GHz), g++ 11.4, pinned with `taskset -c 2`, 1M rows, median of
11 batches of 20 calls, two rounds. `perf` is blocked on this VM, so every statement about branches below is
inferred from timings on random vs sorted rows, not from hardware counters.

## The problem

```cpp
struct Emp { std::string_view name; u64 salary; bool active; };   // name is a view: no string copies

Summ s;
for (const Emp& e : es)
  if (e.active && e.salary >= minSal) {
    if (s.count == 0) s.first = e.name;
    s.count += 1; s.total += e.salary * pct / 100; s.last = e.name;
  }
```

About 60% of rows are kept. In random order the hand loop takes 3.79 ns per row; with the same rows sorted
(inactive first, then by salary) it takes 1.49. That gap is what a branch-free loop can remove.

The generated loop (`provedA` in `iter/gen/proved_gen.hpp`, printed by `SPipe.toCpp`), abridged:

```cpp
for (; i < n; ++i) { const Emp& e = es[i]; if (KEEP(e)) break; }   // search for the first kept row
if (i == n) return s;
const Emp* fp = &es[i]; const Emp* lp = fp; cnt = 1; tot = PAY(*fp);
for (++i; i < n; ++i) {
  bool k = KEEP(e);
  std::uint64_t m = 0 - (std::uint64_t)k;            // all ones if kept, else 0
  cnt += 1 & m; tot += PAY(e) & m;
  lp = k ? &e : lp;                                  // last kept row
}
```

Every step is legal C++ on `uint64_t`, so a compiler could do it; GCC 11.4 does not. The point is that each
step here is a theorem, and the loop is printed from the pipeline rather than written by hand.

## Step 0: what "the pipeline" means

`Iter.Denotes it l` says the iterator `it` behaves exactly like the list `l`: for every monad, callback and
start value, running `it` gives the same result as a `for` over `l`.

```lean
theorem denotes_array (a : Array α) : a.iter.Denotes a.toList
theorem Denotes.filter (h : it.Denotes l) (p : α → Bool) : (it.filter p).Denotes (l.filter p)
theorem Denotes.map    (h : it.Denotes l) (f : α → β)    : (it.map f).Denotes (l.map f)
theorem Denotes.foldl  (h : it.Denotes l) (init : δ) (step : δ → α → δ) :
    it.foldl init step = l.foldl step init
```

These compose, so the fused chain equals `((xs.toList.filter p).map f).foldl step init`, a list expression
that ordinary algebra can work on.

## Step 1: the mask (`sum_select`, `select_mask`)

```lean
theorem select_mask (b : Bool) (v : UInt64) : (v &&& (0 - if b then 1 else 0)) = if b then v else 0
```

In 64-bit arithmetic `0 - 1` is all ones, so `v & (0 - 1) = v` and `v & 0 = 0`. Proved on `BitVec`, which has
exactly the wrap-around of C++ `uint64_t`. `sum_select` says a filtered sum equals a sum that adds 0 for
dropped items (induction, using `0 + a = a`).

## Step 2: one pass (`step1_filter`)

`SPipe.step1` is the loop body above, in Lean. A row is a `Row`, and `none` plays the role of `nullptr`:

```lean
⟨s.count + (if k then 1 else 0), s.total + sel k pay,
 if k && s.first.isNone then some r else s.first, if k then some r else s.last⟩
```

```lean
theorem step1_filter : l.foldl (q.step1 ps) s =
    ((l.filter keep).map fun r => (r, pay r)).foldl step s
```

**Why:** on a dropped row, `k` is false, so the count adds 0, the total adds `sel false pay = 0`, and first and
last are unchanged: the step does nothing. On a kept row it is exactly the hand loop's step: `first` is set
only if it was empty, `last` is overwritten. **How:** induction on `l`, splitting on `k`, and on whether
`first` is empty.

## Step 3: back to names (`summary_split`, `fast1_correct`)

(`fast1` is the one-pass loop from Step 2 run over all rows; Step 4 turns it into the printed loop.)

The loop tracks rows, the summary reports names. `summary_split` writes any running summary as
`⟨length, sum, head?, getLast?⟩`. Applying it to both sides, the two agree field by field once rows are
mapped to their names (`List.head?_map`, `List.getLast?_map`):

```lean
theorem fast1_correct (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) :
    q.fast1 ps rows = q.run ps rows := by
  rw [SPipe.run, (((denotes_array rows).filter _).map _).foldl, summary_split u64Laws, SPipe.fast1,
    step1_filter]
  simp only [summary_split u64Laws, List.length_map, List.map_map, Function.comp_def, List.head?_map,
    List.getLast?_map, Option.map_map]
```

It holds for every pipeline in the record language and every input. `recPipe_gen` applies it to the
benchmark's pipeline: keep `active != 0 & salary >= p0`, pay `salary * p1 / 100`.

## Step 4: search first (`step1_dropWhile`, `step1_step2`, `fast2_correct`)

`fast2` searches for the first kept row `r` (`dropWhile`), starts the summary at `⟨1, pay r, r, r⟩`, and runs
`step2` (the Step 2 body without the `first` update) over the rest.

- `step1_dropWhile`: `l.foldl step1 s = (l.dropWhile (!keep ·)).foldl step1 s`, because a dropped row is a
  no-op (`step1_drop`, the false case of Step 2).
- `step1_step2`: once `first = some f`, `step1` and `step2` agree, and `step2` keeps `first`. Induction.
- `fast2_correct : q.fast2 ps rows = q.run ps rows`: rewrite with `fast1_correct` and `step1_dropWhile`; the
  first row left is kept (`dropWhile_head`), so one `step1` gives `⟨1, pay r, r, r⟩`, then `step1_step2`.

**Why it helps:** the search loop does no pay arithmetic and has a branch that is predictable when dropped rows
come in a run. On the sorted rows the first 40% are dropped, and the ablation's one-pass loop went from
1.41–1.58 to 1.18–1.23 ns per row. On random rows the first row is usually kept, and nothing changes.

**The word sum** (`opt_correct`) uses the mask plus two more facts: `sum_lanes` (with associative,
commutative `+`, item `j` can go to accumulator `j % k`; proved for `UInt64` via `BitVec`, and impossible
for `Float`, which has no `AddLaws`) and `sum_mul` (`Σ x·c = (Σ x)·c`). It prints 8 lanes, chosen from an
earlier timing; lane count was not ablated for the word sum.

## What the languages can express

| language | items | expressions | tests | shape |
|---|---|---|---|---|
| `Pipe` (words) | one `UInt64`, one parameter `k` | literals, `+ * ^ %` | `== <`, `&` | `filter → map → sum` |
| `SPipe` (records) | word fields, word parameters | literals, `+ * /` | `!= 0`, `>=`, `&` | `filter → map → (count, total, first, last)` |

Nothing else: no `take`, `enumerate` or user functions, no strings in expressions, no other terminals.

## Where the proof stops

| step | status |
|---|---|
| `Iter` chain = list program | proved (`Denotes`) |
| list program = search + masked loop (records), masked multi-lane loop (words) | proved (`fast2_correct`, `opt_correct`) |
| that loop printed as C++ text | **trusted** (`SPipe.toCpp`, `Loop.toCpp`, about 60 lines), **fuzzed** |
| C++ text → machine code | **trusted**: GCC |
| count as `Nat` (Lean) vs `uint64_t` (C++) | agree below 2^64 rows |
| 0 lanes | Lean allows it; the printer emits 1 lane, same sum; covered by the fuzz |
| block search (`provedF`) | proved in Lean, C++ copied by hand, results checked |

Printer details that matter: Lean defines `x / 0 = 0` and `x % 0 = x`, C++ leaves both undefined, so `/` and
`%` are guarded unless the divisor is a nonzero literal. A missing field or parameter prints as `0ULL`, as
Lean reads it. The filter is printed with `&`, never `&&` (measured below: `&&` costs 2×).

**Fuzz** (`iter/FuzzCpp.lean`, rows `fuzz_cpp` and `fuzz_mutant` in `replay.sh`): 300 random word pipelines
with 0–9 lanes and 300 random record pipelines, including division and modulo by zero and missing
fields/parameters, each on inputs of length 0, 1, 5 and all. That is 7,200 results; the C++ is built with
UBSan and its output must equal Lean's `Pipe.run` / `SPipe.run`. A planted bug in the last-row select must
make the comparison fail. By hand, disabling the `/` and `%` zero guards was caught by UBSan. The fuzz
checks the printer, not GCC on the benchmark binary; that binary is checked by `results_equal`.

## What makes it fast (ablation)

`iter/ablate.cpp` checks each variant against `handA` on random and sorted rows, then times it. ns per row,
`g++ -O2`, medians of round 1 / round 2:

| variant | random | sorted |
|---|---|---|
| `handA`: hand loop with `if` and `&&` | 4.24 / 4.00 | 2.02 / 1.51 |
| `hand_amp`: hand loop, `&` instead of `&&` | 4.65 / 4.35 | 2.56 / 1.52 |
| `split_branchy`: count/total pass with `if`, then two searches | 3.58 / 3.58 | 1.55 / 1.47 |
| `split_andand`: masked pass with `&&`, then two searches | 3.61 / 3.53 | 1.52 / 1.47 |
| `split_mask`: masked pass, then two searches (an earlier generated loop, 1 lane) | 1.70 / 1.62 | 2.03 / 1.98 |
| `mask_ct`: the masked count/total pass alone | 1.69 / 1.61 | 1.60 / 1.59 |
| `searches_only`: the two first/last searches alone | 0.00 / 0.00 | 0.38 / 0.38 |
| `provedA` before Step 4 (`fast1`: one pass, earlier run) | 1.40 / 1.47 | 1.41 / 1.58 |
| **`provedA`**: search + one pass, what we generate now | **1.41 / 1.36** | **1.23 / 1.18** |

Batch spread (min–max of 11): `provedA` stayed within 10% of its median; single batches of other rows were up
to 4.7× slower (`handA`, round 1 sorted), which is why medians are reported.

What the table supports:
- **The mask is the gain on random rows**: 3.58 with `if`, 1.61–1.70 with the mask, same structure
  otherwise. Writing the mask with `&&` loses it (3.53–3.61).
- **Extra passes cost on sorted rows.** The masked pass costs the same on both inputs (1.59–1.69). The two
  searches cost nothing on random rows (kept rows sit at both ends) and 0.38 on sorted rows (the first kept row
  is 40% in). `split_mask` ≈ `mask_ct` + `searches_only` on both inputs.
- **Skipping the dropped prefix pays on sorted rows**: the generated loop drops from 1.41–1.58 (one pass) to
  1.18–1.23 (search, then one pass), and is unchanged on random rows.

Not explained, not investigated: why `&` makes the hand loop slower, and why at `-O3 -march=native` the hand
loop takes the same time on sorted and random rows (2.86–2.98). Not measured: rows where the dropped ones sit in
the middle, where `std::views` skips them and ours does not.

## Earlier claims this replaced

The first version of this page credited all four rewrites, and a 4-lane split loop, for a 2.2× gain. The
ablation showed the split and the lanes added nothing or made things worse (4 lanes: 1.82 random, 2.34 sorted,
against 1.66 / 2.13 for 1 lane). That loop is no longer generated; it is in the git history (`651384a`). The one-pass loop that replaced
it (`f74f4e5`) lost to `std::views` on sorted rows; Step 4 is the fix.
