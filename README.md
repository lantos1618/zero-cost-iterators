# zero-cost-iterators

Chain `filter`, `map`, `take` and `enumerate` over an array or list, then finish with `foldl`, `find?`,
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

Worth it as a small verified library and a precise answer to "is fusion free, and when?". Not worth it as a
performance tool.

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
| `iter/Iter/` | the library: `Basic` (iterators and their proofs), `Group` (`groupFold`), `Cost` (cost model) |
| `iter/` | the `tasks` CLI, its generated-input checker, the axiom audit, `check_c.py`, and the Lean and C++ benchmarks (`Bench.lean`, `bench.cpp`) |
| `tasks/` | CLI fixtures, expected outputs and `replay.sh` |
| `docs/DETAILS.md` | theorem list, cost model, CLI formats and exit codes, limits |

Earlier experiments (the first `.view()` API, INT8 kernels, Bend and APL work) are on the `archive` branch.
