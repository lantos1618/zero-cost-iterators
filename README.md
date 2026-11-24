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

Benchmark, 1,000,000 items, nanoseconds per item:

| pipeline | hand loop | `Iter` chain | eager lists |
|---|---|---|---|
| `filter → map → foldl` on `UInt64` | 1.86 | 2.16 | 30.3 |
| `filter → map → foldl` on records | 8.42 | 8.61 | |
| `enumerate → find?` (no match) | 1.98 | 14.6 | |

Not covered: the cost model is not formally linked to Lean's compiler, and `enumerate` and `take` still allocate
in compiled code (the last row). See `docs/DETAILS.md` for these limits.

## Try it

You need Lean 4.15.0 through [elan](https://github.com/leanprover/elan). From the repository root:

```sh
(cd iter && lake build)
iter/.lake/build/bin/tasks sales tasks/fixtures/sales.csv
./replay.sh        # every proof and check; BENCH=1 ./replay.sh also runs the benchmark
```

`tasks` is a small CLI built on the library. It summarises an access log, totals sales per product and finds
the first bad line in a file manifest.

## Layout

| path | contents |
|---|---|
| `iter/Iter/` | the library: `Basic` (iterators and their proofs), `Group` (`groupFold`), `Cost` (cost model) |
| `iter/` | the `tasks` CLI, its generated-input checker, the axiom audit, the benchmark and `check_c.py` |
| `tasks/` | CLI fixtures, expected outputs and `replay.sh` |
| `docs/DETAILS.md` | theorem list, cost model, CLI formats and exit codes, limits |

Earlier experiments (the first `.view()` API, INT8 kernels, Bend and APL work) are on the `archive` branch.
