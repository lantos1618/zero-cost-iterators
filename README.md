# zero-cost-iterators

Write a data pipeline as a chain of small steps, run it as one loop, and have Lean prove the loop gives the same
answer as running the steps one after another.

```lean
sales.view
  |>.filter (fun s => s.status == "paid")                     -- keep paid rows (simplified; see bridge/TaskCore.lean)
  |>.map    (fun s => (s.product, s.qty, s.qty * s.unitCents)) -- product, units, revenue
  |>.fuse                                                       -- run every step in a single pass
  |>.groupFold (·.1) agg0 aggStep                               -- one running total per product
```

The repository includes `tasks`, a small command-line tool built on these pipelines. It summarises an access
log, totals sales per product from a CSV, and finds the first bad line in a file manifest.

## Try it

You need Lean 4.15.0 installed through [elan](https://github.com/leanprover/elan). Run from the repository root:

```sh
(cd bridge && lake build tasks)
bridge/.lake/build/bin/tasks sales tasks/fixtures/sales.csv
```

```text
file: tasks/fixtures/sales.csv
rows: 9 (kept: 7; filter: status=paid min_qty=0)
product,lines,units,revenue_cents,revenue
apple,2,4,505,5.05
pear,3,6,1400,14.00
fig,2,2,700,7.00
TOTAL,7,12,2605,26.05
```

Refunded rows are dropped. Products appear in the order they are first seen, and money is kept in whole cents.
The other two commands:

```sh
bridge/.lake/build/bin/tasks logsum tasks/fixtures/access.log
bridge/.lake/build/bin/tasks manifest tasks/fixtures/manifest_bad.txt   # exits 1: line 4 is invalid
```

## What is proved

- **Proved (Lean):** each fused pipeline returns exactly what the step-by-step version returns, for any element
  types and any pure functions. Folds need no associativity. `groupFold` keeps first-seen key order.
- **Tested, not proved:** file reading, the parsers, output formatting and the compiled binary. The tests compare
  against hand-written expected outputs and against 900 generated inputs.
- **Not claimed:** streaming I/O (each file is read whole first), performance of the CLI, and a verified compiler.

## Layout

| path | contents |
|---|---|
| `bridge/` | the Lean project: the `.view()` library, the proofs, and the `tasks` CLI (`TaskCore.lean`, `Tasks.lean`) |
| `tasks/` | CLI fixtures, expected outputs, and `replay.sh` to check them |
| `kernels/` | earlier experiments: INT8 kernels, Bend laws, APL models, and their test suite |
| `docs/DETAILS.md` | input formats, exit codes, the theorem list, and how everything is tested |
| `history/` | earlier milestone reports and raw replay logs |
| `replay.sh` | rebuilds and rechecks everything (needs Bend and C compilers; see `docs/DETAILS.md`) |
