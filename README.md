# `tasks`: everyday file reports from small, proved Lean pipelines

`tasks` is a small command-line tool written in Lean 4. It answers three everyday questions about text files:

- What happened in this access log?
- How much did each product sell?
- Which line of this file manifest is the first bad one?

Each answer is computed by a short chain of steps: keep some rows, reshape them, combine them. The fused chain walks the in-memory
records at most once (the manifest check can stop earlier, and every file has already been read into memory), and
a Lean proof shows that it gives exactly the same answer as running each step on its own.

**Where this lives.** This is a private research project, kept as a local git repository (branch `main`, no
remote) on the Devin VM of this session. Nothing is published, so there is nothing to clone or install. Below,
`ROOT` is the checkout root: on this VM that is `/home/ubuntu/i8red10-git` (the working folder it was staged
from is `/home/ubuntu/i8red10`). All commands below were run by Devin. To check the results without running anything, open the attachment
`REPLAY10_clean.txt` in this session's chat. It is a plain-text transcript of a clean rebuild and every check.

Sections: Example · Quick start · Command reference · What is proved, tested, not claimed · Evidence index.

## Example: sales per product

Input, `tasks/fixtures/sales.csv`:

```text
product,qty,unit_cents,status
apple,3,125,paid
pear,1,240,paid
apple,2,125,refunded
fig,0,999,paid
pear,4,230,paid
apple,1,130,paid
kiwi,5,60,refunded
fig,2,350,paid
pear,1,240,paid
```

Output of `tasks sales tasks/fixtures/sales.csv`:

```text
file: tasks/fixtures/sales.csv
rows: 9 (kept: 7; filter: status=paid min_qty=0)
product,lines,units,revenue_cents,revenue
apple,2,4,505,5.05
pear,3,6,1400,14.00
fig,2,2,700,7.00
TOTAL,7,12,2605,26.05
```

The refunded rows are dropped, so `kiwi` never appears. Products are listed in the order they first appear
(apple, pear, fig) even though their rows are interleaved, and money is integer cents (apple: 3×125 + 1×130 = 505).

The computation, after the CSV has been parsed into a list of `Sale` records (`bridge/TaskCore.lean`):

```lean
sales.view                                                        -- start a pipeline over the list
  |>.filter (fun s => s.status == "paid" && s.qty ≥ o.minQty)     -- keep paid rows
  |>.map    (fun s => (s.product, s.qty, s.qty * s.unitCents))    -- (key, units, line revenue)
  |>.fuse                                                         -- run all steps in one pass
  |>.groupFold (·.1) agg0 aggStep                                 -- one running total per product
```

(In the source the two lambdas are named `saleKeep o` and `saleLine`. `agg0` is the zero total
`{lines, units, cents}`, and `aggStep` adds one row to it.)

**The vocabulary:**
- `xs.view` turns a list into a pipeline description; nothing runs yet. `.filter` and `.map` add steps.
- `.fuse` asks for the steps to run together in a single pass, without building an intermediate list after each
  step.
- `.foldl init step` runs the pipeline and combines the results left to right, in input order. The step does not
  have to be associative.
- `.groupFold key init step` is like `foldl`, but keeps each key and its own running value (accumulator), with keys
  in first-seen order and each key's rows folded in input order. The step you write decides what the accumulator
  holds: here a bounded total, but it could also collect the rows. A key's rows don't have to be adjacent.
- `.enumerate` pairs each item with its index, and `.find p` returns the first item matching `p` and stops there.
- Each terminal returns `Except String _`, which is an error only when a request is refused, for example running
  a step in parallel when that would change the result.

## Quick start

Prerequisite: Lean 4.15.0 through `elan`. It is already installed on this VM in `~/.elan`, and the version is
pinned in `bridge/lean-toolchain`. A build from a clean copy took about 16 s here.

```sh
ROOT=/home/ubuntu/i8red10-git   # the checkout root; change it if the project lives elsewhere
cd "$ROOT/bridge"
export PATH="$HOME/.elan/bin:$PATH"
lake build tasks
cd "$ROOT"
bridge/.lake/build/bin/tasks sales tasks/fixtures/sales.csv
bridge/.lake/build/bin/tasks logsum tasks/fixtures/access.log
status=0; bridge/.lake/build/bin/tasks manifest tasks/fixtures/manifest_bad.txt || status=$?
printf 'exit=%s\n' "$status"; test "$status" -eq 1
```

The build may print a few unused-variable warnings and ends with `Build completed successfully.` The `sales` output is the one shown above. `logsum` prints:

```text
file: tasks/fixtures/access.log
lines: 11 (records: 9, skipped blank/comment: 2)
filter: level=ERROR service=* min_latency_ms=0
matches: 5
total_latency_ms: 2335
max_latency_ms: 900 (first at line 6)
first: line 3 2026-03-01T09:00:05Z api /login
last: line 11 2026-03-01T09:04:00Z api /login
```

The manifest fixture is meant to contain a bad entry, so the last command reports it and **exits with status 1 on
purpose**. The block records that status instead of failing on it, so it also works under `set -e`. Output:

```text
file: tasks/fixtures/manifest_bad.txt
read: whole file buffered and split into 8 lines before checking
result: INVALID at line 4: path contains '..'
entry: assets/../secret.key 64 0badc0de
exit=1
```

Try a filter: `bridge/.lake/build/bin/tasks logsum tasks/fixtures/access.log --service api --min-latency 100`
gives `matches: 2`, `total_latency_ms: 460`.

## Command reference

| command | options | input (every file is read whole into memory; must be valid UTF-8) |
|---|---|---|
| `tasks logsum FILE` | `--level INFO\|WARN\|ERROR` (default `ERROR`), `--service NAME`, `--min-latency N` | lines `TS LEVEL SERVICE LATENCY_MS PATH`, single spaces, 5 fields; latency is decimal digits, read as an arbitrary-precision nonnegative integer; blank lines and `#` lines skipped |
| `tasks sales FILE` | `--min-qty N` (default 0) | header exactly `product,qty,unit_cents,status`; rows of 4 comma-separated fields, no quoting or trimming; `qty` = units sold; `unit_cents` = integer cents per unit; status `paid` or `refunded` (refunded rows are excluded); blank rows skipped |
| `tasks manifest FILE` | `--trace` (prints each validation call to stderr) | lines `PATH SIZE CHECKSUM`; valid iff 3 fields, the path is relative with no `..` or empty segment, the size is decimal with no leading zero (except `0`), and the checksum is 8 lowercase hex digits. Blank lines count as invalid. |

**Report details:**
- **logsum:** count, exact total and maximum latency (with the first line that reached it), and the first and last
  matching entry.
- **sales:** per product, kept rows, units, and revenue in cents and dollars, plus a total line. All filtered gives
  only `TOTAL,0,0,0,0.00`.
- **manifest:** `OK` or the first invalid line with its reason.

| exit | meaning | message |
|---|---|---|
| 0 | success (including manifest all valid) | report on stdout |
| 1 | manifest found an invalid entry | report on stdout |
| 2 | unreadable file or invalid UTF-8; or a log/sales record that does not parse | stderr `FILE: reason` or `FILE:LINE: reason` |
| 64 | usage error (unknown command or flag, missing file argument, bad flag value) | usage text on stderr |

Example of exit 2: `tasks/fixtures/sales_quoted.csv:2: expected 4 comma-separated fields (no quoting), got 5`.
Not supported: quoted CSV (RFC 4180), locales, decimal or floating-point numbers, streaming large files.

## What is proved, what is tested, what is not claimed

**Proved in Lean, about the Lean source:** each of the three pipelines equals a plain step-by-step reference.

| command | theorem (in `bridge/TaskCore.lean`) | built on library theorem |
|---|---|---|
| logsum | `logPipe_spec`: equals filtering the list, then mapping, then a left-to-right `foldl` | `foldl_view_generic` / `push_fold` |
| sales | `salesPipe_spec`: equals an independent stable group-then-fold; `salesPipe_keys`: products appear once each, in first-seen order | `groupFold_view_generic` / `groupFold_correct` |
| manifest | `manifestPipe_spec`: equals `List.find?` on the numbered lines; `entryBad_trace`: tracing doesn't change the answer | `View.find_ok`; `findRun_prefix` gives the exact stopping point in the model |

The library theorems hold for any element and result types and any pure, total Lean callbacks, with no
associativity assumption. The task-level audit covers 29 declarations, all with only Lean's standard axioms and
no `sorry`.

**Runtime-tested only:**
- reading the file, UTF-8 decoding, splitting lines, the log/CSV parsers, the manifest rule as written, and
  report formatting;
- the compiled native binary, since the Lean compiler is trusted, not verified;
- the manifest's early stop in the binary. With `--trace` on `manifest_bad.txt`, exactly 4 validation calls are
  printed and none for lines 5–8, which are deliberately invalid garbage. An eager control on the same file makes
  all 8 calls.

**How:**
- 34 CLI commands are compared byte for byte, stdout, stderr and exit code, against hand-written expected files
  (`tasks/replay.sh`). Exits 0, 1, 2 and 64 all occur.
- 300 generated files per command, from a fixed seed, are compared with independent references written without
  pipelines (`taskcheck`). This includes empty, all-filtered and repeated-key cases.
- Three deliberately broken versions must be caught, and are:
  - a maximum that moves to the last tie;
  - new products inserted at the front;
  - reporting the last invalid manifest line instead of the first.

**Not claimed:**
- That early stopping saves I/O. The whole file is read and split before the pipeline runs; only validation calls
  are skipped.
- Any performance result for these commands; no benchmark was run for them.
- Proofs about parsing or I/O, effectful callbacks, a parallel or GPU backend, or a verified compiler.

## Evidence index

Paths are workspace paths on the Devin VM, relative to the project root; they are not web links. In a browser,
open the files marked (attached) from this session's chat. Everything else is opened in the VM folder.

| what | where |
|---|---|
| Clean rebuild + every check, this tool and the earlier suite (attached) | `REPLAY10_clean.txt`. Results: earlier suite TOTAL=346 UNEXPECTED=0; tool rows 6/6; 34/34 commands; 3×300 generated files, 0 failures. |
| Replay script | `run_i8red10.sh`: runs `run_i8red9.sh` unchanged, then the tool checks |
| Fixtures and hand-written expected outputs | `tasks/fixtures/`, `tasks/expected/`, `tasks/replay.sh` |
| Pipelines, formats, theorems / CLI / generated-input checks / axiom audit | `bridge/TaskCore.lean`, `bridge/Tasks.lean`, `bridge/TaskCheck.lean`, `bridge/TaskAudit.lean` |
| The underlying library: generic `.view()` proofs, `groupFold`, a narrower Bend model, native tests | `README_i8red9.md` (the prior report, unchanged; attached), `EVIDENCE_i8red9.txt`, `REPLAY9_clean.txt` (attached) |
| **Generic prototype benchmarks** (library call sites on synthetic records, not these CLI commands) | `README_i8red9.md` §2 and §5, raw log `records/bench_gen_shapes_31x2.txt`. In short, view time ÷ handwritten time, n = 200,000, one VM: projection call sites 0.97–0.98 (`foldl`) and 0.99–1.00 (`groupFold`); call sites whose `map` builds a tuple 2.04–2.08 and 1.30–1.31. |
| Earlier history: INT8 kernels, stream adapters, APL models, UTF-8, lambda, GPU | `README_i8red8.md` and older `README_i8red*.md` / `REPLAY*_clean.txt`. That README's Mac-only results (the user's Bend runs, Lean tiling, Metal) are historical and not Devin-verified. |
| This README before the newcomer rewrite (it was `README_i8red10.md` in the working folder) | `records/README_i8red10_v1_before_newcomer_rewrite.md` |
| The first zero-cost milestone's README (it was `README.md` before this one replaced it) | `README_v0_zero_cost.md` |

To rebuild everything from a clean copy, in Devin only, use
a new, uniquely named directory each time, so nothing from an earlier run is reused (nothing is deleted):

```sh
fresh=$(mktemp -d "$HOME/i8red10-fresh.XXXXXX")
rsync -a --exclude .lake --exclude 'results_i8red*' "$ROOT/" "$fresh/"
find "$fresh" \( -name .lake -o -name 'results_i8red*' -o -name '*.olean' \) -print   # prints nothing
cd "$fresh" && ./run_i8red10.sh
```

This takes several minutes.

## Dependencies and limits

| needed for | external tool or file (not in this repository) |
|---|---|
| the quick start (`tasks`) | Lean `leanprover/lean4:v4.15.0` via `elan` (pinned in `bridge/lean-toolchain`); no Lake packages (`bridge/lake-manifest.json` is empty) |
| the full replay `run_i8red10.sh` (earlier suite) | Bend 2.0.40 at `~/.bend/bin/bend`; gcc; clang; python3; about 5 GiB free RAM |
| the earlier suite's Bend-prelude rows | `bendlink/base.bend.pinned`, a copy of Bend 2.0.40's prelude `~/.bend/bend2/base.bend`. It is third-party and not committed; create it with `cp ~/.bend/bend2/base.bend "$ROOT/bendlink/base.bend.pinned"` before the full replay |
| the earlier suite's row `pos_C_byteidentical_to_r5` | the older private folder `~/i8dot-bend-r5` on this VM |
| the generic prototype benchmarks (not rerun) | gcc and a SIFT10K (siftsmall) tarball passed as `bench/run_bench.sh --dataset FILE`, not included; `bench/dataset_members.sha256` gives the expected member hashes |

All of these are installed on this VM. Elsewhere, only the quick start is expected to work as written.
Build output (`bridge/.lake/`, `results_i8red*/`) and generated binaries are not committed (see `.gitignore`).
