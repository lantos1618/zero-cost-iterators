# Details

Everything the short README leaves out: the pipeline vocabulary, input formats, exit codes, the theorems, how
the tool is tested, and how to rerun every check. Paths are relative to the repository root.

## The pipeline vocabulary

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

The three pipelines, as written in `bridge/TaskCore.lean`:

| command | pipeline |
|---|---|
| `tasks logsum` | `rs.view.filter (logKeep o) \|>.map toHit \|>.fuse \|>.foldl logS0 logStep` |
| `tasks sales` | `rs.view.filter (saleKeep o) \|>.map saleLine \|>.fuse \|>.groupFold (·.1) agg0 aggStep` |
| `tasks manifest` | `ls.view.enumerate \|>.fuse \|>.find (entryBad tr)` |

Parsing happens before the pipeline and is not covered by the proofs.

## Commands, input formats and exit codes

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

Example `logsum` output (`tasks/fixtures/access.log`):

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

Example `manifest` output (`tasks/fixtures/manifest_bad.txt`, exit status 1):

```text
file: tasks/fixtures/manifest_bad.txt
read: whole file buffered and split into 8 lines before checking
result: INVALID at line 4: path contains '..'
entry: assets/../secret.key 64 0badc0de
```

## What is proved, tested, and not claimed

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

## Rerunning every check

```sh
cp ~/.bend/bend2/base.bend kernels/bendlink/base.bend.pinned   # third-party Bend prelude, not committed
./replay.sh                                                      # several minutes; raw outputs in results/
```

`replay.sh` runs `kernels/replay.sh` (the library and kernel suite) and then the `tasks` checks: build, axiom
audit, no-`sorry` scan, `taskcheck` (generated inputs) and `tasks/replay.sh` (fixtures). It exits 0 only if no
row is unexpected. To check only the CLI fixtures: `(cd bridge && lake build tasks taskcheck) && tasks/replay.sh`.

| needed for | tool or file (not in this repository) |
|---|---|
| the CLI | Lean `leanprover/lean4:v4.15.0` through `elan` (pinned in `bridge/lean-toolchain`); no Lake packages |
| `kernels/replay.sh` | Bend 2.0.40 at `~/.bend/bin/bend`, gcc, clang, python3, about 5 GiB free RAM |
| its Bend-prelude rows | `kernels/bendlink/base.bend.pinned`, a copy of Bend 2.0.40's `~/.bend/bend2/base.bend` |
| two byte-identity rows | earlier private folders `~/i8dot-bend-r5` and `~/i8red6` |
| the old INT8 benchmark (`kernels/bench/`, not rerun) | gcc and a SIFT10K (siftsmall) archive passed as `--dataset FILE`; expected hashes in `kernels/bench/dataset_members.sha256` |

## Benchmarks

No benchmark was run for the CLI. Earlier library benchmarks (synthetic records, n = 200,000, one VM, view time
divided by handwritten-loop time) are reported in `history/README_i8red9.md` §2 and §5, with the raw log in
`history/records/bench_gen_shapes_31x2.txt`: about 0.97–1.00 when the pipeline's `map` only projects fields, and
2.04–2.08 (`foldl`) and 1.30–1.31 (`groupFold`) when the `map` builds a tuple.

## History

`history/` holds the earlier milestone reports and replay transcripts; see `history/README.md`.
