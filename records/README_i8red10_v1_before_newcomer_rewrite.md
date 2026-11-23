# i8red10: everyday file tasks on the generic typed `.view()`

i8red10 = i8red9 (unchanged, replayed in full) + one native CLI, `tasks`, with three file-driven commands whose
computation is a real `.view()` call site through the reusable View API and its generic lowering. Parsing, file
I/O and output formatting sit outside the fusion theorem and are runtime-tested only.

## Everyday tasks

Build and run (Devin workspace only):

```sh
cd bridge && lake build TaskCore tasks taskcheck && cd ..
bridge/.lake/build/bin/tasks logsum   tasks/fixtures/access.log [--level INFO|WARN|ERROR] [--service NAME] [--min-latency N]
bridge/.lake/build/bin/tasks sales    tasks/fixtures/sales.csv  [--min-qty N]
bridge/.lake/build/bin/tasks manifest tasks/fixtures/manifest_bad.txt [--trace]
```

**Exit codes:** 0 ok · 1 manifest has an invalid entry · 2 unreadable file, invalid UTF-8, or log/sales record
parse error · 64 usage error. Read/UTF-8 errors print `FILE: reason`; record parse errors print
`FILE:LINE: reason` on stderr and nothing on stdout. An invalid manifest entry is a *result* (exit 1), not a parse
error.

**File reading (all commands):** `readBinFile` reads the whole file into memory, strict `String.fromUTF8?`
decodes it (invalid UTF-8 → exit 2, nothing replaced), and it is split on `\n` (a trailing `\r` is removed)
before any view runs. No command streams from disk.

### 1. `logsum`: access-log summary (`.filter/.map/.fuse/.foldl`)

Format: one record per line, `TS LEVEL SERVICE LATENCY_MS PATH`, single spaces, exactly 5 fields;
`LEVEL ∈ {INFO, WARN, ERROR}`; `LATENCY_MS` decimal digits (unbounded `Nat`, exact). Empty lines and lines
starting with `#` are skipped. Kept: `level = --level` (default ERROR) ∧ (`service = --service` if given) ∧
`latency ≥ --min-latency` (default 0). The max reports the first line that reached it.

```lean
rs.view.filter (logKeep o) |>.map toHit |>.fuse |>.foldl logS0 logStep      -- TaskCore.lean, logPipe
```

```text
$ tasks logsum tasks/fixtures/access.log                      # exit 0
file: tasks/fixtures/access.log
lines: 11 (records: 9, skipped blank/comment: 2)
filter: level=ERROR service=* min_latency_ms=0
matches: 5
total_latency_ms: 2335
max_latency_ms: 900 (first at line 6)
first: line 3 2026-03-01T09:00:05Z api /login
last: line 11 2026-03-01T09:04:00Z api /login
$ tasks logsum tasks/fixtures/bad_level.log                   # exit 2
tasks/fixtures/bad_level.log:2: level must be INFO, WARN or ERROR, got 'ERR'
```

Edge cases in the replay: `--service api --min-latency 100` (2 matches), `--level WARN`, no match
(`max_latency_ms: none`), empty file, a latency of 2^64−1 plus 1 giving total `18446744073709551616` exactly,
fractional latency `3.5` (exit 2), missing file and invalid UTF-8 (exit 2), bad flag values (exit 64).

### 2. `sales`: sales by product (`.filter/.map/.fuse/.groupFold`)

Dialect: first line exactly `product,qty,unit_cents,status`; every data line has exactly 4 comma-separated fields,
**no quoting or escaping, no trimming**; `product` non-empty; `qty` = units sold (decimal digits, may be 0);
`unit_cents` = integer cents per unit; `status ∈ {paid, refunded}`; empty data lines skipped. Kept:
`status = paid ∧ qty ≥ --min-qty` (default 0). Per product: lines kept, units = Σ qty, revenue = Σ qty·unit_cents.
Products appear in first-seen order among kept rows. Not supported: RFC 4180 quoting, locales, decimals/floats.

```lean
rs.view.filter (saleKeep o) |>.map saleLine |>.fuse |>.groupFold (·.1) agg0 aggStep   -- TaskCore.lean, salesPipe
```

```text
$ tasks sales tasks/fixtures/sales.csv                        # exit 0
file: tasks/fixtures/sales.csv
rows: 9 (kept: 7; filter: status=paid min_qty=0)
product,lines,units,revenue_cents,revenue
apple,2,4,505,5.05
pear,3,6,1400,14.00
fig,2,2,700,7.00
TOTAL,7,12,2605,26.05
$ tasks sales tasks/fixtures/sales_quoted.csv                 # exit 2
tasks/fixtures/sales_quoted.csv:2: expected 4 comma-separated fields (no quoting), got 5
```

`apple` (lines 2, 4, 7), `pear` (3, 6, 10) and `fig` (5, 9) are interleaved; the refunded `apple` row and the
refunded `kiwi` row are filtered out, so `kiwi` never appears; `fig,0,...` counts a line with 0 units. Edge cases
in the replay: `--min-qty 2`, `--min-qty 4` (one key), `--min-qty 100` (all filtered: only `TOTAL,0,0,0,0.00`),
header-only file, empty file / missing header / `qty -1` / quoted field (exit 2), unknown flag (exit 64).

### 3. `manifest`: first invalid entry (`.enumerate/.fuse/.find`)

Format: `PATH SIZE CHECKSUM`, single spaces. A line is valid iff it has exactly 3 fields; `PATH` does not start
with `/`, has no `..` segment and no empty segment; `SIZE` is decimal digits with no leading zero (except `0`);
`CHECKSUM` is exactly 8 lowercase hex digits. Every raw line, including blank ones, is checked; lines are not
pre-parsed, so a malformed suffix cannot fail before `find` runs.

```lean
ls.view.enumerate |>.fuse |>.find (entryBad tr)       -- TaskCore.lean, manifestPipe; entryBad = (checkEntry l).isSome
```

```text
$ tasks manifest tasks/fixtures/manifest_bad.txt --trace      # exit 1
file: tasks/fixtures/manifest_bad.txt
read: whole file buffered and split into 8 lines before checking
result: INVALID at line 4: path contains '..'
entry: assets/../secret.key 64 0badc0de
trace: pred line 1                                             (stderr)
trace: pred line 2
trace: pred line 3
trace: pred line 4
trace: model findPulls=4 (untraced recount); lines buffered before find=8
```

Lines 5–8 of that fixture are valid UTF-8 but invalid entries (`DEADBEEF`, a `☃ ünïcödé` garbage line,
`/etc/passwd`, `x`). The native `--trace` run shows exactly 4 predicate calls and none after line 4. An eager
control (`taskcheck eager`) runs the same traced predicate over every line first, then picks the first `true`. It
prints 8 calls and the same answer, line 4, which shows the fixture separates eager from short-circuit behaviour.
**What stops early is the predicate, not the I/O:** the whole file was already read and split into 8 lines.

Other cases: all-valid file (exit 0, 4 calls), invalid first line (`007`, 1 call), blank line 2 (`expected 3
space-separated fields, got 1`), empty file (exit 0, 0 entries), invalid UTF-8 (exit 2).

### Verification

- **Golden fixtures:** `tasks/fixtures/*` and the hand-written expected stdout/stderr in `tasks/expected/*`.
  `tasks/replay.sh` runs 34 commands and compares stdout, stderr and the exit code byte for byte; exits 0, 1, 2
  and 64 all occur.
- **Fixed-seed reference comparison** (`taskcheck`, seed 20261122, 300 generated files per task). Each file is
  rendered to text, parsed, run through the CLI pipeline, and compared with an independent reference written
  without `.view()`:
  - log: a direct recursive summary; 65 empty, 183 zero-match;
  - sales: a stable insert-at-end association list; 53 empty, 116 all-filtered, 157 with repeated keys;
  - manifest: `findIdx?` with exact pull count = first invalid index + 1, or line count when all valid; 192 invalid,
    108 valid.
- **Mutants that must be caught:** a max that moves to the last tie (caught 11 times), groupFold inserting new keys
  at the front (174), and "last invalid entry" instead of the first (123).

### Theorem coverage and trust boundary per row

| row | proved about the Lean source (TaskCore audit: 29 declarations including the 5 named here, standard axioms only, no `sorry`) | runtime-tested only |
|---|---|---|
| logsum | `logPipe_spec`: the call site = staged `(rs.filter keep).map toHit` then `foldl logStep logS0`, via the existing `foldl_view_generic`/`push_fold` | file read, UTF-8, line split, record parser, report formatting, native binary |
| sales | `salesPipe_spec`: = `groupRef` (stable group-then-fold) of the staged list, via `groupFold_view_generic`/`groupFold_correct`; `salesPipe_keys`: output keys = kept products deduplicated in first-seen order | the same, plus CSV dialect and cents formatting |
| manifest | `manifestPipe_spec`: = `ls.enum.find? entryBad`, via the existing `View.find_ok`; the existing `findRun_prefix` makes `findPulls` the exact stopping point in the model; `entryBad_trace`: the traced predicate has the same Boolean value as the untraced one | file read and split, `checkEntry` rule as written (no spec beyond its code), formatting, and the native call count, observed through `dbgTrace` on stderr |

No new lowering was added: the three call sites use the existing `filter`/`map`/`enumerate`/`fuse`/`foldl`/
`groupFold`/`find`, so no new law or control was needed. Not claimed: parser or I/O proofs, streaming reads,
large-file performance, any benchmark (none was run for i8red10), a verified compiler.

### Replay (Devin-only)

```sh
rsync -a --exclude .lake --exclude 'results_i8red*' ~/i8red10/ fresh/ && cd fresh && ./run_i8red10.sh
```

`run_i8red10.sh` first runs the unchanged `run_i8red9.sh`, then the task rows: build, TaskCore audit, theorem list,
no-sorry scan, `taskcheck`, and `tasks/replay.sh`. Fresh-copy result: the i8red9 suite TOTAL=346 UNEXPECTED=0; the task rows TOTAL=6 UNEXPECTED=0 (34/34 fixture commands, 3×300 generated inputs with 0 fails, every mutant caught, TaskCore audit 29 declarations with standard axioms only); script exit 0. The transcript is
`REPLAY10_clean.txt`. Files: `bridge/TaskCore.lean` (formats, pipelines, theorems), `bridge/Tasks.lean`
(CLI), `bridge/TaskCheck.lean` (references, generator, mutants, eager control), `bridge/TaskAudit.lean`,
`tasks/`, `run_i8red10.sh`.

---

# (carried from i8red9) i8red9: a generic typed `.view()` with user-defined procedures, and a stable `groupFold`

**Opening claim.** For any source, intermediate and accumulator types and any pure total `map`, `filter`, key and
step callbacks (immutable captures included), the fused `.view()` `foldl` and `groupFold` return exactly the staged
results, in source order, with no associativity assumption. The proof covers the Lean source definitions of the
supported adapters (`map`, `filter`) followed by `foldl` or `groupFold`; `groupFold` needs decidable key equality
and returns keys in first-seen order. The compiled binary is tested, not proved.

**Measured, separately.** On one Devin VM (n = 200,000 String-bearing records, 16 keys, association-list table,
callbacks written at the call site), the projection call sites took 0.97–0.98× (`foldl`) and 0.99–1.00×
(`groupFold`) the time of matching handwritten loops. When the user's `map` builds a tuple, the same tasks took
2.04–2.08× and 1.30–1.31× the time of the equivalent projecting handwritten loop.

## 1. What you write

```lean
structure Emp  where name : String; dept : String; salary : Nat; active : Bool     -- your record
structure Summ where count : Nat; total : Nat; first : String; last : String        -- your accumulator

-- ordered foldl into a different accumulator type; minSal and pct are runtime captures
es.view.filter (fun e => e.active && e.salary ≥ minSal) |>.fuse
  |>.foldl s0 (fun s e => ⟨s.count + 1, s.total + e.salary * pct / 100,
                          if s.count = 0 then e.name else s.first, e.name⟩)

-- groupFold: one accumulator per String key, items folded in original order, keys in first-seen order
es.view.filter (fun e => e.active && e.salary ≥ minSal) |>.fuse
  |>.groupFold (·.dept) s0 (fun s e => ⟨s.count + 1, s.total + e.salary * pct / 100,
                                       if s.count = 0 then e.name else s.first, e.name⟩)

-- the same, with a map stage that builds a tuple (supported; slower, see the table)
es.view.filter (fun e => e.active && e.salary ≥ minSal)
  |>.map (fun e => (e.dept, e.name, e.salary * pct / 100)) |>.fuse
  |>.groupFold (·.1) s0 (fun s r => summStep s r.2)
```

A non-associative String step shows that order is preserved:
`groupFold key "" (acc ↦ "[" ++ acc ++ "|" ++ label ++ "]")` over keys `a b a c b a` with labels `1 2 3 4 5 6`
gives `[("a","[[[|1]|3]|6]"), ("b","[[|2]|5]"), ("c","[|4]")]`.

| operation | returns | state kept while scanning |
|---|---|---|
| `groupFold(key, init, step)` | one accumulator per distinct key, keys in first-seen order | every distinct key plus its accumulator, whose size you choose |
| full `groupBy` | every member, grouped | all items, O(n) |
| adjacent runs | one group per maximal run of equal keys | the current run |

Adjacent runs split `a b a` into three groups, so they are not `groupFold` (control `adjacent_differs`).

## 2. Results

Every ratio is **view time ÷ handwritten time** (median of 31 rounds, run 1 / run 2). Below 1 means the view was faster.

| comparison | baseline (handwritten) | `foldl` | `groupFold` |
|---|---|---|---|
| projection call site | matching projecting loop, same table | 0.973 / 0.978 | 0.989 / 1.001 |
| map-built tuple call site | equivalent projecting loop (stronger baseline) | 2.04 / 2.08 | 1.30 / 1.31 |
| map-built tuple call site, user step marked `@[inline]` | equivalent projecting loop | 0.980 / 0.997 | 1.34 / 1.32 |

**What the tuple rows show, and what they don't.**
- **`foldl`, an end-to-end gap:** the tuple row differs from its baseline in two ways. The pair is allocated, and
  the user step is called out of line. Inlining the step closes the gap (0.98–1.00). Its emitted loop then has no
  step call and the same 2 constructor sites as the projection call site. These variants cannot separate the two
  causes.
- **`groupFold`, a gap that inlining doesn't close:** the gap stays with the step inlined. That outer loop still has
  3 constructor sites per accepted record before the recursive table insert. The projection call site's outer loop
  has none, and it is at parity. This fits the payload tuple, but key access also differs (`.1` vs `.dept`), so it is reported as an
  observed gap, not a proven cause.
- **No negative cost:** a handwritten twin that builds the same tuple ran slower than the view on `groupFold`
  (0.82–0.83, §5). That twin's insert and step are compiled differently, so the result is a weak baseline, not
  evidence of negative abstraction cost.

**What changed to get here, by kind:**
- **Generic library specialization, every call site:** the view composes `map`/`filter` into one inlineable closure,
  proved equal to the proof-side lowering. The adapters and terminals are inlined. The `groupFold` insert is
  specialized and evaluates the key once per item, proved equal. All six specialized loops have no `lean_apply` and
  no closure allocation; a name-based scan of the emitted C checks this.
- **Call-site rewrite by the user:** projecting fields in the key and reducer, instead of mapping to a tuple.

## 3. Scope: what the theorem does not cover

- **Effects, traps, opaque callbacks:** outside the theorem. Lean callbacks here are pure total functions. The fused
  path calls them in source order, at most once per item. It interleaves stages where the staged path does not, so
  effect equivalence is not claimed.
- **Dynamic callbacks:** a closure chosen at run time is still correct under the theorem. It was not measured, and it
  would fall back to an indirect call per element.
- **Parallel `foldl`/`groupFold`:** refused (`groupFold_refused`; native run). There is no lawful per-key chunk
  summary, and no parallel backend exists. Chunk-then-merge is proved lawful for a separator join and wrong for the
  bracket step, so refusal is a default, not a claim that every step is illegal.
- **Other adapters:** the generic proof covers `map`/`filter` → `foldl`/`groupFold` only. `take`, `find`, `window`,
  `sortBy` and the rest keep their i8red8 status.
- **Not claimed:** "zero cost for any procedure", performance beyond this host and workload, a verified Lean
  compiler or C toolchain, floating point, or a parallel/GPU backend.

## 4. Evidence: proofs and checks

**Lean 4.15, standard axioms only:**
- `Chain.push_fold`: for all `c xs k b`, `xs.foldl (c.push k) b = (c.ref xs).foldl k b`. Here `c.ref` is the
  independent staged list semantics, and `c.push` is one `foldl` over the source with no intermediate list.
- `View.foldPath_eq` ties it to the actual `View.foldl`. The executable closure `PP.run` is proved equal to `c.push`
  by `PP.hrun`.
- `push_trace` (order), `push_one` (each item reaches the terminal at most once) and `push_fold_capture`.
- `groupFold_correct` (equals `groupRef`, an independent stable group-then-fold), `groupFold_state` (first-seen key
  order), `groupFold_ok` (the actual `View.groupFold`), and `gInsK_eq` (key evaluated once, equal to `gIns`).
- **Controls in Lean:**
  - interleaved String fixture, empty input and all-filtered input;
  - proved differences for reset, front-insert, adjacent-run and reversed-source mutants;
  - 7 false claims rejected: reset, front, adjacent, parallel accepted, lawful bracket chunking, reassociation,
    swapped stages.

**Bend 2.0.40 (an independent, narrower model, not linked to Lean):**
- **Domain:** three keys, payload of any `Data` type, per-key ordered traces, no payload arithmetic.
- **Laws:** `groupA/B/C` prove the one-pass table equals the per-key stable selection for every input.
- **String witnesses:** interleaved per-key state, the bracket result `[[[|1]|3]|6]`, empty input, and checked
  inequalities against the reset and front-insert mutants.
- **Result:** `--verdict` gives ALL PROOFS CHECK. Six mutants are rejected under both check and `--verdict`.
- **Not modeled in Bend:** unbounded key types and first-seen key order (both proved in Lean).

**Native tests (finite, not proof):** on 400 random datasets, including empty and all-filtered cases, the fused
view, unfused view, handwritten loops and independent reference agree on all 14 forms. The String fixtures and the
`.parallelize` refusal also run natively.

**Clean replay:** run from a fresh copy with no `.lake` output, including every i8red8 check: TOTAL=346
UNEXPECTED=0, script exit 0 (`REPLAY9_clean.txt`). The axiom audit covers all 427 `Vw.*` theorems. There are no
`sorry`, `admit`, `native_decide` or `axiom` in the sources.

## 5. Evidence: benchmark protocol and full timing

**Protocol:**
- **Host:** Devin Linux VM, Intel(R) Xeon(R) Processor, 8 vCPUs. Lean 4.15.0 `lake build` (leanc), pinned with `taskset -c 2`.
- **Workload:**
  - same generated data for every form: n = 200,000, 16 departments, 1,000 names;
  - forms timed in rotated order (form order shifts by one each round), 31 rounds per form, two runs;
  - captures vary per round (`minSal = 20000 + r % 3`, `pct = 100 + r % 2`);
  - checksums compared with the independent reference: 0 mismatches.
- **Log:** `records/bench_gen_shapes_31x2.txt`, all 14 forms timed together.

| form (view ÷ handwritten) | baseline | `foldl` | `groupFold` |
|---|---|---|---|
| projection | projecting loop | 0.973 / 0.978 | 0.989 / 1.001 |
| map-built tuple | twin building the same tuple (weak baseline, see §2) | 0.998 / 1.006 | 0.829 / 0.824 |
| map-built tuple | projecting loop | 2.04 / 2.08 | 1.30 / 1.31 |
| map-built tuple, user step `@[inline]` | projecting loop | 0.980 / 0.997 | 1.34 / 1.32 |
| map-built tuple | idiomatic `for`/`let mut` loop (repacks 4 mutable variables per iteration) | 0.552 / 0.558 | 1.30 / 1.30 |
| unfused view (staged lists) | twin building the same tuple | 2.15 / 2.15 | 1.13 / 1.14 |

**Historical first result (kept, not a clean before/after):** before the generic specialization, the map-built
tuple call sites against the idiomatic `for`/`let mut` loops measured 1.85× (`foldl`) and 3.24× (`groupFold`). That
was 11 rounds; log `records/bench_gen_run0_first.txt`, C in `records/bench_gen_run0_GenDemo.c`.
- Back then every element went through proof-side lambdas, with one `lean_apply` per stage. The table insert applied
  the key and the equality dictionary once per table entry.
- The pre-specialization view was never timed against the stronger projecting loops.

**Measurement notes:**
- One shared VM, one core, one n, one key count.
- The table is the same association list in every form (linear lookup), so the ratios are fair, but absolute cost
  grows with the number of keys.
- An early printer dropped leading zeros in ratio fractions. It is fixed, and every ratio here is recomputed from
  logged medians.
- One run that timed the handwritten forms at 0 µs, because the compiler shared their result with the
  expected-value computation, is discarded and documented.
- Growing bracket Strings are correctness fixtures only and are never timed.

## 6. Trusted boundary

- **Proved:** source semantics → generic lowering → the actual `View.foldl` / `View.groupFold` definitions.
- **Trusted:**
  - the Lean compiler, `leanc`/clang, the Lean runtime, and the host;
  - `check_spec.py`, which scans the emitted C by name;
  - the benchmark harness.
- **No semantic effect:** `@[inline]`/`@[specialize]` are compiler hints.

## 7. Replay (Devin-only)

Every build, Lean/Bend check, test, replay and benchmark runs only in the Devin workspace (Linux VM,
`/home/ubuntu`). The user's Mac is only for viewing and steering.

```sh
rsync -a --exclude .lake --exclude 'results_i8red*' ~/i8red9/ fresh/ && cd fresh && ./run_i8red9.sh
bridge/.lake/build/bin/gendemo check
for r in 1 2; do taskset -c 2 bridge/.lake/build/bin/gendemo bench 200000 31; done
./check_spec.py bridge/.lake/build/ir/GenDemo.c
```

## 8. Earlier research material (secondary)

The INT8 kernels, the i8red8 stream adapters, APL models, UTF-8 and lambda rows are carried forward unchanged
and replayed (see `README_i8red8.md`). The historical Mac-only results (the user's Bend runs, Lean tiling, and the
M2 Pro Metal replay) are **not Devin-verified**, and nothing above depends on them.

## 9. Files

- `bridge/Vw/Push.lean`, `Plan.lean`, `Group.lean`, `GroupCtl.lean`: definitions and proofs.
- `bridge/GenDemo.lean`: native call sites, handwritten loops, checker and benchmark.
- `group_bend/GroupFold.bend` and `group_bend/neg/`; `view_controls9/`; `check_spec.py`; `run_i8red9.sh`.
- `REPLAY9_clean.txt`, `EVIDENCE_i8red9.txt`, and `records/`: timing logs, first-build C, and the README before
  this edit.
