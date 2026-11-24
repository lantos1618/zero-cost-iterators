# Details

Everything the short README leaves out. Paths are relative to the repository root.

## The API (`iter/Iter/Basic.lean`, `iter/Iter/Group.lean`)

An `Iter α` is its own loop: `fold k b` runs the body `k` over the items, in any monad, and stops at the first
`.done`. Adapters only wrap the body, so a chain is one loop over the source.

| | |
|---|---|
| sources | `xs.iter` for `List` and `Array` |
| adapters | `.map f`, `.filter p`, `.take n` (stops pulling after `n`), `.takeWhile p` (stops at the first miss), `.drop n`, `.dropWhile p`, `.enumerate` (0-based positions), `.zip bs` (with an `Array`, by index, stops at the shorter) |
| terminals | `.foldl init step`, `.find? p` (stops at the hit), `.count`, `.any p` / `.all p` / `.contains a` (stop when decided), `.min?`, `.max?`, `.groupFold key init step`, and `for x in it do ...` |

Terminals return plain values; there is no fusion flag and no `Except` wrapper. `foldl` needs no associativity.
`groupFold` keeps one accumulator per distinct key, keys in first-seen order, each key's items folded in input
order; its table is an association list, so each item costs O(number of keys).

The CLI pipelines, as written in `iter/TaskCore.lean`:

| command | pipeline |
|---|---|
| `tasks logsum` | `rs.iter.filter (logKeep o) \|>.map toHit \|>.foldl logS0 logStep` |
| `tasks sales` | `rs.iter.filter (saleKeep o) \|>.map saleLine \|>.groupFold (·.1) agg0 aggStep` |
| `tasks manifest` | `ls.iter.enumerate.find? (entryBad tr)` |

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


## What is proved

**Meaning (`iter/Iter/Basic.lean`, `iter/Iter/Group.lean`).** `Denotes it l` says that running `it` with any
body, in any lawful monad, is the same as running that body over the list `l` left to right, stopping at the
first `.done`. Sources and adapters preserve it, so every chain gets its staged meaning by composition:

| theorem | statement |
|---|---|
| `denotes_list`, `denotes_array` | `xs.iter` denotes `xs` (`a.toList` for arrays) |
| `Denotes.map`, `.filter`, `.take`, `.enumerate` | the adapter denotes `l.map f`, `l.filter p`, `l.take n`, `l.enum` |
| `Denotes.takeWhile`, `.drop`, `.dropWhile`, `.zip` (`Iter/More.lean`) | `l.takeWhile p`, `l.drop n`, `l.dropWhile p`, `l.zip bs.toList` |
| `Denotes.count`, `.any`, `.all`, `.contains`, `.min?`, `.max?` | `l.length`, `l.any p`, `l.all p`, `l.any (· == a)`, `l.min?`, `l.max?` |
| `Denotes.foldl`, `Denotes.find?` | the terminal equals `List.foldl` / `List.find?` on `l` |
| `Denotes.forIn` | `for x in it` equals `for x in l`, in any lawful monad (state, exceptions) |
| `Denotes.groupFold` | equals an independent stable group-then-fold (`groupRef`) |

**Cost (`iter/Iter/Cost.lean`).** A small IR: a chain of `map`/`filter` (`Chain`), a per-item loop body
(`Body`), and programs that are either one loop or a materialising pass (`Prog.buffer`, the only construct that
allocates). Costs are item reads (`pulls`), callback calls (`calls`) and intermediate cells (`allocs`).
`Chain.staged` is the independent eager reference, one new list per adapter. `lower` builds one loop. For every
chain and terminal:

| theorem | statement |
|---|---|
| `lower_result` | same answer as the staged program, including early-exit terminals |
| `lower_allocs` | 0 intermediate allocations |
| `lower_pulls_le` | at most one read per source item |
| `lower_pulls`, `lower_calls` | for terminals that never stop early: exactly one read per item and exactly the staged program's calls |
| `lower_eq_hand` | `filter p` then `map f` lowers to the loop one writes by hand |
| `toIter_denotes` | the same chain built with the real `Iter` adapters has the staged meaning |

Worked example (`ex_fold`, `ex_find`): on `[1..6]`, `filter even → map (·*10)`, a sum costs 6 reads, 12 calls,
0 cells fused versus 12 reads, 12 calls, 6 cells staged; a `find (· > 20)` stops after 4 reads. Three mutants
give the same answers and are rejected by cost: materialising every stage (`mut_staged`, 9 cells), testing each
filter twice (`mut_dup`, 15 calls), and a find that keeps reading (`mut_noexit`, 6 reads).

**Rewrites (`iter/Iter/Rewrite.lean`).** Proved for any `+` that is associative and commutative with
identity `0` (`AddLaws`), instantiated for `UInt64` (`u64Laws`, wrapping like C++ `uint64_t`) and `Nat`:

| theorem | statement |
|---|---|
| `sum_select` | sum of `f` over the kept items = sum of `p x ? f x : 0` over all items |
| `select_mask` | on `UInt64`, `v &&& (0 - (b ? 1 : 0)) = b ? v : 0` |
| `sum_lanes` | for any `k`, sending item `j` to accumulator `j % k` and adding the lanes gives the sum |
| `sum_mul` | on `UInt64`, the sum of `x * c` is the sum of `x`, times `c` |
| `find_blocks` | for any split into blocks, testing each block with `any` and searching only the first block that matches is `find?` |
| `chain_lanes`, `chain_lanes_mul`, `chain_find_blocks` | the `Iter` chains equal the select + lanes loop, the lanes loop with one final multiplication, and the block search |
| `summary_split` | folding (count, total, first, last) = (length, sum, first row, last row) |
| `head_filter`, `getLast_filter` | the first / last kept row is a forward / backward `find?` |

**Generator (`iter/Iter/Gen.lean`).** `Pipe` is `filter keep → map f → sum` (also `count`, `min?`, `max?`) over 64-bit words, with
expressions built from the item, a parameter `k`, literals, `+`, `*`, `^`, `%`, `==`, `<` and `&`. `opt` makes
a masked, `k`-lane loop and moves a constant right factor of `f` after the sum. `opt_correct`: for every
pipeline, lane count and input, `(opt lanes q).run k xs = q.run k xs`, where `q.run` is the `Iter` chain.
`wordPipe_gen` instantiates it for the benchmark's pipeline. `Loop.toCpp` prints the loop; `replay.sh`
checks the committed `gen/proved_gen.hpp` is exactly what it prints.

`SPipe` is `filter keep → map (label, pay) → running (count, total, first, last)` over rows of word fields,
with expressions built from fields, parameters, literals, `+`, `*`, `/`, `!= 0`, `>=` and `&`; a missing field
or parameter reads as 0. `SPipe.fast1` is one pass, masked count and total, first and last kept as row
pointers with selects; `step1_filter` shows each step skips dropped rows and is the summary step on kept ones,
and `fast1_correct` proves `fast1 = run`, the `Iter` chain. `SPipe.fast2` is what the printed loop computes:
search for the first kept row, then the same pass without tracking `first` (`step2`). `step1_dropWhile` (the
dropped prefix changes nothing) and `step1_step2` (once `first` is set the two steps agree) give
`fast2_correct : fast2 = run`; `recPipe_gen` instantiates it for the benchmark. `SPipe.toCpp` prints it.
`SPipe.fast3 mode` handles each later row with the masked step or a branchy one (`stepB`, equal by
`stepB_step2`) as `mode` says; `fast3_correct` holds for every `mode`, and `SPipe.toCppAdapt` prints a loop
that picks per block from the data (`adaptA`, `recPipe_adapt`). The count is a `Nat` in Lean and a `uint64_t` in
C++, which agree for any array that fits in memory.

**Printer fuzzing (`iter/FuzzCpp.lean`).** 300 random word pipelines (0–9 lanes; each as sum, count, `min?`
and `max?`) and 300 random record
pipelines, with `%` and `/` by zero and missing fields and parameters, each run on inputs of length 0, 1, 5
and all; each record pipeline is printed masked-only and switching (random block, window and threshold): 21,600
results. The C++ is built with `-fsanitize=undefined` and its output must equal Lean's `Pipe.run` /
`SPipe.run` byte for byte (`fuzz_cpp`). `fuzz_mutant` (last row taken on every row) and `fuzz_mutant2`
(branchy body drops the count) and `fuzz_mutant3` (`min` mask inverted) plant printer bugs and require the comparison to fail; `fuzz_policy` inverts
the switch condition and requires it to pass.

`bench.cpp`'s `provedU`, `provedC`, `provedMax`, `provedA` and `adaptA` come from that header (`count_correct`
and `red_correct` cover the word `count` and `min?`/`max?` loops); `provedF` is a hand transcription of the block
search, compared with the hand loop on several inputs (`results_equal`), not proved.

**CLI (`iter/TaskCore.lean`).** `logPipe_spec`, `salesPipe_spec`, `salesPipe_keys` and `manifestPipe_spec`
are one-line compositions of the lemmas above. `entryBad_trace`: tracing doesn't change the answer.

`iter/TaskAudit.lean` lists every theorem in `Iter` and `TaskCore` (146, auto-generated equation lemmas
excluded) and fails if any uses an axiom beyond `propext`, `Classical.choice` and `Quot.sound`. No `sorry`.

## What is checked, not proved

- **Emitted C** (`iter/check_c.py`): for each benchmarked chain it follows the specialised loop Lean generates
  and counts heap allocation sites, closure allocations and indirect calls (`lean_apply_*`). Gate: `filter →
  map → foldl` on words and on records has no closures, no indirect calls and no more allocation sites than the
  hand loop. `enumerate → find?` and `drop → dropWhile → filter → count` are reported but not gated (below).
- **CLI:** file reading, parsers, formatting and the binary. 34 commands compared byte for byte with
  hand-written expected files (`tasks/replay.sh`), exits 0, 1, 2 and 64; 300 fixed-seed generated inputs per
  command against references written without `Iter` (`taskcheck`); three planted mutants caught. With `--trace`
  on `manifest_bad.txt` exactly 4 validation calls are printed, against 8 for an eager control.

## Limits

- The cost model is a model. Nothing proves that Lean's compiler preserves it; `check_c.py` and the benchmark
  are the evidence for compiled code.
- `drop`, `dropWhile` and `zip` have the same gap: `drop → dropWhile → filter → count` has 16 allocation sites to
  the hand loop's 0 and runs 6.0 vs 5.2 ns per item (1.17×). `zip` is proved but not benchmarked.
- `take` and `enumerate` carry their counter in a pair with the accumulator. In Lean 4.15's output this pair,
  and the `(index, item)` pair, are heap cells per item: `enumerate → find?` is about 7× slower than a hand
  loop. The cost model does not cover these two adapters.
- `groupFold` uses an association list: O(keys) work per item.
- The CLI reads each file whole before the pipeline runs, so early exit saves only validation calls.
- No parallel backend.

## Benchmark

`iter/Bench.lean`, `iter/bench.cpp` and `iter/ablate.cpp`, all run by `BENCH=1 ./replay.sh`: the same
generated data, 1,000,000 items, a warm-up call, then batches of 20 calls (Lean: median of 5 batches; C++:
median, min and max of 11). Two rounds; the README reports round 2. Each call varies one argument so the
compiler cannot hoist it out of the timing loop. The C++ runs under `taskset -c 2` and is built twice, with
`g++ -O2 -std=c++20` and with `-O3 -march=native` (GCC 11.4: `std::views::filter`/`transform`/`iota`, no
C++23 `enumerate`; `enumerate` is `iota | transform`). Results are checked equal before timing. `Emp::name` is
a `std::string_view`, so no variant copies strings. One 8-vCPU VM (Intel Xeon, 2.4 GHz); `perf` is blocked
there (`perf_event_paranoid=4`), so no hardware counters, and Clang 14 cannot build GCC 11's `<ranges>`.

## Rerunning every check

`./replay.sh` builds `iter/`, runs the audit, checks the theorem list, scans for `sorry`, runs `taskcheck`, the
fixture replay, `check_c.py`, the header freshness check and the printer fuzz, and exits 0 only if no row is unexpected. It needs only Lean 4.15.0 through
`elan` (pinned in `iter/lean-toolchain`) and python3.

## History

The previous API (`.view`/`.fuse` with a pull-machine model), the INT8/Bend/APL kernels and the milestone
reports are on the `archive` branch, unchanged from commit `8cf63c2`.
