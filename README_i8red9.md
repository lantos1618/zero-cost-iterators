# i8red9: a generic typed `.view()` with user-defined procedures, and a stable `groupFold`

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
