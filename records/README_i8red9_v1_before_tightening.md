# i8red9: a generic typed `.view()` over your own types and procedures, plus `groupFold`

This is a private local artifact in `~/i8red9`, copied from i8red8; i8red8 and every earlier directory are unchanged.
INT8 was only a demonstration. This milestone runs the same `.view()` front door over **arbitrary element and
accumulator types**: String-bearing records, user-written callbacks, immutable runtime captures, and summary-record
or String accumulators. It also adds a grouping terminal, `groupFold(key, init, step)`. The five INT8 kernels and
every i8red8 check are kept and replayed.

## 1. The two real call sites (compiled natively by Lean, `bridge/GenDemo.lean`)

```lean
structure Emp where name : String; dept : String; salary : Nat; active : Bool
structure Summ where count : Nat; total : Nat; first : String; last : String   -- bounded-size summary

-- A: filter -> map -> ordered foldl into a non-element accumulator (minSal, pct are runtime captures)
es.view.filter (fun e => e.active && e.salary ≥ minSal)
  |>.map (fun e => (e.name, e.salary * pct / 100)) |>.fuse |>.foldl s0 summStep

-- B: filter -> map -> groupFold by a String key, retained Summ per key, first-seen key order
es.view.filter (fun e => e.active && e.salary ≥ minSal)
  |>.map (fun e => (e.dept, e.name, e.salary * pct / 100)) |>.fuse
  |>.groupFold (·.1) s0 (fun s r => summStep s r.2)
```

`summStep` is ordered (`first`/`last`) and no associativity is used. Order-sensitive String fixture (a
non-associative step, run natively and proved in Lean):
`groupFold key "" (acc ↦ "[" ++ acc ++ "|" ++ label ++ "]")` over keys `a b a c b a` with labels `1 2 3 4 5 6`
gives `[("a","[[[|1]|3]|6]"), ("b","[[|2]|5]"), ("c","[|4]")]`.

## 2. Verdict

| question | answer | kind of evidence |
|---|---|---|
| fused map/filter/foldl = staged reference, any types, pure total callbacks, no associativity | **yes, for all inputs** | Lean theorem `Chain.push_fold` + `View.foldPath_eq` |
| fused model builds no list between adapters | **yes**: one `List.foldl` over the source with a composed callback | Lean definition `Chain.push` / `PP.run`; `push_one`: each source item reaches the terminal at most once |
| immutable captures | **yes** (`push_fold_capture`; captures are ordinary closure values) | Lean theorem |
| `groupFold` = stable group-then-fold, first-seen key order, per-key retained state | **yes, for all inputs, any `DecidableEq` key** | Lean `groupFold_correct`, `groupFold_state`, `groupFold_ok` |
| `groupFold` in Bend | **yes, narrow domain**: three keys, any `Data` payload, ordered traces; String witnesses | Bend 2.0.40 `--verdict` ALL PROOFS CHECK; 6 mutants rejected |
| real call sites compile and agree with handwritten loops | **yes** on 400 random datasets × 14 forms, plus fixtures | native finite tests (not proof) |
| per-element indirect calls (`lean_apply`, closure allocation) in the specialized loops | **none** in all 6 generic call sites | structural check of emitted C (`check_spec.py`) |
| native cost vs a handwritten loop of the **same shape** | **0.82–1.01×** (see §5) | measurement on this one host |
| `.parallelize(...)` with `foldl`/`groupFold` | **refused** (no lawful chunk summary supplied) | Lean theorem `groupFold_refused` + native run |

## 3. What "any procedure" buys

* **Pure total user callbacks** (map, filter, key, step) of any types may be used in an ordered `foldl` or
  `groupFold` **without being associative, commutative or having an identity**. The ordered fold is compared to the
  ordered staged reference, not to a reassociated one. The bracket step is the witness: `foldl ≠ foldr` on the
  fixture (Lean control `false_br_reassoc` is rejected).
* **Opaque, effectful or trapping callbacks are outside the theorem.** The fused and staged paths call callbacks in
  the same source order, at most once per item (`push_trace`, `push_one`), but evaluation order across adapters
  differs (interleaved vs staged). So effect equivalence is not claimed. Effects must keep their observable
  sequencing, which this milestone does not model.
* **Parallel chunk combining needs a separate lawful summary.** Neither `foldl` nor `groupFold` accepts
  `.parallelize(k)`. Lean control: chunk-then-merge is proved lawful for the separator join (`chunk_sep_lawful`)
  and proved wrong for the bracket step (`chunk_br_wrong`). So refusal is the right default, but separator join is
  not "universally illegal".

## 4. groupFold vs groupBy vs adjacent grouping

| operation | output | retained state while scanning | materialization |
|---|---|---|---|
| `groupFold(key, init, step)` | one accumulator per distinct key, first-seen key order | a table of (key, accumulator): O(#keys) | the result table only; items are not kept |
| full `groupBy` (i8red8 barrier) | every item, grouped | all items: O(n) | the whole grouping |
| adjacent grouping (run splitting) | one group per maximal run of equal keys | the current run only | per run |

Adjacent grouping splits `a b a` into three groups, so it is **not** `groupFold` (control `adjacent_differs` /
`false_gf_adjacent`). The table here is an association list (linear lookup per item, String equality); a hash map
is not used in either the generic or the handwritten paths. Domain limit: keys need `DecidableEq`. The ordering
guarantee is first-seen order, not sorted order.

## 5. Native cost (same benchmark, same data, `taskset -c 2`, n = 200,000 records, 16 departments, 31 rounds × 2 runs)

Ratio of medians, generic view ÷ handwritten loop. Rows after the first come from `records/bench_gen_shapes_31x2.txt`, where all 14 forms are timed together. All forms produce identical checksums (0 mismatches).

| comparison | foldl (A) run 1 / run 2 | groupFold (B) run 1 / run 2 |
|---|---|---|
| **first result** (before specialization) vs idiomatic `for`/`let mut` loop, 11 rounds | 1.85 | 3.24 |
| **T: mapped payload**, after generic specialization; twin loop builds the same tuple, same table | 0.998 / 1.006 | 0.829 / 0.824 |
| **P: projection call site** (no payload tuple); twin loop reads fields directly, same table | 0.973 / 0.978 | 0.989 / 1.001 |
| original mapped call site vs projecting handwritten loop | 2.04 / 2.08 | 1.30 / 1.31 |
| same, with the user's step marked `@[inline]` (user annotation) | 0.980 / 0.997 | 1.34 / 1.32 |
| unfused view (staged lists) vs mapped twin | 2.15 / 2.15 | 1.13 / 1.14 |

**What changed, by kind:**
* **Generic compiler specialization (library only, every call site):** `View` composes map/filter into an
  inlineable closure `PP.run` when the view is built, proved equal to the proof-side `Chain.push` (`PP.hrun`).
  Adapters and terminals are `@[inline]`. The `groupFold` insert `gInsK` is `@[specialize]` and evaluates the key
  once per item (`gInsK_eq` proves it equal to `gIns`). Before: every element went through `Chain.push` lambdas
  with `lean_apply_1`/`lean_apply_2` per stage, and `gIns` applied `key` and the `DecidableEq` dictionary per table
  entry. After: zero `lean_apply` and zero closure allocation in all six specialized loops.
* **Call-site rewrite (user code):** the projection shape P drops the per-record payload tuple (2 constructor
  allocations per accepted record in B). This rewrite is the reason P beats the original mapped call site. It is
  not something the compiler did.
* **Remaining overhead, not removed:** an arbitrary user `map` that builds a tuple still allocates it per accepted
  record. Lean's compiler does not scalar-replace a value passed into the recursive table insert. The fair
  comparison is the same-shape twin (row T), where the view is at parity or faster. The idiomatic `for`/`let mut`
  handwritten foldl is slow (view ÷ it = 0.55–0.58) because Lean repacks its 4 mutable variables into tuples every
  iteration. It is reported, but the structural-recursion loop is the stronger baseline used above.
* **Measurement caveats:** 31 rounds per form, rotated order, one pinned core on a shared VM. Per-cell IQR and
  min–max are in `records/bench_gen_*.txt`. Early runs printed ratios with dropped fraction zeros; this is fixed,
  and the table is recomputed from logged medians (`records/ratio_format_note.txt`). A run before that measured the
  handwritten forms as 0 µs because the compiler shared their result with the expected-value computation; it is
  discarded and documented.

**Allocation accounting** (semantic equality is separate from all of this): the fused path creates no intermediate
list. The String values are shared references (no copying). The `Summ` record is rebuilt per accepted item in both
generic and handwritten paths (in place when unshared). The group table is the same association list in both
paths. The growing bracket Strings are correctness fixtures only and are never timed.

## 6. Proof and compiler boundary

* **Proved (Lean 4.15, standard axioms only):** source semantics (`Plan` denotation `den`, `Chain.ref`,
  `groupRef`) → generic lowering (`Chain.push`, `PP.run`, `gIns`/`gInsK`) → the actual `View.foldl` /
  `View.groupFold` terminals (`foldPath_eq`, `groupFold_ok`). This is the code the native call sites execute.
* **Not proved:** the Lean compiler (LCNF → C), `leanc`/clang, the runtime and the host. Equality of native results
  is tested on finite inputs, not proved. `@[inline]`/`@[specialize]` are compiler hints with no semantic effect.
  The emitted-C property is checked structurally by a script.
* **Bend:** an independent model (three keys, any `Data` payload, ordered traces). No translator links it to the
  Lean model.
* No claims: arbitrary callback/effect equivalence, a verified native compiler, a parallel or GPU backend,
  floating point, or an APL interpreter.

## 7. Replay (Devin-only)

**Execution rule.** Every build, Lean/Bend proof check, test, replay and benchmark runs only inside the Devin
workspace (Linux VM, `/home/ubuntu`). The user's Mac is only for viewing and steering.

```sh
rsync -a --exclude .lake --exclude 'results_i8red*' ~/i8red9/ fresh/ && cd fresh && ./run_i8red9.sh
bridge/.lake/build/bin/gendemo check                                  # native generic call sites
for r in 1 2; do taskset -c 2 bridge/.lake/build/bin/gendemo bench 200000 31; done   # timing (§5)
./check_spec.py bridge/.lake/build/ir/GenDemo.c                       # emitted-C structure
```

Clean replay from a fresh copy with no `.lake` output (`~/i8red9-scratch`): **TOTAL=346 UNEXPECTED=0, script exit 0**
(`REPLAY9_clean.txt`, about 94 s wall time). This includes every i8red8 check. Lean axiom audit: 427 `Vw.*` theorems use
only `propext` / `Classical.choice` / `Quot.sound` or no axioms, and every source-declared theorem is covered; i8red7's
162 theorems are audited as before. No `sorry`, `admit`, `native_decide` or `axiom` in the sources. New rows: the Lean
positive control plus 7 false-claim controls (all rejected), Bend `GroupFold.bend` check + `--verdict` (ALL PROOFS
CHECK), 6 Bend mutants rejected under both check and `--verdict`, `gendemo check` (0 fails), the emitted-C structure
check (0 violations), and a benchmark smoke run (checksums only). The full 31-round timing is in §5, run separately.

## 8. Historical Mac-only and user-reported results (NOT Devin-verified)

These are unchanged from README_i8red8 §7. They were never replayed here, and nothing above depends on them:
the user's `AplLaws.bend` (10 declarations), a 30-law / 15-inequality Bend run, Lean tiling of matrix multiply and
convolution, and an M2 Pro Metal replay (418 outputs, 9 cases). No GPU claim is made.

## 9. Files

* `bridge/Vw/Push.lean`: `Chain`, `ref`, `push`, `push_fold`, `push_trace`, `push_one`, `push_fold_capture`,
  and `PP` with `run`/`hrun`.
* `bridge/Vw/Plan.lean`: `View.push`, `foldPath`, `foldPath_eq`, with inline adapters.
* `bridge/Vw/Group.lean`: `gIns`, `gInsK`, `groupRef`, `groupFold_correct`, `groupFold_state`, `View.groupFold`,
  `groupFold_ok`, `groupFold_refused`.
* `bridge/Vw/GroupCtl.lean`: String-record fixtures, mutants (reset, front, adjacent, reversed) and chunk lawfulness.
* `bridge/GenDemo.lean`: the native call sites, handwritten twins, checker and benchmark.
* `group_bend/GroupFold.bend`, `group_bend/neg/*.bend`, `view_controls9/*.lean`, `check_spec.py`.
* `run_i8red9.sh`, `REPLAY9_clean.txt`, `EVIDENCE_i8red9.txt`, and `records/` (all timing logs, including the first
  result, and the C of the first build).
