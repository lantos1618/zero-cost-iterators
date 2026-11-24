# Zero-cost abstractions from laws: proving them in Lean, printing them as C++

*A write-up of this repository: the method, two case studies, what is proved and what is not, and how we tried
to prove ourselves wrong.*

## Abstract

"Zero-cost abstraction" is usually a promise checked by benchmarks: write the iterator chain, look at the
assembly, hope the compiler fused it. We treat it as a theorem instead. For an abstraction we (1) state its
laws, (2) prove that it equals an independently written plain program, (3) define a cost model and prove the
lowered program costs no more, with deliberately wasteful lowerings proved to be rejected, (4) prove the
optimising rewrites we apply, and (5) print C++ from C syntax trees whose meaning is proved, so only a
one-rule-per-node printer and the C++ compiler are trusted. We apply the recipe to fused iterators (`Iter`:
nine adapters, ten terminals, effects and early exit) and, to check it carries over, to `Result` chaining.
All 449 theorems are checked by Lean 4 with no `sorry` and no non-standard axioms. One idea came out of it
that we have not seen stated elsewhere: a loop that switches between a branchy and a branch-free body *per
block, based on the data*, is proved correct for *every* switching policy, so the policy can be tuned for
speed without any risk to the result. Speed is measured, not proved: the generated loops beat a plain
hand-written loop where the filter is unpredictable, tie it elsewhere, and lose to hand-written branch-free or
AVX2 code in 11–14 of 70 rows of our own falsification race.

## 1. Why prove zero cost?

A benchmark answers "was this fast on this input with this compiler today". It cannot answer the two questions
that make an abstraction safe to use:

1. **Does it compute the same thing?** An iterator chain with `take`, `filter` and a callback that throws must
   stop at the same item, with the same state, as the hand loop. Fusion bugs are usually about early exit and
   effect order, not arithmetic.
2. **Does it do no extra work?** "No intermediate list", "each item read once", "the callback called the same
   number of times" are properties of every run, not of one input.

Both are statements about all inputs, so they need a proof. And a proof about Lean code only helps C++
programmers if the C++ comes out of the proof. That is the motivation for the last step: print C++ from the
proved representation, and keep the unproved part (the printer and compiler) small and named.

We are explicit about what this is not: it is not a claim that generated loops are faster than good C++. A
person can write every loop we generate. What the proof adds is that the fast form is *guaranteed* equal to
the slow, readable one, so it can be generated and tuned without review.

## 2. The recipe

| step | artefact | in `Iter` | in `Result` |
|---|---|---|---|
| 1. laws: the abstraction as data, with a meaning | type + `eval` | `Iter`, `fold` | `KTree`, `KTree.eval` |
| 2. the law that justifies the lowering, proved generically | one theorem per construct | `Denotes.*` (every lawful monad) | `flat_correct` (every lawful monad) |
| 3. an independent plain program; abstraction = plain | theorem | `foldl` over the staged list | `lrun`, `lower_correct` |
| 4. a cost model; lowering costs no more, 0 intermediates | costed evaluators + theorems | `Cost`, `lower_allocs`, `lower_pulls_le`, `lower_calls` | `RCost`, `lower_wraps`, `lower_steps` |
| 5. wasteful lowerings rejected | mutant theorems | `mut_staged`, `mut_dup`, `mut_noexit` | `mut_eager`, `mut_boxed` |
| 6. proved rewrites | list lemmas | `opt_correct`, `fast2/3_correct`, `nodiv_ok`, `printed_find` | (none needed) |
| 7. C syntax trees with C's meaning; trees = proved program | `CE`, `CS`, `*.toC_eval`, `printed_*` | expressions, loop structure, range-for | `printed_chain` |
| 8. print, compile, try to break it | printer, fuzz, mutants, race | 43,200-result fuzz, `falsify.sh` | `chain.cpp`, `chain.sh` |

Steps 2 and 5 are the ones most often skipped. Step 2 is what makes new pipelines cheap: once each adapter has
its `Denotes` lemma, a pipeline's correctness proof is a one-line composition. Step 5 tests the *statement*: a
true theorem can be weaker than intended, and a mutant that gives the right answer while doing extra work
must fail it.

[docs/GUIDE.md](GUIDE.md) is this table as a tutorial, worked on `Result`.

## 3. Case study 1: fused iterators

### 3.1 The abstraction and its law

```lean
structure Iter (α : Type) where
  fold : {m : Type → Type} → [Monad m] → {β : Type} → (β → α → m (ForInStep β)) → β → m β
```

An iterator *is* its loop: `fold k b` runs body `k` over the items in any monad and stops at the first `.done`.
Adapters only wrap the body, so a chain is one loop. The law:

```lean
def Denotes (it : Iter α) (l : List α) : Prop :=
  ∀ (m : Type → Type) [Monad m] [LawfulMonad m] (β : Type) (k : β → α → m (ForInStep β)) (b : β),
    it.fold k b = lfold k b l      -- lfold: the plain left fold over l with early exit (= forIn, lfold_forIn)
```

`Denotes it l` says `it` behaves as list `l` for every lawful monad, every body and every start value, so for
state, exceptions and early exit together. Each adapter has one lemma (`Denotes.filter`, `Denotes.take`,
`Denotes.enumerate`, ...) and each terminal one (`Denotes.foldl`, `Denotes.find?`, `Denotes.forIn`, ...). The
whole pattern is about 200 lines; a user's proof that

```lean
sales.iter |>.filter (·.paid) |>.map (fun s => s.qty * s.unitCents) |>.foldl 0 (· + ·)
```

equals the staged list program is `(((denotes_array sales).filter _).map _).foldl _ _`.

### 3.2 Zero cost, as a theorem

`iter/Iter/Cost.lean` gives a small staged-pipeline language a costed semantics: `pulls` (source reads),
`calls` (callbacks) and `allocs` (intermediate cells). The fused lowering is proved to return the same result
(`lower_result`), allocate nothing (`lower_allocs`), read each item at most once (`lower_pulls_le`) and make
exactly the staged program's callback calls (`lower_calls`). Three wasteful lowerings that return the same
answer are proved to be rejected: one that builds the intermediate list, one that tests the filter twice, one
that ignores early exit.

The limit is stated next to the theorem: the model is not linked to the code Lean's compiler emits. We measured
that separately. For `filter → map → fold` the compiled Lean chain is within 0–16% of a hand loop and 14×
faster than staged lists; for `enumerate`, `drop`, `dropWhile` and `zip` Lean boxes the counter and the chain
is 1.2–7× slower. So "zero cost" holds in the model for every adapter and in compiled Lean for some.

### 3.3 Proved rewrites

Two small pipeline languages (`iter/Iter/Gen.lean`), one over 64-bit words and one over records, are lowered to
loop forms that are proved equal to their `Iter` chains:

- **masks and lanes** (`opt_correct`, `count_correct`, `red_correct`): `if (keep) acc += v` becomes
  `acc[l] += v & -(keep)`, spread over independent accumulators, using that `+` on 64-bit words is associative
  and commutative (`sum_lanes`);
- **divide-free filters** (`nodiv_ok`): for odd `d`, `x % d == 0` iff `x * d⁻¹ ≤ (2⁶⁴−1)/d`, so the filter
  vectorises (Granlund–Montgomery; Lemire, Kaser, Kurz);
- **summary split** (`fast2_correct`): a (count, total, first, last) record summary is a search for the first
  kept row, then one masked pass with `last` as a pointer select;
- **block search** (`printed_find`): `enumerate → find?` as an `any` pass per block of `B`, then a scan of the
  block that hit, for every `B`;
- **any-policy switching** (`fast3_correct`), below.

### 3.4 The any-policy theorem

Branch-free code wins when the filter is unpredictable and loses when it is predictable (sorted data, long
runs). Vectorwise (Răducanu, Boncz, Zukowski, SIGMOD 2013) already switched between the two at run time. What
we add is a proof that makes the switching policy irrelevant to correctness:

```lean
theorem fast3_correct (mode : Nat → Bool) (q : SPipe) (ps : List UInt64) (rows : Array (Row ν)) :
    q.fast3 mode ps rows = q.run ps rows
```

`mode` picks, per row, the masked or the branchy body, and is an *arbitrary* function. The proof is a fold
lemma (`foldl_mix`): if two step functions agree on every state reachable after the first kept row
(`stepB_step2`), any interleaving of them gives the same fold. The printed loop (`SPipe.toCppAdapt`) chooses
each block of 256 rows from how often the keep test flipped in the previous block; `printed_adapt` proves the
printed loop structure computes the chain for every block size, window and threshold. A tuner can therefore
change the policy, the threshold or the block size, or learn them, and cannot change a result. The fuzz checks
this the other way: inverting the policy in the printed C++ must leave all 43,200 results unchanged.

The same idea runs through the generator: it prints up to ten proved-equal variants of each loop (masked or
branchy, 1/2/4/8 accumulators, a plain hand-style loop), and the benchmark keeps the fastest on a separate
sample. Since the plain loop is a candidate, the pick can at worst tie it, up to timing noise.

### 3.5 TPC-H Query 6

To check the method on a query it was not written for, we ran TPC-H Q6 (five range tests, revenue = Σ price ×
discount) through it. The only language change was adding `<`. `q6_total` says the pipeline's total is the
query's revenue, and `q6_gen`, `q6_adapt` say both generated loops equal it; each is a one-line reuse of the
general theorems. Measured on rows laid out as the official generator lays them out, the generated loop is
1.7–2.0× faster than a plain hand loop, ties or beats branch-free hand code, and is 6–12% slower than
hand-written AVX2 under GCC `-O3 -march=native`.

## 4. Case study 2: `Result` chaining

`iter/Iter/Res.lean` (260 lines) runs the recipe on validation code: a chain of steps that may fail, nested
any way (`and_then`, `?`, `>>=`), against flat early-return code. Steps are `set e` (`x = e;`) and
`ensure p err` (`if (!p) return err;`).

- **Law:** `flat_correct`: any nesting equals the flat list of steps, in every lawful monad. It is
  `bind_assoc` in list form, proved once by induction.
- **Plain program and equality:** `lrun` is written independently as early returns; `lower_correct`.
- **Cost:** `RCost` counts steps and intermediate `Result` values. The chain builds one per `then`; the flat
  code builds 0 (`lower_wraps`) and runs exactly the chain's steps, so it stops at the same failure
  (`lower_steps`). `mut_eager` (keeps running after a failure) and `mut_boxed` (wraps every step) are rejected.
- **C:** `lowerC` builds a statement tree; `printed_chain` proves its C meaning is the chain's result and never
  undefined.

Most of the new work was the C statement model (next section); steps 1–5 carried over unchanged.

Measured (`iter/chain.sh`, `noinline` calls on 1M inputs, four builds): the printed function ties a hand
function with the same tests in every build, with the same instruction count (34 under GCC 12, 42–43 under
clang 15). A library `and_then` chain is within 3% of it under GCC and 0–9% slower under clang. The largest
effect was neither: writing `x % 7 == 6` instead of `!(x % 7 < 6)` makes clang 10% faster, because it then uses
a multiply-compare divisibility test. Equal results, different spelling. That is a rewrite to prove, not an
abstraction cost.

## 5. The trust boundary

```
abstraction ──law (Denotes, flat_correct)──▶ plain program ──rewrites──▶ fast program
fast program ──printed_*──▶ model of the printed loop
expressions ──*.toC_eval──▶ CE tree, never undefined
statements ──printed_chain, printed_range_cs──▶ CS tree, never undefined
CE / CS ──print (trusted, 1 rule per node)──▶ C++ text ──compiler (trusted)──▶ machine code
```

- **`CE`** (`iter/Iter/CExpr.lean`): 64-bit operators, `?:`, casts. `CE.eval` returns `none` for `/` or `%`
  by 0, where C++ is undefined and Lean is not (`x / 0 = 0`, `x % 0 = x`). Every generated expression is
  proved to evaluate to `some` of the Lean value, so the zero guards are proved, not just tested.
- **`CS`** (`iter/Iter/CStmt.lean`): assignment, `if (!c) return r;`, `if`, sequencing and a range-for
  over the input. `CS.exec` returns `none` on undefined behaviour, `.ret` on `return`, `.ok env` on fall-through.
  The `Result` function and the range-for word loops are printed from `CS` trees and proved.
- **Loop models** (`iter/Iter/CLoop.lean`): the lane, record, switching and search loops use local arrays,
  index loops and pointer selects, which `CS` does not have yet. For those, each printed C++ loop is modelled
  by one Lean function, and the models are proved equal to the proved loops (`printed_correct`,
  `printed_summary`, `printed_adapt`, `printed_find`). That each printed line means its Lean function is
  trusted and fuzzed.

What is trusted, all of it named: the text rule per node (`CE.print`, `CS.print`), the line-to-function
correspondence for loops not yet in `CS`, and the C++ compiler. The fuzz (`iter/FuzzCpp.lean`) prints 600
random pipelines in every loop form, compiles them with UBSan and compares 43,200 results with Lean; three
planted printer bugs must be caught and one policy inversion must change nothing.

Bugs we found are a fair test of where the boundary is. Every one was outside the proofs: a 0-lane loop that
never ended, `x % 0` (defined in Lean, undefined in C++), a missing parameter printed as non-compiling C++, and
a fuzz harness that grew quadratically. None was a wrong law or a wrong proof. Each led to moving a piece of the
printer into a proved tree.

## 6. Trying to prove it wrong

For each claim we wrote down the cheapest test that would break it, and ran it (README, "How to prove this
wrong").

| claim | cheapest break | result |
|---|---|---|
| a chain equals its list program | a counterexample (it would make the proof impossible) | 449 theorems check; 0 non-standard axioms |
| zero cost in the model | a wasteful lowering the cost theorems accept | 5 planted (3 iterator, 2 `Result`), all rejected |
| zero cost in compiled Lean | time a chain against its hand loop | **broken** for `enumerate`, `drop`, `dropWhile`, `zip` |
| the printed C++ computes what Lean proved | plant a printer bug | 4 planted, all caught |
| generated C++ is within 5% of the fastest hand loop | `falsify.sh`: GCC 11 and 12, clang 15, `-O2`, `-O3 -march=native`, profile-guided GCC; plain, branch-free and AVX2 hand loops | **broken in 11–14 of 70 rows**; no wrong results |

The losses, and what we learned from them:

- **Profile-guided GCC, random records, 2.9× slower** than branch-free hand code: with a profile showing the
  keep test taken 60% of the time, GCC turns our pointer select back into a branch, which mispredicts. A
  pointer mask fixes it but costs 15% in normal builds, so it is not applied.
- **GCC native sum and max, 1.1–1.9× slower than hand AVX2.** Under clang 15 ours beats the AVX2 loop on sum,
  count and max, because the divide-free filter vectorises there.
- **Search with no match at `-O2`, 1.3–1.7× slower**, with identical instructions: forcing 64-byte loop
  alignment closes it. Code placement, not the loop.
- **Inconsistent numbers.** An outside review of an earlier README found its speed tables contradicted each
  other (stale runs). The README now has one speed table, regenerated per release, and states that
  differences under about 5% are noise on this VM.

Hardware counters are blocked on the test VM, so explanations involving branch misprediction are inferred
from random-vs-sorted timings and from the assembly, not measured.

## 7. Speed, for the record

ns per item, 1M items, median of 11 batches pinned to one core, GCC 11.4, `-O2` / `-O3 -march=native`:

| pipeline | C++ hand loop | C++ `std::views` | ours |
|---|---|---|---|
| words: filter → map → sum | 0.76 / 0.77 | 3.32 / 3.40 | 0.57 / 0.55 |
| words: filter → count | 0.38 / 0.39 | 3.15 / 3.19 | 0.39 / 0.42 |
| words: filter → map → max | 3.68 / 3.23 | 3.41 / 3.37 | 0.91 / 0.78 |
| records, random | 3.78 / 3.15 | 4.04 / 4.13 | 1.32 / 1.35 |
| records, sorted | 1.50 / 2.83 | 1.11 / 1.16 | 1.10 / 1.21 |
| records, mixed | 2.68 / 2.94 | 2.64 / 2.51 | 1.22 / 1.18 |
| enumerate → find, no match | 0.30 / 0.29 | 0.30 / 0.30 | 0.30 / 0.22 |

The pattern is the textbook one (Ross, TODS 2004): branch-free code wins where the filter is unpredictable
and ties where it is predictable. A hand-written branch-free loop gets about our speed. The proofs make the
rewrite safe to generate and tune; they do not make it faster than a good programmer.

## 8. Related work

| idea | prior work | relation |
|---|---|---|
| fused iterator chains | stream fusion (Coutts, Leshchinskiy, Stewart, ICFP 2007); Rust iterators; C++20 ranges | same API idea; we prove the fusion law under effects and early exit, and state zero cost as a theorem |
| fused streams as C, no overhead | strymonas (Kiselyov et al., POPL 2017) | strymonas generates by staging and is complete for more combinators; we prove correctness and cost |
| proved generators printing C | Fiat-Crypto (Erbsen et al., S&P 2019); CompCert; CakeML | Fiat-Crypto is the model for steps 6–8, at far larger scale; CompCert/CakeML would remove the compiler from the trusted base |
| branch-free selection | Ross (TODS 2004) | the masks we prove |
| run-time switching between bodies | Vectorwise micro-adaptivity (SIGMOD 2013) | the switching we prove correct for every policy |
| schedules that change speed, not results; autotuning equal plans | Halide (PLDI 2013), Exo (PLDI 2022), FFTW's planner | our tuner is the same idea with each candidate's equality proved |
| divisibility by multiplication | Granlund–Montgomery (PLDI 1994); Lemire, Kaser, Kurz (2019) | `nodiv_ok` proves the form we print |

Every technique here exists elsewhere. What we have not seen combined is the fusion law under arbitrary lawful
effects, zero cost stated and checked as a theorem in a cost model with mutants, and the any-policy theorem
for adaptive loops, all ending in printed C++ with a named trusted base.

## 9. Limitations

- **The cost model is a model.** It counts reads, calls and intermediates, not cycles, and is not connected to
  Lean's compiled code or to C++ machine code.
- **The pipeline languages are small**: word and record pipelines with a handful of operators; no strings, no
  user functions. `Iter` itself is general, but only these languages are printed as C++.
- **Part of the printed loops is still trusted.** Local arrays, index loops and pointer selects are not yet in
  `CS`, so for the lane, record and search loops the line-to-model correspondence is fuzzed, not proved.
- **The compiler is trusted.** Compiling with a verified compiler would close that, at a large speed cost.
- **One VM, no hardware counters.** Speed results are for one 8-vCPU Xeon; causes involving branches are
  inferred.

## 10. Future work

1. Add local arrays, index loops and selects to `CS`, and print the lane, record and search loops from it;
   then only `CS.print` and the compiler are trusted.
2. Prove and print spelling rewrites such as `!(x % d < d − 1)` ⇔ `x % d == d − 1`, which section 4 showed
   matter to clang more than the abstraction does.
3. A third abstraction with state that outlives a call (a ring buffer, a parser combinator), to test step 4
   with a richer cost model.
4. User-defined functions in the pipeline languages, with their own `toC_eval` obligations.
5. Learn the switching policy; `fast3_correct` already guarantees any learned policy is correct.

## Reproducing

```sh
(cd iter && lake build)   # Lean 4.15.0 via elan; checks every proof
./replay.sh               # build, axiom audit, theorem list, fuzz, mutants, Result checks: 15 rows
sh iter/falsify.sh        # the speed race (GCC 11/12, clang 15)
sh iter/chain.sh          # the Result chain race
```
