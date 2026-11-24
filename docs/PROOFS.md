# How the proofs work

The result: a Lean proof lets us hand GCC a loop it would never write itself, and the loop runs
2.2× faster than the hand-written C++ loop on the record summary. This page explains why that is
allowed and how each proof step works.

## The problem

The pipeline, written the obvious way:

```cpp
Summ s;
for (const Emp& e : es)
  if (e.active && e.salary >= minSal) {
    if (s.count == 0) s.first = e.name;
    s.count += 1; s.total += e.salary * pct / 100; s.last = e.name;
  }
```

Every row passes through one `if`, and four fields (`count`, `total`, `first`, `last`) are threaded through
one chain of updates. The CPU cannot predict the branch, and each row has to wait for the previous one.

A faster loop exists:

```cpp
// no branch: m is all ones if the row is kept, else 0
std::uint64_t m = 0 - (std::uint64_t)(e.active & (e.salary >= minSal));
cnt[j] += 1 & m;  tot[j] += pay & m;          // 4 independent accumulators, row i in lane i % 4
// ...afterwards: add up the lanes, search forward for first, backward for last
```

GCC will not make this change. It does not know the change is safe, and it is only safe for reasons
GCC cannot check by itself. Lean can check them. The rest of this page shows the four facts needed and how
they chain together.

## Step 0: what "the pipeline" means

`xs.iter |>.filter p |>.map f |>.foldl init step` is a fused loop, with no lists built along the way.
`Iter.Denotes it l` says that the iterator `it` behaves exactly like the plain list `l`: for every monad,
callback and start value, running `it` gives the same result as a plain `for` over `l`.

```lean
theorem denotes_array (a : Array α) : a.iter.Denotes a.toList
theorem Denotes.filter (h : it.Denotes l) (p : α → Bool) : (it.filter p).Denotes (l.filter p)
theorem Denotes.map    (h : it.Denotes l) (f : α → β)    : (it.map f).Denotes (l.map f)
theorem Denotes.foldl  (h : it.Denotes l) (init : δ) (step : δ → α → δ) :
    it.foldl init step = l.foldl step init
```

These compose. The fused chain therefore equals `((xs.toList.filter p).map f).foldl step init`, an ordinary
list expression that ordinary algebra can work on. This is what links the fast loop to the API.

## Step 1: split the running summary into four independent jobs

`summary_split` (in `Iter/Rewrite.lean`):

```lean
rows.foldl step ⟨0, 0, none, none⟩ =
  ⟨rows.length, sumL (rows.map Prod.snd), rows.head?.map Prod.fst, rows.getLast?.map Prod.fst⟩
```

**Why it's true:** each field of `step` depends only on its own old value and the current row. `count` goes
up by 1, `total` adds the pay, `first` is set once, and `last` is overwritten each time. So one fold over
four fields is the same as four separate folds.

**How it's proved:** a generalised lemma, `fold_step`, which works from any starting summary, by induction
on `rows`. It needs `total + 0 = total` and associativity, which is why it takes an `AddLaws` argument.

## Step 2: first and last are searches

```lean
theorem head_filter    : (l.filter p).head?    = l.find? p
theorem getLast_filter : (l.filter p).getLast? = l.reverse.find? p
```

**Why:** the first kept row is the first row that passes `p`. A search can stop there, so `first` costs a few
rows instead of a whole pass, and `last` is a backward search that also stops early.

**How:** induction on `l`, splitting on whether `p x` is true.

## Step 3: a filter inside a sum is a mask

```lean
theorem sum_select : sumL ((l.filter p).map f) = sumL (l.map fun x => if p x then f x else 0)
theorem select_mask (b : Bool) (v : UInt64) : (v &&& (0 - if b then 1 else 0)) = if b then v else 0
```

**Why:** dropping an item from a sum is the same as adding 0 in its place. In 64-bit arithmetic `0 - 1` is all
ones, so `v & (0 - 1) = v` and `v & 0 = 0`. The `if` disappears, and so does the branch.

**How:** `sum_select` is induction using `0 + a = a`. `select_mask` is checked on the 64-bit bit vectors,
which have exactly the wrap-around behaviour of C++ `uint64_t`.

## Step 4: several accumulators are allowed

```lean
theorem sum_lanes (h : AddLaws α) (k : Nat) (xs : List α) :
    sumL (xs.foldl rot (List.replicate k 0)) = sumL xs
```

`rot` adds the next item to the front accumulator and moves that accumulator to the back. With `k` lanes,
item `i` lands in lane `i % k`, as in the C++.

**Why:** if `+` is associative and commutative, the sum can be regrouped and reordered any way you like.
**How:** `sum_lanes_from` is the general statement, "the lanes sum to their start values plus the items", by
induction over the items.

This is the step that needs real knowledge about `+`. `UInt64` addition wraps around, and it is still
associative and commutative. Lean proves this through `BitVec` (`u64Laws`). The same rewrite would be wrong
for floating-point `+`, and the type stops you: there is no `AddLaws Float`.

## Putting it together: `fast_correct`

In `Iter/Gen.lean`, pipelines are data: a small language of field expressions (`X`) and predicates (`Q`).
`SPipe.run` is the ordinary `Iter` chain. `SPipe.fast` is what the printed C++ computes. The theorem:

```lean
theorem fast_correct (q : SPipe) (lanes : Nat) (ps : List UInt64) (rows : Array (Row ν)) :
    q.fast lanes ps rows = q.run ps rows := by
  rw [SPipe.run, (((denotes_array rows).filter _).map _).foldl, summary_split u64Laws]   -- steps 0, 1
  simp only [SPipe.fast, sel, select_mask, ..., sum_lanes natLaws, sum_lanes u64Laws,    -- steps 3, 4
    ← sum_select u64Laws, ← sum_select natLaws, sumL_ones, head_filter, getLast_filter]  -- steps 3, 2
```

It holds for **every** pipeline in the language, every lane count and every input, not just the benchmark.
`recPipe_gen` applies it to the benchmark's pipeline: `active != 0 & salary >= p0`, pay `salary * p1 / 100`.

The word-sum generator (`opt_correct`) follows the same pattern with one more fact, `sum_mul`: `Σ x·c = (Σ x)·c`
in wrapping arithmetic, so the multiply runs once instead of once per item.

## Where the proof stops

| step | status |
|---|---|
| `Iter` chain = list program | proved (`Denotes`) |
| list program = split, masked, multi-lane loop | proved (`fast_correct`, `opt_correct`) |
| that loop printed as C++ text | **trusted**: `SPipe.toCpp` / `Loop.toCpp`, about 60 lines |
| C++ text → machine code | **trusted**: GCC |
| count as `Nat` (Lean) vs `uint64_t` (C++) | agree for any array that fits in memory |
| block search (`provedF`) | proved in Lean, C++ copied by hand, results checked |

Two safety details the printer handles: Lean defines `x / 0 = 0` and `x % 0 = x`, but in C++ both are
undefined, so the printer guards `/` and `%` unless the divisor is a nonzero literal. The filter is printed
with `&` and never `&&`, because `&&` short-circuits, which brings the branch back and loses the 2.2×.

## Why GCC can't do this itself

GCC already vectorises plain sums of integers. What it will not do is take one loop that carries four
dependent fields under a branch, and split it into a count, a masked sum and two early-exit searches. That
needs all of steps 1–4 at once. Each step is a fact about this program's meaning (`first` is set once, the
filter can become a mask, `+` can be reordered), not just a local pattern in the code. In Lean each one is a
short proof. Once they are proved, the fast loop is no longer a risky hand optimisation: it is a theorem plus a
printer.
