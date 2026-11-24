# How to prove your own abstraction is zero cost

A step-by-step guide to the recipe this repository uses, worked on its second example: `Result` chaining
(`iter/Iter/Res.lean`, 260 lines). The first example, `Iter`, is larger; the steps are the same. Each step
says what to write, what to prove, and what can go wrong.

The abstraction: validation code written as a nested chain of steps that may fail,

```cpp
// what people write (C++23 std::expected, Rust's ?, Haskell's >>=)
auto r = parse(x).and_then(scale).and_then(check_mod7).and_then(mix).and_then(check_mod97);
```

and the claim to prove: it computes exactly what the flat early-return code computes, and costs no more.

```cpp
// the plain program
if (!(x < 1000000000000)) return Res{0, 1};
x = x * 10 + k;
if (!(x % 7 < 6)) return Res{0, 2};
...
return Res{1, x};
```

## Step 1. Write the abstraction as data, with its meaning

Make the abstraction a Lean value you can inspect, and give it a meaning (`eval`) in terms of the effect
it stands for. Keep the meaning generic over the effect where you can.

```lean
inductive KTree (m : Type → Type) (α : Type) where
  | step (f : α → m α)
  | seq (a b : KTree m α)

def KTree.eval [Monad m] : KTree m α → α → m α
  | .step f => f
  | .seq a b => fun x => a.eval x >>= b.eval
```

`seq` nests either way, so `(a >=> b) >=> c` and `a >=> (b >=> c)` are different trees. That is the
abstraction's whole convenience, and its whole risk: the flat code must not depend on how the user nested it.

**Pitfall:** do not define the meaning by first flattening. The meaning must be the one users rely on
(here: `>>=`), or step 2 proves nothing.

## Step 2. State the law, and prove it once, generically

The law says what the abstraction may be replaced by. Here: any nesting equals the flat list of steps run
left to right, in every lawful monad.

```lean
def KTree.flat : KTree m α → List (α → m α)
def runList [Monad m] : List (α → m α) → α → m α

theorem flat_correct [Monad m] [LawfulMonad m] :
    ∀ (t : KTree m α) (x : α), runList t.flat x = t.eval x
```

The proof is three lines: induction on the tree, plus `runList_append`, which is the monad associativity law
(`bind_assoc`) in list form. This is the counterpart of `Iter.Denotes` for iterators: one generic fact
that every concrete use reuses.

**Pitfall:** if the law needs `LawfulMonad`, say so. A proof for one monad only (say `Except`) would not
cover state or logging.

## Step 3. Write the plain program independently, and prove the abstraction equals it

Write the program a careful person would write by hand, *not* by calling the abstraction:

```lean
def lrun (k : UInt64) : List St → UInt64 → Except UInt64 UInt64
  | [], x => .ok x
  | .set e :: ss, x => lrun k ss (e.eval k x)
  | .ensure p err :: ss, x => if p.eval k x then lrun k ss x else .error err

theorem lower_correct (c : Chain) (k x : UInt64) : lrun k c.flat x = c.run k x
```

`lower_correct` reuses `flat_correct` (through `lrun_eq`, which says `lrun` is `runList` of the step
meanings). Independence matters: if `lrun` were defined as `runList`, the theorem would be `rfl` and would
not rule out a shared bug.

## Step 4. Define what "cost" means, and prove the lowering costs no more

"Zero cost" is only a theorem once cost is defined. Pick the quantities the abstraction is suspected of
adding, and count them in a costed version of both programs:

```lean
structure RCost where
  steps : Nat   -- steps executed
  wraps : Nat   -- intermediate Result values built and inspected between steps

def Chain.runC (k : UInt64) : Chain → UInt64 → Except UInt64 UInt64 × RCost   -- 1 wrap per `seq`
def lrunC (k : UInt64) : List St → UInt64 → Except UInt64 UInt64 × RCost      -- 0 wraps

theorem lower_wraps : (lrunC k ss x).2.wraps = 0
theorem lower_steps : (lrunC k c.flat x).2.steps = (c.runC k x).2.steps
```

`lower_steps` says the flat code runs exactly the steps the chain runs, so it also stops at the same
failure. `runC_fst` and `lrunC_fst` say the costed versions return the same values as the plain ones.

**Pitfall:** a cost model is only as good as what it counts. Here it counts steps and wrappers, not cycles;
whether a compiler removes the wrappers in the real `std::expected` code is a separate, measured question
(step 7).

## Step 5. Plant wrong lowerings and prove they are rejected

A correct theorem can be weaker than you meant. Test the statement by writing lowerings that give the
right answer but are wasteful, and prove the cost theorems catch them:

```lean
def eagerC ...  -- keeps evaluating steps after a failure (same result)
def boxedC ...  -- wraps every step in a Result (same result)

theorem mut_eager : (eagerC 0 demo.flat 500).1 = demo.run 0 500 ∧
    (eagerC 0 demo.flat 500).2.steps ≠ (demo.runC 0 500).2.steps
theorem mut_boxed : (boxedC 0 demo.flat 5).1 = demo.run 0 5 ∧ (boxedC 0 demo.flat 5).2.wraps ≠ 0
```

If a mutant gave the same answer *and* passed the cost theorems, the cost model would be too weak.

## Step 6. Lower to a C syntax tree with its own meaning, and prove the tree

Do not print C++ straight from Lean strings. Build a small C syntax tree, give the tree a meaning that
follows C (undefined behaviour is `none`), and prove the tree means the plain program:

```lean
-- iter/Iter/CStmt.lean
inductive CS where
  | skip | assign (s : Slot) (e : CE) | guard (c r : CE)   -- `if (!c) return r;`
  | seq (a b : CS) | when (c : CE) (t : CS) | each (body : CS)
def CS.exec (xs : List UInt64) : CS → (Slot → UInt64) → Option Out   -- none = undefined behaviour

-- iter/Iter/Res.lean
def lowerC : List St → CS
theorem printed_chain (c : Chain) (k x : UInt64) (env : Slot → UInt64) (hx : env .x = x) (hk : env .k = k) :
    ((lowerC c.flat).exec [] env).map Out.res = some (c.run k x)
```

`printed_chain` says the statements never hit undefined behaviour (it is `some`) and return the chain's
result. Expression trees (`CE`, `iter/Iter/CExpr.lean`) are reused from the iterator work; `/` and `%` by
zero are undefined there, so a step that divides by a value that might be 0 fails this proof.

The printer is now one fixed text rule per tree node (`CE.print`, `CS.print`). That rule, and the C++
compiler, are what you still trust.

## Step 7. Print, compile, and try to prove it wrong

```lean
theorem checkChain_gen ... := printed_chain check k x env hx hk     -- the worked chain, one line
def Chain.toCpp (c : Chain) (name : String) : String                -- prints `lowerC c.flat`
```

`iter/gen/proved_gen.hpp` contains the printed `provedCheck`. Then check what the theorems do not cover:

- **Results** (`replay.sh` rows `chain_cpp`, `chain_mutant`): `iter/chain.cpp` runs 3M inputs through the
  printed function, a hand-written early-return function and a library `and_then` chain (flat and nested),
  under UBSan; all must agree. A planted printer bug (wrong error code) must be caught.
- **Speed** (`sh iter/chain.sh`): the same functions, timed and counted in instructions under GCC 12 and
  clang 15. Results are in the README.

## Checklist

| step | you write | you prove | it rules out |
|---|---|---|---|
| 1 | the abstraction as data + its meaning | — | — |
| 2 | the law | the law, for every lawful effect | nesting or effect order changing the result |
| 3 | an independent plain program | abstraction = plain program | a lowering with a different result |
| 4 | a cost model for both | lowering cost ≤ abstraction cost; 0 intermediates | hidden work in the model |
| 5 | wasteful lowerings | each is rejected | a cost theorem too weak to mean anything |
| 6 | a C tree with C's meaning | tree = plain program, never undefined | printer logic bugs; UB such as `% 0` |
| 7 | the printer (one rule per node), tests | — | (fuzzed) the text rule; (measured) the compiler |

What stays trusted at the end: the text rule per node, the C++ compiler, and that the cost model counts
the costs you care about.
