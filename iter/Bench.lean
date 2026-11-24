import Iter
/-! One focused benchmark: `Iter` chains vs hand-written loops, same inputs, compiled by Lean 4.15.
`check_c.py` inspects the C that Lean emits for these same functions. -/

structure Emp where
  name : String
  salary : Nat
  active : Bool

structure Summ where
  count : Nat
  total : Nat
  first : String
  last : String

def s0 : Summ := ⟨0, 0, "", ""⟩

@[inline] def summStep (s : Summ) (r : String × Nat) : Summ :=
  ⟨s.count + 1, s.total + r.2, if s.count = 0 then r.1 else s.first, r.1⟩

/-- filter → map → foldl over unboxed words -/
@[noinline] def iterU (xs : Array UInt64) (k : UInt64) : UInt64 :=
  xs.iter.filter (fun x => (x ^^^ k) % 3 == 0) |>.map (· * 2) |>.foldl 0 (· + ·)

def handUgo (xs : Array UInt64) (k : UInt64) (i : Nat) (acc : UInt64) : UInt64 :=
  if h : i < xs.size then
    let x := xs[i]
    handUgo xs k (i + 1) (if (x ^^^ k) % 3 == 0 then acc + x * 2 else acc)
  else acc
termination_by xs.size - i

@[noinline] def handU (xs : Array UInt64) (k : UInt64) : UInt64 := handUgo xs k 0 0

/-- drop → dropWhile → filter → count: the counter and flag adapters -/
@[noinline] def iterD (xs : Array UInt64) (k : UInt64) : Nat :=
  (xs.iter.drop 1 |>.dropWhile (fun x => x % 7 != k % 7) |>.filter (fun x => (x ^^^ k) % 3 == 0)).count

/-- the same, with `drop 1` done by the array loop's own index (`Array.iterFrom`) -/
@[noinline] def iterD2 (xs : Array UInt64) (k : UInt64) : Nat :=
  (xs.iterFrom 1 |>.dropWhile (fun x => x % 7 != k % 7) |>.filter (fun x => (x ^^^ k) % 3 == 0)).count

def handDgo (xs : Array UInt64) (k : UInt64) (i : Nat) (dropping : Bool) (n : Nat) : Nat :=
  if h : i < xs.size then
    let x := xs[i]
    if dropping && x % 7 != k % 7 then handDgo xs k (i + 1) true n
    else handDgo xs k (i + 1) false (if (x ^^^ k) % 3 == 0 then n + 1 else n)
  else n
termination_by xs.size - i

@[noinline] def handD (xs : Array UInt64) (k : UInt64) : Nat := handDgo xs k 1 true 0

/-- the same chain run eagerly on lists (one new list per stage) -/
@[noinline] def stagedU (xs : Array UInt64) (k : UInt64) : UInt64 :=
  ((xs.toList.filter (fun x => (x ^^^ k) % 3 == 0)).map (· * 2)).foldl (· + ·) 0

/-- records: filter → map to a tuple → foldl into a summary -/
@[noinline] def iterA (es : Array Emp) (minSal pct : Nat) : Summ :=
  es.iter.filter (fun e => e.active && e.salary ≥ minSal)
    |>.map (fun e => (e.name, e.salary * pct / 100)) |>.foldl s0 summStep

def handAgo (es : Array Emp) (minSal pct : Nat) (i : Nat) (s : Summ) : Summ :=
  if h : i < es.size then
    let e := es[i]
    handAgo es minSal pct (i + 1)
      (if e.active && e.salary ≥ minSal then
        ⟨s.count + 1, s.total + e.salary * pct / 100, if s.count = 0 then e.name else s.first, e.name⟩
      else s)
  else s
termination_by es.size - i

@[noinline] def handA (es : Array Emp) (minSal pct : Nat) : Summ := handAgo es minSal pct 0 s0

/-- enumerate → find (early exit) -/
@[noinline] def iterF (xs : Array UInt64) (t : UInt64) : Option (Nat × UInt64) :=
  xs.iter.enumerate.find? (·.2 > t)

/-- the same, numbered by the array loop's own index (`Array.iterIdx`) -/
@[noinline] def iterF2 (xs : Array UInt64) (t : UInt64) : Option (Nat × UInt64) :=
  xs.iterIdx.find? (·.2 > t)

def handFgo (xs : Array UInt64) (t : UInt64) (i : Nat) : Option (Nat × UInt64) :=
  if h : i < xs.size then
    if xs[i] > t then some (i, xs[i]) else handFgo xs t (i + 1)
  else none
termination_by xs.size - i

@[noinline] def handF (xs : Array UInt64) (t : UInt64) : Option (Nat × UInt64) := handFgo xs t 0

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def timeNs {α : Type} (reps : Nat) (f : Nat → α) (sink : α → UInt64) : IO (Nat × UInt64) := do
  let t0 ← IO.monoNanosNow
  let mut acc : UInt64 := 0
  for r in [0:reps] do
    acc := acc + sink (f r)
  let t1 ← IO.monoNanosNow
  return (t1 - t0, acc)

def median (xs : Array Nat) : Nat := (xs.qsort (· < ·))[xs.size / 2]!

def bench {α : Type} (label : String) (n reps : Nat) (f : Nat → α) (sink : α → UInt64) : IO Unit := do
  let _ := sink (f 0)   -- warm-up run, not timed
  let mut ts : Array Nat := #[]
  let mut chk : UInt64 := 0
  for _ in [0:5] do
    let (t, c) ← timeNs reps f sink
    ts := ts.push t; chk := c
  let ns := median ts
  IO.println s!"BENCH {label} median_ns_per_item_x100={ns * 100 / (n * reps)} checksum={chk}"

def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  let mut xs : Array UInt64 := Array.mkEmpty n
  let mut s : UInt64 := 42
  for _ in [0:n] do
    s := lcg s; xs := xs.push (s >>> 40)
  let names : Array String := #["ana", "bo", "cy", "di", "ed", "flo", "gus", "hal"]
  let es : Array Emp := xs.mapIdx fun i x => ⟨names[i % 8]!, (x % 200000).toNat, x % 5 != 0⟩
  let big : UInt64 := xs.foldl max 0
  let ok1 := iterU xs 0 == handU xs 0 && handU xs 1 == stagedU xs 1 && iterU xs 1 == handU xs 1
  let a := iterA es 50000 90; let b := handA es 50000 90
  let ok2 := a.count == b.count && a.total == b.total && a.first == b.first && a.last == b.last
  let ok3 := iterF xs big == handF xs big && iterF xs (big + 1) == handF xs (big + 1) &&
    iterF2 xs big == handF xs big && iterF2 xs (big + 1) == handF xs (big + 1)
  let ok4 := iterD xs 0 == handD xs 0 && iterD xs 5 == handD xs 5 && iterD2 xs 0 == handD xs 0 && iterD2 xs 5 == handD xs 5
  IO.println s!"BENCH items={n} results_equal={ok1 && ok2 && ok3 && ok4}"
  let reps := 20
  for round in [1:3] do
    IO.println s!"BENCH round={round}"
    bench "handU" n reps (fun r => handU xs r.toUInt64) id
    bench "iterU" n reps (fun r => iterU xs r.toUInt64) id
    bench "stagedU" n reps (fun r => stagedU xs r.toUInt64) id
    bench "handA" n reps (fun r => handA es (50000 + r % 2) 90) (fun r => r.total.toUInt64)
    bench "iterA" n reps (fun r => iterA es (50000 + r % 2) 90) (fun r => r.total.toUInt64)
    bench "handF_miss" n reps (fun r => handF xs (big + 1 + r.toUInt64)) (fun r => (r.map (·.2)).getD 0)
    bench "iterF_miss" n reps (fun r => iterF xs (big + 1 + r.toUInt64)) (fun r => (r.map (·.2)).getD 0)
    bench "iterF2_miss" n reps (fun r => iterF2 xs (big + 1 + r.toUInt64)) (fun r => (r.map (·.2)).getD 0)
    bench "handD" n reps (fun r => handD xs r.toUInt64) (·.toUInt64)
    bench "iterD" n reps (fun r => iterD xs r.toUInt64) (·.toUInt64)
    bench "iterD2" n reps (fun r => iterD2 xs r.toUInt64) (·.toUInt64)
  return if ok1 && ok2 && ok3 && ok4 then 0 else 1
