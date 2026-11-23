import Vw
/-! Two REAL compiled call sites of the generic `.view()` front door over String-bearing user records,
user-authored callbacks with immutable runtime captures, and non-element accumulators; compared with
independently handwritten loops over the same state representation. Native Lean (compiled C via
`leanc`); the fused path executes the generic `View.foldPath` / `Chain.push` code, not a hand-coded loop.
Usage: gendemo check | gendemo bench N ROUNDS -/
open Vw

structure Emp where
  name : String
  dept : String
  salary : Nat
  active : Bool

/-- bounded-size summary: count, total, and references to the first/last accepted names -/
structure Summ where
  count : Nat
  total : Nat
  first : String
  last : String
  deriving DecidableEq, Repr, BEq

def s0 : Summ := ⟨0, 0, "", ""⟩
/-- user step: ordered (first/last), not an element type, no associativity used -/
def summStep (s : Summ) (r : String × Nat) : Summ :=
  ⟨s.count + 1, s.total + r.2, if s.count = 0 then r.1 else s.first, r.1⟩

/-! ### call site A: filter → map → foldl -/
@[noinline] def viewA (es : List Emp) (minSal pct : Nat) : Summ :=
  match (es.view.filter (fun e => e.active && e.salary ≥ minSal)
      |>.map (fun e => (e.name, e.salary * pct / 100)) |>.fuse |>.foldl s0 summStep) with
  | .ok s => s | .error _ => s0
@[noinline] def stagedA (es : List Emp) (minSal pct : Nat) : Summ :=
  match (es.view.filter (fun e => e.active && e.salary ≥ minSal)
      |>.map (fun e => (e.name, e.salary * pct / 100)) |>.foldl s0 summStep) with
  | .ok s => s | .error _ => s0
/-- independent handwritten loop -/
@[noinline] def handA (es : List Emp) (minSal pct : Nat) : Summ := Id.run do
  let mut c := 0; let mut t := 0; let mut fst := ""; let mut lst := ""
  for e in es do
    if e.active && e.salary ≥ minSal then
      if c = 0 then fst := e.name
      c := c + 1; t := t + e.salary * pct / 100; lst := e.name
  return ⟨c, t, fst, lst⟩

/-- stronger handwritten baseline: explicit structural recursion on the same `Summ` record
(the `for`/`let mut` form above packs its 4 mutable variables into nested tuples each iteration) -/
def handA2go (minSal pct : Nat) : List Emp → Summ → Summ
  | [], s => s
  | e :: es, s =>
    if e.active && e.salary ≥ minSal then
      handA2go minSal pct es ⟨s.count + 1, s.total + e.salary * pct / 100, if s.count = 0 then e.name else s.first, e.name⟩
    else handA2go minSal pct es s
@[noinline] def handA2 (es : List Emp) (minSal pct : Nat) : Summ := handA2go minSal pct es s0

/-- the same user step with an `@[inline]` hint: a user-side annotation only; the call sites below use
the identical generic `.view()` path (variant to measure what the compiler does once it may inline) -/
@[inline] def summStepI (s : Summ) (r : String × Nat) : Summ :=
  ⟨s.count + 1, s.total + r.2, if s.count = 0 then r.1 else s.first, r.1⟩
@[noinline] def viewAi (es : List Emp) (minSal pct : Nat) : Summ :=
  match (es.view.filter (fun e => e.active && e.salary ≥ minSal)
      |>.map (fun e => (e.name, e.salary * pct / 100)) |>.fuse |>.foldl s0 summStepI) with
  | .ok s => s | .error _ => s0

/-! ### call site B: filter → map → groupFold by String dept -/
@[noinline] def viewB (es : List Emp) (minSal pct : Nat) : List (String × Summ) :=
  match (es.view.filter (fun e => e.active && e.salary ≥ minSal)
      |>.map (fun e => (e.dept, e.name, e.salary * pct / 100)) |>.fuse
      |>.groupFold (·.1) s0 (fun s r => summStep s r.2)) with
  | .ok t => t | .error _ => []
@[noinline] def stagedB (es : List Emp) (minSal pct : Nat) : List (String × Summ) :=
  match (es.view.filter (fun e => e.active && e.salary ≥ minSal)
      |>.map (fun e => (e.dept, e.name, e.salary * pct / 100))
      |>.groupFold (·.1) s0 (fun s r => summStep s r.2)) with
  | .ok t => t | .error _ => []
/-- independent handwritten insertion into the SAME representation (assoc list, first-seen order) -/
def hIns (d n : String) (p : Nat) : List (String × Summ) → List (String × Summ)
  | [] => [(d, ⟨1, p, n, n⟩)]
  | (k, s) :: rest => if k == d then (k, ⟨s.count + 1, s.total + p, s.first, n⟩) :: rest else (k, s) :: hIns d n p rest
@[noinline] def handB (es : List Emp) (minSal pct : Nat) : List (String × Summ) := Id.run do
  let mut tbl : List (String × Summ) := []
  for e in es do
    if e.active && e.salary ≥ minSal then
      tbl := hIns e.dept e.name (e.salary * pct / 100) tbl
  return tbl

@[noinline] def viewBi (es : List Emp) (minSal pct : Nat) : List (String × Summ) :=
  match (es.view.filter (fun e => e.active && e.salary ≥ minSal)
      |>.map (fun e => (e.dept, e.name, e.salary * pct / 100)) |>.fuse
      |>.groupFold (·.1) s0 (fun s r => summStepI s r.2)) with
  | .ok t => t | .error _ => []
def handB2go (minSal pct : Nat) : List Emp → List (String × Summ) → List (String × Summ)
  | [], t => t
  | e :: es, t =>
    if e.active && e.salary ≥ minSal then handB2go minSal pct es (hIns e.dept e.name (e.salary * pct / 100) t)
    else handB2go minSal pct es t
@[noinline] def handB2 (es : List Emp) (minSal pct : Nat) : List (String × Summ) := handB2go minSal pct es []

/-! ### shape comparison (call-site rewrite, not a compiler change):
`T` = mapped payload: the user's map builds a tuple per accepted record, consumed by a separate reducer;
`P` = projection: key/reducer read the record fields directly, no payload tuple.
Each shape has its own handwritten loop with the same semantics and the same table representation. -/
@[noinline] def viewAp (es : List Emp) (minSal pct : Nat) : Summ :=
  match (es.view.filter (fun e => e.active && e.salary ≥ minSal) |>.fuse
      |>.foldl s0 (fun s e => ⟨s.count + 1, s.total + e.salary * pct / 100,
                              if s.count = 0 then e.name else s.first, e.name⟩)) with
  | .ok s => s | .error _ => s0
/-- handwritten twin of the mapped shape A: builds the same (name, value) pair and calls the same step -/
def handATgo (minSal pct : Nat) : List Emp → Summ → Summ
  | [], s => s
  | e :: es, s =>
    if e.active && e.salary ≥ minSal then handATgo minSal pct es (summStep s (e.name, e.salary * pct / 100))
    else handATgo minSal pct es s
@[noinline] def handAT (es : List Emp) (minSal pct : Nat) : Summ := handATgo minSal pct es s0

@[noinline] def viewBp (es : List Emp) (minSal pct : Nat) : List (String × Summ) :=
  match (es.view.filter (fun e => e.active && e.salary ≥ minSal) |>.fuse
      |>.groupFold (·.dept) s0 (fun s e => ⟨s.count + 1, s.total + e.salary * pct / 100,
                                          if s.count = 0 then e.name else s.first, e.name⟩)) with
  | .ok t => t | .error _ => []
/-- handwritten twin of the mapped shape B: builds the same (dept, name, value) tuple, inserts with the
same assoc-list table, calls the same step -/
def hInsT (r : String × String × Nat) : List (String × Summ) → List (String × Summ)
  | [] => [(r.1, summStep s0 r.2)]
  | (k, s) :: rest => if k == r.1 then (k, summStep s r.2) :: rest else (k, s) :: hInsT r rest
def handBTgo (minSal pct : Nat) : List Emp → List (String × Summ) → List (String × Summ)
  | [], t => t
  | e :: es, t =>
    if e.active && e.salary ≥ minSal then handBTgo minSal pct es (hInsT (e.dept, e.name, e.salary * pct / 100) t)
    else handBTgo minSal pct es t
@[noinline] def handBT (es : List Emp) (minSal pct : Nat) : List (String × Summ) := handBTgo minSal pct es []

/-! ### data -/
def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64
def depts : Array String := #["eng", "ops", "sales", "legal", "hr", "fin", "mkt", "it", "qa", "sec",
  "data", "ml", "infra", "web", "mobile", "design"]
def gen (n seed nd nn : Nat) : List Emp := Id.run do
  let names : Array String := (List.range nn).toArray.map fun i => s!"emp{i}"
  let mut s := seed; let mut out : Array Emp := #[]
  for _ in [0:n] do
    s := lcg s; let a := s / 65536
    out := out.push ⟨names[a % nn]!, depts[(a / 7) % nd]!, (a / 131) % 200000, (a / 977) % 5 != 0⟩
  return out.toList

def refA (es : List Emp) (minSal pct : Nat) : Summ :=
  ((es.filter (fun e => e.active && e.salary ≥ minSal)).map (fun e => (e.name, e.salary * pct / 100))).foldl summStep s0
def refB (es : List Emp) (minSal pct : Nat) : List (String × Summ) :=
  groupRef (·.1) s0 (fun s (r : String × String × Nat) => summStep s r.2)
    ((es.filter (fun e => e.active && e.salary ≥ minSal)).map (fun e => (e.dept, e.name, e.salary * pct / 100)))

def ck (s : Summ) : Nat := s.count * 1000003 + s.total + s.first.length * 31 + s.last.length * 17
def ckT (t : List (String × Summ)) : Nat := t.foldl (fun a (k, s) => a * 7 % 1000000007 + k.length + ck s) 0

def check : IO UInt32 := do
  let mut fails := 0; let mut cases := 0
  let mut s := 12345
  for i in [0:400] do
    s := lcg s
    let n := if i % 50 = 0 then 0 else (s / 97) % 300
    let nd := 1 + (s / 13) % 6
    let es := gen n s nd 40
    let minSal := if i % 37 = 0 then 10000000 else (s / 7) % 150000  -- some runs: all filtered
    let pct := (s / 3) % 150
    cases := cases + 1
    let ra := refA es minSal pct; let rb := refB es minSal pct
    for r in [viewA es minSal pct, stagedA es minSal pct, handA es minSal pct, handA2 es minSal pct, viewAi es minSal pct, viewAp es minSal pct, handAT es minSal pct] do
      if r != ra then fails := fails + 1
    for r in [viewB es minSal pct, stagedB es minSal pct, handB es minSal pct, handB2 es minSal pct, viewBi es minSal pct, viewBp es minSal pct, handBT es minSal pct] do
      if r != rb then fails := fails + 1
  IO.println s!"generic view vs staged vs handwritten vs independent reference: {cases} datasets x 14 forms, fails={fails}"
  -- order-sensitive String fixtures run NATIVELY through the same entry point
  let evs : List (String × String) := [("a","1"),("b","2"),("a","3"),("c","4"),("b","5"),("a","6")]
  let br := fun (acc : String) (e : String × String) => "[" ++ acc ++ "|" ++ e.2 ++ "]"
  let g := (evs.view.fuse.groupFold (·.1) "" br).toOption
  let want := some [("a", "[[[|1]|3]|6]"), ("b", "[[|2]|5]"), ("c", "[|4]")]
  IO.println s!"native groupFold bracket fixture: {repr g} ok={g == want}"
  if g != want then fails := fails + 1
  let e0 := (([] : List (String × String)).view.fuse.groupFold (·.1) "" br).toOption
  let e1 := (evs.view.filter (fun _ => false) |>.fuse |>.groupFold (·.1) "" br).toOption
  IO.println s!"native empty={repr e0} all-filtered={repr e1}"
  if e0 != some [] || e1 != some [] then fails := fails + 1
  let par := (evs.view.fuse.parallelize 2 |>.groupFold (·.1) "" br)
  match par with
  | .error m => IO.println s!"native parallelize groupFold: {m}"
  | .ok _ => do IO.println "parallelize groupFold NOT refused"; fails := fails + 1
  IO.println s!"GENDEMO_CHECK fails={fails}"
  return if fails = 0 then 0 else 1

def median (xs : Array Nat) : Nat := let s := xs.qsort (· < ·); s[s.size / 2]!
def q (xs : Array Nat) (num den : Nat) : Nat := let s := xs.qsort (· < ·); s[(s.size - 1) * num / den]!

def bench (n rounds : Nat) : IO UInt32 := do
  let es := gen n 987654321 16 1000
  let forms : Array String := #["viewA", "handA", "stagedA", "handA2", "viewAi", "viewAp", "handAT", "viewB", "handB", "stagedB", "handB2", "viewBi", "viewBp", "handBT"]
  let mut times : Array (Array Nat) := Array.mkArray forms.size #[]
  let mut sums : Array Nat := Array.mkArray forms.size 0
  let mut bad := 0
  for r in [0:rounds] do
    let minSal := 20000 + r % 3
    let pct := 100 + r % 2
    let wantA := ck (refA es minSal pct); let wantB := ckT (refB es minSal pct)
    for j in [0:forms.size] do
      let i := (j + r) % forms.size
      let t0 ← IO.monoNanosNow
      let c := match i with
        | 0 => ck (viewA es minSal pct) | 1 => ck (handA es minSal pct) | 2 => ck (stagedA es minSal pct)
        | 3 => ck (handA2 es minSal pct) | 4 => ck (viewAi es minSal pct)
        | 5 => ck (viewAp es minSal pct) | 6 => ck (handAT es minSal pct)
        | 7 => ckT (viewB es minSal pct) | 8 => ckT (handB es minSal pct) | 9 => ckT (stagedB es minSal pct)
        | 10 => ckT (handB2 es minSal pct) | 11 => ckT (viewBi es minSal pct)
        | 12 => ckT (viewBp es minSal pct) | _ => ckT (handBT es minSal pct)
      if c == 1 then IO.println "unlikely"   -- forces evaluation before t1
      let t1 ← IO.monoNanosNow
      if c != (if i < 7 then wantA else wantB) then bad := bad + 1
      times := times.modify i (·.push (t1 - t0))
      sums := sums.modify i (· + c)
  IO.println s!"n={n} rounds={rounds} depts=16 names=1000 (times in microseconds; median [p25,p75] min-max)"
  for i in [0:forms.size] do
    let t := times[i]!
    IO.println s!"{forms[i]!}: median={median t / 1000} [{q t 1 4 / 1000},{q t 3 4 / 1000}] {q t 0 1 / 1000}-{q t 1 1 / 1000} checksum_sum={sums[i]!}"
  let ratio (a b : Nat) : String :=
    let x := median times[a]! * 10000 / median times[b]!
    let f := toString (x % 10000)
    s!"{x / 10000}.{"".pushn '0' (4 - f.length) ++ f}"
  IO.println s!"[T mapped payload] viewA/handAT = {ratio 0 6}   viewB/handBT = {ratio 7 13}"
  IO.println s!"[P projection]     viewAp/handA2 = {ratio 5 3}  viewBp/handB2 = {ratio 12 10}"
  IO.println s!"[user @[inline] step] viewAi/handA2 = {ratio 4 3} viewBi/handB2 = {ratio 11 10}"
  IO.println s!"[idiomatic for/let mut] viewA/handA = {ratio 0 1}  viewB/handB = {ratio 7 8}"
  IO.println s!"[unfused view] stagedA/handAT = {ratio 2 6}  stagedB/handBT = {ratio 9 13}"
  IO.println s!"checksum mismatches={bad}"
  return if bad = 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["check"] => check
  | ["bench", n, r] => bench n.toNat! r.toNat!
  | _ => do IO.println "usage: gendemo check | gendemo bench N ROUNDS"; return 2
