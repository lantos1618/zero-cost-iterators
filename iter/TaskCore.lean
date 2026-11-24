import Iter
/-! Everyday file-driven tasks on the `Iter` API.
Parsing, file reading and report formatting are ordinary code OUTSIDE the pipelines and are NOT
covered by any theorem. Each task's computation is one `Iter` chain below (`logPipe`, `salesPipe`,
`manifestPipe`), tied to its staged list meaning by composing the generic `Denotes` lemmas. -/
open Iter

namespace Tasks

/-- text → lines: split on '\n'; one trailing '\r' per line is stripped; the empty piece after a final
'\n' is dropped (so "" has 0 lines and "a\n" has 1). The whole file is already in memory. -/
def splitLines (s : String) : List String :=
  let ps := (s.splitOn "\n").map (fun l => if l.endsWith "\r" then l.dropRight 1 else l)
  match ps.getLast? with
  | some "" => ps.dropLast
  | _ => ps

def isNatStr (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/-- exact integer cents → "D.CC" -/
def dollars (c : Nat) : String :=
  toString (c / 100) ++ "." ++ (if c % 100 < 10 then "0" else "") ++ toString (c % 100)

/-- parse every non-skipped line (1-based line numbers from `start`); first error wins -/
def parseLines {α : Type} (parse : Nat → String → Except String α) (skip : String → Bool)
    (ls : List String) (start : Nat := 1) : Except (Nat × String) (List α) :=
  let r := (ls.enumFrom start).foldl (fun (acc : Except (Nat × String) (List α)) (nl : Nat × String) => match acc with
    | .error e => .error e
    | .ok out => if skip nl.2 then .ok out else match parse nl.1 nl.2 with
        | .ok x => .ok (x :: out)
        | .error m => .error (nl.1, m)) (.ok [])
  r.map List.reverse

/-! ## 1. logsum: access-log summary (filter → map → fuse → foldl) -/

/-- one record = `TS LEVEL SERVICE LATENCY_MS PATH`, single spaces, LEVEL ∈ {INFO, WARN, ERROR},
LATENCY_MS decimal digits (exact Nat, no size limit). Empty lines and lines starting with '#' are skipped. -/
structure LogRec where
  line : Nat
  ts : String
  level : String
  service : String
  latency : Nat
  path : String
  deriving Repr, BEq, DecidableEq

def logSkip (l : String) : Bool := l.isEmpty || l.startsWith "#"

def parseLogLine (n : Nat) (l : String) : Except String LogRec :=
  match l.splitOn " " with
  | [ts, lv, sv, lat, p] =>
    if ts.isEmpty || sv.isEmpty || p.isEmpty then .error "empty field (fields are separated by single spaces)"
    else if !(lv == "INFO" || lv == "WARN" || lv == "ERROR") then
      .error s!"level must be INFO, WARN or ERROR, got '{lv}'"
    else if !isNatStr lat then .error s!"latency_ms must be decimal digits, got '{lat}'"
    else .ok ⟨n, ts, lv, sv, lat.toNat!, p⟩
  | fs => .error s!"expected 5 space-separated fields, got {fs.length}"

structure LogOpts where
  level : String := "ERROR"
  service : Option String := none
  minLatency : Nat := 0

/-- the visible selection condition -/
def logKeep (o : LogOpts) (r : LogRec) : Bool :=
  r.level == o.level &&
  (match o.service with | none => true | some s => r.service == s) &&
  decide (r.latency ≥ o.minLatency)

structure Hit where
  line : Nat
  latency : Nat
  desc : String
  deriving Repr, BEq, DecidableEq

def toHit (r : LogRec) : Hit := ⟨r.line, r.latency, r.ts ++ " " ++ r.service ++ " " ++ r.path⟩

/-- bounded report state: count, exact total, max (FIRST line attaining it), first and last hit -/
structure LogSumm where
  count : Nat := 0
  total : Nat := 0
  maxLat : Nat := 0
  maxLine : Nat := 0
  first : Option Hit := none
  last : Option Hit := none
  deriving Repr, BEq, DecidableEq

def logS0 : LogSumm := {}

def logStep (s : LogSumm) (h : Hit) : LogSumm :=
  let newMax : Bool := s.count == 0 || decide (h.latency > s.maxLat)
  { count := s.count + 1, total := s.total + h.latency,
    maxLat := if newMax then h.latency else s.maxLat,
    maxLine := if newMax then h.line else s.maxLine,
    first := if s.count == 0 then some h else s.first,
    last := some h }

/-- THE logsum call site -/
def logPipe (o : LogOpts) (rs : List LogRec) : LogSumm :=
  rs.iter.filter (logKeep o) |>.map toHit |>.foldl logS0 logStep

theorem logPipe_spec (o : LogOpts) (rs : List LogRec) :
    logPipe o rs = ((rs.filter (logKeep o)).map toHit).foldl logStep logS0 :=
  (((denotes_list rs).filter _).map _).foldl _ _

def logReport (file : String) (nLines nRecs : Nat) (o : LogOpts) (s : LogSumm) : String :=
  let svc := match o.service with | none => "*" | some x => x
  let hit : Option Hit → String := fun | none => "none" | some h => s!"line {h.line} {h.desc}"
  String.intercalate "\n" [
    s!"file: {file}",
    s!"lines: {nLines} (records: {nRecs}, skipped blank/comment: {nLines - nRecs})",
    s!"filter: level={o.level} service={svc} min_latency_ms={o.minLatency}",
    s!"matches: {s.count}",
    s!"total_latency_ms: {s.total}",
    (if s.count == 0 then "max_latency_ms: none" else s!"max_latency_ms: {s.maxLat} (first at line {s.maxLine})"),
    s!"first: {hit s.first}",
    s!"last: {hit s.last}"] ++ "\n"

/-! ## 2. sales: sales by product (filter → map → fuse → groupFold, String keys) -/

/-- CSV dialect: first line is exactly `product,qty,unit_cents,status`; then one row per line,
4 fields split on ',', NO quoting/escaping (a ',' inside a field is a field-count error), no trimming;
product non-empty; qty = units sold (decimal Nat, 0 allowed); unit_cents = price per unit in integer
cents (decimal Nat); status ∈ {paid, refunded}. Empty lines after the header are skipped. -/
structure Sale where
  line : Nat
  product : String
  qty : Nat
  unitCents : Nat
  status : String
  deriving Repr, BEq, DecidableEq

def salesHeader : String := "product,qty,unit_cents,status"

def parseSaleLine (n : Nat) (l : String) : Except String Sale :=
  match l.splitOn "," with
  | [p, q, u, st] =>
    if p.isEmpty then .error "empty product"
    else if !isNatStr q then .error s!"qty must be decimal digits, got '{q}'"
    else if !isNatStr u then .error s!"unit_cents must be decimal digits, got '{u}'"
    else if !(st == "paid" || st == "refunded") then .error s!"status must be paid or refunded, got '{st}'"
    else .ok ⟨n, p, q.toNat!, u.toNat!, st⟩
  | fs => .error s!"expected 4 comma-separated fields (no quoting), got {fs.length}"

def parseSales (ls : List String) : Except (Nat × String) (List Sale) :=
  match ls with
  | [] => .error (1, s!"missing header (expected '{salesHeader}')")
  | h :: rest =>
    if h != salesHeader then .error (1, s!"expected header '{salesHeader}'")
    else parseLines parseSaleLine (·.isEmpty) rest 2

structure SalesOpts where
  minQty : Nat := 0

/-- the visible selection condition: refunded rows are excluded -/
def saleKeep (o : SalesOpts) (s : Sale) : Bool := s.status == "paid" && decide (s.qty ≥ o.minQty)

structure Agg where
  lines : Nat := 0
  units : Nat := 0
  cents : Nat := 0
  deriving Repr, BEq, DecidableEq

def agg0 : Agg := {}

/-- line revenue = qty × unit_cents, exact -/
def saleLine (s : Sale) : String × Nat × Nat := (s.product, s.qty, s.qty * s.unitCents)
def aggStep (a : Agg) (r : String × Nat × Nat) : Agg := ⟨a.lines + 1, a.units + r.2.1, a.cents + r.2.2⟩

/-- THE sales call site -/
def salesPipe (o : SalesOpts) (rs : List Sale) : List (String × Agg) :=
  rs.iter.filter (saleKeep o) |>.map saleLine |>.groupFold (·.1) agg0 aggStep

theorem salesPipe_spec (o : SalesOpts) (rs : List Sale) :
    salesPipe o rs = groupRef (·.1) agg0 aggStep ((rs.filter (saleKeep o)).map saleLine) :=
  (((denotes_list rs).filter _).map _).groupFold _ _ _

/-- output keys are the kept products in first-seen order, each once -/
theorem salesPipe_keys (o : SalesOpts) (rs : List Sale) :
    (salesPipe o rs).map Prod.fst = dedupRef ((rs.filter (saleKeep o)).map Sale.product) := by
  rw [salesPipe_spec]; simp [groupRef, List.map_map, Function.comp_def, saleLine]

def salesReport (file : String) (nRows : Nat) (o : SalesOpts) (g : List (String × Agg)) : String :=
  let tot := g.foldl (fun (t : Agg) (kv : String × Agg) => ⟨t.lines + kv.2.lines, t.units + kv.2.units, t.cents + kv.2.cents⟩) {}
  let row := fun (k : String) (a : Agg) => s!"{k},{a.lines},{a.units},{a.cents},{dollars a.cents}"
  String.intercalate "\n" ([
    s!"file: {file}",
    s!"rows: {nRows} (kept: {tot.lines}; filter: status=paid min_qty={o.minQty})",
    "product,lines,units,revenue_cents,revenue"] ++ g.map (fun kv => row kv.1 kv.2) ++ [row "TOTAL" tot]) ++ "\n"

/-! ## 3. manifest: first invalid entry (enumerate → fuse → find) -/

def isLowerHex (c : Char) : Bool := c.isDigit || (c.toNat ≥ 97 && c.toNat ≤ 102)

/-- every line (including empty ones) is an entry `PATH SIZE CHECKSUM`, single spaces.
Rules, checked in this order: 3 fields; PATH not absolute; no '..' segment; no empty segment;
SIZE decimal digits without a leading zero; CHECKSUM exactly 8 lowercase hex digits.
`none` = valid, `some reason` = invalid. -/
def checkEntry (l : String) : Option String :=
  match l.splitOn " " with
  | [p, sz, h] =>
    let segs := p.splitOn "/"
    if p.startsWith "/" then some "absolute path"
    else if segs.any (· == "..") then some "path contains '..'"
    else if segs.any (·.isEmpty) then some "empty path segment"
    else if !isNatStr sz then some s!"size must be decimal digits, got '{sz}'"
    else if sz.length > 1 && sz.startsWith "0" then some s!"size has a leading zero, got '{sz}'"
    else if h.length != 8 || !h.all isLowerHex then some s!"checksum must be 8 lowercase hex digits, got '{h}'"
    else none
  | fs => some s!"expected 3 space-separated fields, got {fs.length}"

/-- THE predicate the CLI uses; with `tr = true` the same predicate also writes one stderr line per call -/
def entryBad (tr : Bool) (e : Nat × String) : Bool :=
  if tr then dbgTrace s!"trace: pred line {e.1 + 1}" fun _ => (checkEntry e.2).isSome
  else (checkEntry e.2).isSome

theorem entryBad_trace (e : Nat × String) : entryBad true e = entryBad false e := by
  simp [entryBad, dbgTrace]

/-- THE manifest call site (index is 0-based; line = index + 1); stops at the first invalid entry -/
def manifestPipe (tr : Bool) (ls : List String) : Option (Nat × String) :=
  ls.iter.enumerate.find? (entryBad tr)

theorem manifestPipe_spec (tr : Bool) (ls : List String) :
    manifestPipe tr ls = ls.enum.find? (entryBad tr) :=
  (denotes_list ls).enumerate.find? _

/-- items the same chain pulls before stopping, counted by a `for` loop over it in `StateM` -/
def manifestPulls (tr : Bool) (ls : List String) : Nat :=
  let run : StateM Nat (Option (Nat × String)) := do
    for e in ls.iter.enumerate do
      modify (· + 1)
      if entryBad tr e then return some e
    return none
  (run.run 0).2

end Tasks
