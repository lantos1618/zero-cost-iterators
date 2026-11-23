import TaskCore
/-! Fixed-seed generated-input check for the three `tasks` commands. The generator produces BOTH the file
text and its structured meaning; expected answers come from straightforward independent reference code
over that meaning (no `.view()`, no parser). Also: mutants that the comparison must catch, and an EAGER
control (`taskcheck eager FILE`) that evaluates the same traced predicate on every line. -/
open Tasks

structure G where s : Nat
def G.next (g : G) : Nat × G := let s := (g.s * 6364136223846793005 + 1442695040888963407) % 18446744073709551616; (s / 65536, ⟨s⟩)
def rnd (n : Nat) : StateM G Nat := modifyGet fun g => let (x, g') := g.next; (x % n, g')
def pick {α} [Inhabited α] (xs : List α) : StateM G α := do return xs[← rnd xs.length]!

/-! ### logsum -/
def genLog : StateM G (String × List LogRec × LogOpts) := do
  let n ← rnd 30
  let n := if (← rnd 7) == 0 then 0 else n
  let crlf := (← rnd 5) == 0
  let mut lines : Array String := #[]
  let mut recs : Array LogRec := #[]
  for i in [0:n] do
    if (← rnd 6) == 0 then lines := lines.push (← pick ["", "# comment", "#"])
    let lv ← pick ["INFO", "WARN", "ERROR", "ERROR"]
    let sv ← pick ["api", "db", "web"]
    let c ← rnd 9; let big ← rnd 1000; let small ← rnd 10
    let lat := if c == 0 then 10 ^ 20 + big else small * 100
    let r : LogRec := ⟨lines.size + 1, s!"2026-01-01T00:00:{i}Z", lv, sv, lat, s!"/p{← rnd 5}"⟩
    recs := recs.push r
    lines := lines.push s!"{r.ts} {r.level} {r.service} {r.latency} {r.path}"
  let eol := if crlf then "\r\n" else "\n"
  let txt := String.intercalate eol lines.toList ++ (if (← rnd 2) == 0 && lines.size > 0 then eol else "")
  let o : LogOpts := { level := ← pick ["ERROR", "ERROR", "WARN", "INFO"],
                       service := ← pick [none, none, some "api", some "db", some "nosuch"],
                       minLatency := ← pick [0, 0, 300, 10 ^ 21] }
  return (txt, recs.toList, o)

/-- independent reference: select, then compute each field separately (max by a second pass) -/
def refLog (o : LogOpts) (rs : List LogRec) : Nat × Nat × Nat × Nat × Option Nat × Option Nat :=
  let sel := rs.filter fun r => r.level = o.level ∧ (o.service = none ∨ o.service = some r.service) ∧ r.latency ≥ o.minLatency
  let mx := sel.foldl (fun m r => max m r.latency) 0
  let mxLine := match sel.find? (fun r => r.latency = mx) with | some r => r.line | none => 0
  (sel.length, (sel.map (·.latency)).foldl (· + ·) 0, mx, mxLine, sel.head?.map (·.line), sel.getLast?.map (·.line))

def summOf (s : LogSumm) : Nat × Nat × Nat × Nat × Option Nat × Option Nat :=
  (s.count, s.total, s.maxLat, s.maxLine, s.first.map (·.line), s.last.map (·.line))

/-- MUTANT: ties keep the LAST maximal line -/
def logStepGe (s : LogSumm) (h : Hit) : LogSumm :=
  let nm : Bool := s.count == 0 || decide (h.latency ≥ s.maxLat)
  { logStep s h with maxLat := if nm then h.latency else s.maxLat, maxLine := if nm then h.line else s.maxLine }

/-! ### sales -/
def genSales : StateM G (String × List Sale × SalesOpts) := do
  let n ← rnd 26
  let n := if (← rnd 8) == 0 then 0 else n
  let mut lines : Array String := #[salesHeader]
  let mut rows : Array Sale := #[]
  for _ in [0:n] do
    if (← rnd 8) == 0 then lines := lines.push ""
    let p ← pick ["apple", "pear", "fig", "kiwi", "plum", "Fig", "dragon fruit"]
    let q ← rnd 10
    let c ← rnd 10; let big ← rnd 100; let small ← rnd 1000
    let u := if c == 0 then 10 ^ 18 + big else small
    let st ← pick ["paid", "paid", "paid", "refunded"]
    let r : Sale := ⟨lines.size + 1, p, q, u, st⟩
    rows := rows.push r
    lines := lines.push s!"{p},{q},{u},{st}"
  let txt := String.intercalate "\n" lines.toList ++ "\n"
  return (txt, rows.toList, { minQty := ← pick [0, 0, 3, 100] })

/-- independent reference: first-seen keys by an explicit scan, then per-key sums by re-filtering -/
def refSales (o : SalesOpts) (rs : List Sale) : List (String × Nat × Nat × Nat) :=
  let kept := rs.filter fun s => s.status = "paid" ∧ s.qty ≥ o.minQty
  let keys := kept.foldl (fun ks s => if ks.contains s.product then ks else ks ++ [s.product]) []
  keys.map fun k =>
    let mine := kept.filter (·.product = k)
    (k, mine.length, (mine.map (·.qty)).foldl (· + ·) 0, (mine.map fun s => s.qty * s.unitCents).foldl (· + ·) 0)

def flat (g : List (String × Agg)) : List (String × Nat × Nat × Nat) := g.map fun (k, a) => (k, a.lines, a.units, a.cents)

/-- MUTANT: a new key is inserted at the FRONT of the table -/
def frontIns (t : List (String × Agg)) (r : String × Nat × Nat) : List (String × Agg) :=
  match t.find? (·.1 == r.1) with
  | some _ => t.map fun (k, a) => if k == r.1 then (k, aggStep a r) else (k, a)
  | none => (r.1, aggStep agg0 r) :: t

/-! ### manifest -/
def validLine : StateM G String := do
  let d ← pick ["assets", "docs", "bin", "a/b", "ünï"]
  let f ← pick ["x.png", "readme.md", "tool", "c.d.e"]
  let sz ← pick ["0", "7", "2048", "1048576"]
  let h ← pick ["9f86d081", "00000000", "deadbeef", "0badc0de"]
  return s!"{d}/{f} {sz} {h}"

/-- (line text, reason the rule must give) — each mutation triggers exactly one known rule -/
def badLine : StateM G (String × String) := do
  match ← rnd 9 with
  | 0 => return ("a/../b 1 00000000", "path contains '..'")
  | 1 => return ("/etc/passwd 1 00000000", "absolute path")
  | 2 => return ("a//b 1 00000000", "empty path segment")
  | 3 => return ("a/b 007 00000000", "size has a leading zero, got '007'")
  | 4 => return ("a/b 1 DEADBEEF", "checksum must be 8 lowercase hex digits, got 'DEADBEEF'")
  | 5 => return ("a/b 1 abc", "checksum must be 8 lowercase hex digits, got 'abc'")
  | 6 => return ("a/b 1", "expected 3 space-separated fields, got 2")
  | 7 => return ("", "expected 3 space-separated fields, got 1")
  | _ => return ("☃ ünï ✓", "size must be decimal digits, got 'ünï'")

def genManifest : StateM G (String × List String × Option (Nat × String)) := do
  let n ← rnd 20
  let mut ls : Array String := #[]
  let mut first : Option (Nat × String) := none
  for i in [0:n] do
    if (← rnd 8) == 0 then
      let (l, why) ← badLine
      if first.isNone then first := some (i, why)
      ls := ls.push l
    else ls := ls.push (← validLine)
  let txt := if ls.isEmpty then "" else String.intercalate "\n" ls.toList ++ "\n"
  return (txt, ls.toList, first)

def main (args : List String) : IO UInt32 := do
  if let ["eager", path] := args then
    let ls := splitLines (← IO.FS.readFile path)
    -- EAGER control: evaluate the same traced predicate on EVERY line, then pick the first
    let flags := ls.enum.map fun e => (e, entryBad true e)
    IO.println s!"eager first invalid: {(flags.find? (·.2)).map (·.1.1 + 1)}"
    return 0
  let N := 300
  let mut g : G := ⟨20261122⟩
  let mut bad := 0
  -- logsum
  let mut lf := 0; let mut lpf := 0; let mut lm := 0; let mut lEmpty := 0; let mut lNone := 0
  for _ in [0:N] do
    let ((txt, recs, o), g') := genLog.run g; g := g'
    match parseLines parseLogLine logSkip (splitLines txt) with
    | .ok rs => if rs != recs then lpf := lpf + 1
    | .error _ => lpf := lpf + 1
    let want := refLog o recs
    match logPipe o recs with
    | .ok s => if summOf s != want then lf := lf + 1
    | .error _ => lf := lf + 1
    if recs.isEmpty then lEmpty := lEmpty + 1
    if want.1 == 0 then lNone := lNone + 1
    match (recs.view.filter (logKeep o) |>.map toHit |>.fuse |>.foldl logS0 logStepGe) with
    | .ok s => if summOf s != want then lm := lm + 1
    | .error _ => pure ()
  IO.println s!"TASKCHECK logsum inputs={N} empty={lEmpty} zero_matches={lNone} parse_mismatch={lpf} pipeline_vs_reference_fails={lf} tie_mutant_caught={lm}"
  -- sales
  let mut sf := 0; let mut spf := 0; let mut sm := 0; let mut sEmpty := 0; let mut sNone := 0; let mut sRep := 0
  for _ in [0:N] do
    let ((txt, rows, o), g') := genSales.run g; g := g'
    match parseSales (splitLines txt) with
    | .ok rs => if rs != rows then spf := spf + 1
    | .error _ => spf := spf + 1
    let want := refSales o rows
    match salesPipe o rows with
    | .ok t => if flat t != want then sf := sf + 1
    | .error _ => sf := sf + 1
    if rows.isEmpty then sEmpty := sEmpty + 1
    if want.isEmpty then sNone := sNone + 1
    if want.any (fun (_, l, _, _) => l ≥ 2) then sRep := sRep + 1
    match (rows.view.filter (saleKeep o) |>.map saleLine |>.fuse |>.foldl [] frontIns) with
    | .ok t => if flat t != want then sm := sm + 1
    | .error _ => pure ()
  IO.println s!"TASKCHECK sales inputs={N} empty={sEmpty} zero_kept={sNone} with_repeated_key={sRep} parse_mismatch={spf} pipeline_vs_reference_fails={sf} front_insert_mutant_caught={sm}"
  -- manifest
  let mut mf := 0; let mut mpf := 0; let mut mm := 0; let mut mInv := 0; let mut mOk := 0
  for _ in [0:N] do
    let ((txt, ls, want), g') := genManifest.run g; g := g'
    if splitLines txt != ls then mpf := mpf + 1
    let got := match manifestPipe false ls with
      | .ok (some (i, l)) => some (i, (checkEntry l).getD "?")
      | _ => none
    if got != want then mf := mf + 1
    let wantPulls := match want with | some (i, _) => i + 1 | none => ls.length
    if manifestPulls false ls != wantPulls then mf := mf + 1
    if want.isSome then mInv := mInv + 1 else mOk := mOk + 1
    -- MUTANT: report the LAST invalid entry
    let last := (ls.enum.filter (fun e => (checkEntry e.2).isSome)).getLast?.map fun (i, l) => (i, (checkEntry l).getD "?")
    if last != want then mm := mm + 1
  IO.println s!"TASKCHECK manifest inputs={N} invalid={mInv} valid={mOk} split_mismatch={mpf} pipeline_or_pull_count_vs_reference_fails={mf} last_invalid_mutant_caught={mm}"
  bad := lpf + lf + spf + sf + mpf + mf
  let caught := lm > 0 && sm > 0 && mm > 0
  IO.println s!"TASKCHECK fails={bad} mutants_all_caught={caught}"
  return if bad == 0 && caught then 0 else 1
