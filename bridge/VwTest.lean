import Vw
/-! Runtime tests for the view rows (Lean compiled runtime). Exit 1 on any failure. -/
open Vw

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2^64

/-- independent stable insertion sort -/
def insSort {α} (le : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => ins x acc) []
where ins (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le y x then y :: ins x ys else x :: y :: ys
/-- independent consecutive grouping, compares with the run's last element -/
def runs {α} (eq : α → α → Bool) (xs : List α) : List (List α) :=
  (xs.foldl (fun (acc : List (List α)) x => match acc with
    | (g :: gs) => if eq (g.getLast?.getD x) x then (g ++ [x]) :: gs else [x] :: g :: gs
    | [] => [[x]]) []).reverse
/-- independent first-occurrence dedup -/
def dedup {α} [BEq α] (xs : List α) : List α :=
  (xs.foldl (fun (acc : List α) x => if acc.contains x then acc else x :: acc) []).reverse

def toCs (bs : List Nat) : Option (List Nat) :=
  (String.fromUTF8? (ByteArray.mk (bs.map (·.toUInt8)).toArray)).map fun s => s.toList.map Char.toNat

/-! lambda subset C printer (trusted printer, differentially tested): every node is computed in
int64 from int32-range operands, then range-checked; a failed check returns trap = 1 -/
partial def cE : {t : Lam.Ty} → Lam.E t → StateM (Nat × String) String
  | _, .x => leaf "x" | _, .cap => leaf "c" | _, .lit n => leaf s!"(int64_t){n}LL"
  | _, .add a b => bin "+" a b true | _, .sub a b => bin "-" a b true | _, .mul a b => bin "*" a b true
  | _, .max a b => do let u ← cE a; let v ← cE b; node s!"({u} <= {v} ? {v} : {u})" false
  | _, .lt a b => do let u ← cE a; let v ← cE b; node s!"({u} < {v})" false
  | _, .eq a b => do let u ← cE a; let v ← cE b; node s!"({u} == {v})" false
  | _, .and a b => do let u ← cE a; let v ← cE b; node s!"({u} != 0 && {v} != 0)" false
  | _, .not a => do let u ← cE a; node s!"({u} == 0)" false
where
  node (rhs : String) (chk : Bool) : StateM (Nat × String) String := do
    let (k, acc) ← get
    let v := s!"t{k}"
    let line := s!"  int64_t {v} = {rhs};\n" ++
      (if chk then s!"  if ({v} < INT32_MIN || {v} > INT32_MAX) return 1;\n" else "")
    set (k + 1, acc ++ line); pure v
  leaf (r : String) : StateM (Nat × String) String := node r true
  bin {t1 t2 : Lam.Ty} (o : String) (a : Lam.E t1) (b : Lam.E t2) (chk : Bool) : StateM (Nat × String) String := do
    let u ← cE a; let v ← cE b; node s!"({u} {o} {v})" chk

def cFun (name : String) (e : Lam.E t) : String :=
  let (r, (_, body)) := (cE e).run (0, "")
  s!"static int {name}(int64_t x, int64_t c, int64_t *out) \{\n{body}  *out = {r};\n  return 0;\n}\n"

def lams : List (String × (Σ t, Lam.E t)) :=
  [("pred", ⟨_, Lam.pred⟩),
   ("affine", ⟨_, .add (.mul .x .cap) (.lit 7)⟩),
   ("sq_minus", ⟨_, .sub (.mul .x .x) .cap⟩),
   ("clamp", ⟨_, .max (.sub .x .cap) (.lit 0)⟩),
   ("band", ⟨_, .and (.lt .cap .x) (.not (.eq .x (.lit 0)))⟩)]

def edge : List Int := [-2147483648, -2147483647, -46341, -46340, -65536, -1, 0, 1, 2, 7, 46340, 46341, 65535, 2147483646, 2147483647]

def main (args : List String) : IO UInt32 := do
  let out := args.headD "."
  let mut fails := 0
  -- 1. UTF-8: reference encoder vs Lean runtime for EVERY scalar value
  let mut nsc := 0
  for v in List.range 0x110000 do
    if v < 0xD800 || v ≥ 0xE000 then
      nsc := nsc + 1
      if (Char.ofNat v).toString.toUTF8.toList.map (·.toNat) != Utf8.enc1 v then fails := fails + 1
  IO.println s!"utf8 enc1 = String.toUTF8 on all {nsc} scalar values: fails={fails}"
  -- 2. UTF-8: decoder vs Lean runtime validator on random + biased byte strings
  let pool : Array Nat := #[0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1, 0xED, 0xEE, 0xEF, 0xF0, 0xF1, 0xF4, 0xF5, 0xFF]
  let mut s := 12345
  let mut agree := 0; let mut valid := 0; let mut f2 := 0
  for _ in List.range 300000 do
    s := lcg s; let len := (s / 2^33) % 9
    let mut bs : List Nat := []
    for _ in List.range len do
      s := lcg s
      let b := if (s / 2^40) % 4 == 0 then (s / 2^20) % 256 else pool[(s / 2^24) % pool.size]!
      bs := bs ++ [b]
    let d := Utf8.dec bs
    if d == toCs bs then agree := agree + 1 else f2 := f2 + 1
    if d.isSome then valid := valid + 1
  IO.println s!"utf8 dec vs String.fromUTF8?: 300000 cases, agree={agree} (valid={valid}) fails={f2}"
  fails := fails + f2
  for str in ["", "abc", "é€😀", "naïve café", String.mk [Char.ofNat 0x10FFFF, Char.ofNat 0xE000, Char.ofNat 0xD7FF]] do
    let bs := str.toUTF8.toList.map (·.toNat)
    if Utf8.dec bs != some (str.toList.map Char.toNat) then fails := fails + 1
    let nb := (str.toList.view.map (fun _ => 1) |>.fuse).items.length
    IO.println s!"  {repr str}: bytes={bs.length} scalars={(Utf8.dec bs).map List.length} view-scalars={nb}"
  -- 3. sort / groupBy / distinct vs independent references, fused and unfused
  let mut f3 := 0
  for t in List.range 2000 do
    s := lcg (s + t); let len := (s / 2^33) % 12
    let mut xs : List (Nat × Nat) := []
    for i in List.range len do s := lcg s; xs := xs ++ [((s / 2^35) % 4, i)]
    let le := fun (a b : Nat × Nat) => decide (a.1 ≤ b.1)
    let eq := fun (a b : Nat × Nat) => a.1 == b.1
    for fz in [false, true] do
      let base : View (Nat × Nat) := { xs.view with fused := fz }
      if (base.sortBy le).items != insSort le xs then f3 := f3 + 1
      if (base.groupBy eq).items != runs eq xs then f3 := f3 + 1
      if (base.map (·.1)).distinct.items != dedup (xs.map (·.1)) then f3 := f3 + 1
      if (base.map (·.1) |>.filter (· > 0) |>.sortBy (· ≤ ·) |>.map (· * 2)).segments != 2 then f3 := f3 + 1
  IO.println s!"sort/groupBy/distinct vs independent refs, 2000 lists x fused/unfused: fails={f3}"
  fails := fails + f3
  -- 4. lambda subset: Lean source eval vs stack lowering at runtime, and emit C with expected results
  let mut f4 := 0
  let mut c := "#include <stdint.h>\n#include <stdio.h>\n"
  let mut tests := ""
  let mut ntest := 0
  for (nm, ⟨t, e⟩) in lams do
    c := c ++ cFun nm e
    for x in edge do
      for cc in edge do
        let ev := (Lam.eval e x cc).map Lam.enc
        if Lam.exec x cc (Lam.compile e) [] != ev.map (·  :: []) then f4 := f4 + 1
        let (tr, v) := match ev with | some v => (0, v) | none => (1, 0)
        tests := tests ++ s!"  r = {nm}({x}LL, {cc}LL, &o); if (r != {tr} || (r == 0 && o != {v}LL)) \{ bad++; printf(\"MISMATCH {nm} x={x} c={cc}\\n\"); } n++;\n"
        ntest := ntest + 1
  c := c ++ "int main(void) {\n  int64_t o = 0; int r, bad = 0, n = 0;\n" ++ tests ++
    "  printf(\"lambda C vs Lean eval: %d cases, %d mismatches\\n\", n, bad);\n  return bad != 0;\n}\n"
  IO.FS.writeFile s!"{out}/lam_test.c" c
  IO.println s!"lambda stack lowering vs eval at runtime: {ntest} cases, fails={f4}; wrote {out}/lam_test.c"
  fails := fails + f4
  IO.println s!"VWTEST fails={fails}"
  pure (if fails == 0 then 0 else 1)
