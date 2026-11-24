import Iter
/-! Differential test of the trusted C++ printers. `fuzzcpp cpp N` prints a C++ program with `N` random
word pipelines (random lane counts, including 0) and `N` random record pipelines (including `/` and `%` by
zero, missing fields and parameters), each word pipeline as `sum`, `count`, `min?` and `max?` loops, each record pipeline printed twice: as `SPipe.toCpp` and as `SPipe.toCppAdapt` with
random block, window and threshold, so both bodies and the switch between them run; `fuzzcpp expect N` prints what Lean's `Pipe.run` / `SPipe.run`, the
`Iter` chains, give on the same inputs. `replay.sh` builds the C++ with UBSan and diffs the two. -/
open Iter.Gen

abbrev G := StateM UInt64

def rnd (n : Nat) : G Nat := modifyGet fun (s : UInt64) =>
  let s := s * 6364136223846793005 + 1442695040888963407
  ((s >>> 33).toNat % n, s)

def word : G UInt64 := do
  match ← rnd 4 with
  | 0 => return 0
  | 1 => return (← rnd 4).toUInt64
  | 2 => return (← rnd 1000).toUInt64
  | _ => return ((← rnd 65536).toUInt64 <<< 48) ||| (← rnd 1000000000).toUInt64

def genE : Nat → G E
  | 0 => do match ← rnd 3 with | 0 => pure .x | 1 => pure .k | _ => pure (.lit (← word))
  | d + 1 => do
    match ← rnd 7 with
    | 0 => pure .x
    | 1 => pure .k
    | 2 => pure (.lit (← word))
    | 3 => pure (.add (← genE d) (← genE d))
    | 4 => pure (.mul (← genE d) (← genE d))
    | 5 => pure (.xor (← genE d) (← genE d))
    | _ => pure (.mod (← genE d) (← genE d))

def genP : Nat → G P
  | 0 => do pure (.eq (← genE 1) (← genE 1))
  | d + 1 => do
    match ← rnd 4 with
    | 0 => pure (.eq (← genE 2) (← genE 2))
    | 1 => pure (.lt (← genE 2) (← genE 2))
    | 2 => pure (.eq (.mod (← genE 2) (.lit (← rnd 4).toUInt64)) (.lit 0))
    | _ => pure (.and (← genP d) (← genP d))

/-- fields 0–2 exist and 3 is missing; parameters 0–1 exist and 2 is missing -/
def genX : Nat → G X
  | 0 => do match ← rnd 3 with | 0 => pure (.fld (← rnd 4)) | 1 => pure (.prm (← rnd 3)) | _ => pure (.lit (← word))
  | d + 1 => do
    match ← rnd 6 with
    | 0 => pure (.fld (← rnd 4))
    | 1 => pure (.prm (← rnd 3))
    | 2 => pure (.lit (← word))
    | 3 => pure (.add (← genX d) (← genX d))
    | 4 => pure (.mul (← genX d) (← genX d))
    | _ => pure (.div (← genX d) (← genX d))

def genQ : Nat → G Q
  | 0 => do pure (.ne0 (← genX 1))
  | d + 1 => do
    match ← rnd 3 with
    | 0 => pure (.ne0 (← genX 2))
    | 1 => pure (.ge (← genX 2) (← genX 2))
    | _ => pure (.and (← genQ d) (← genQ d))

def genList (n : Nat) (g : G α) : G (List α) := (List.range n).mapM fun _ => g

structure Case where
  words : List (Nat × Pipe)
  recs : List (SPipe × Nat × Nat × Nat)
  xs : Array UInt64
  rows : Array (Row String)
  ks : List UInt64
  pss : List (List UInt64)

def gen (n : Nat) : Case := (go.run 7).1 where
  go : G Case := do
    let words ← genList n do pure (← rnd 10, ⟨← genP 2, ← genE 3⟩)
    let recs ← genList n do pure (⟨← genQ 2, ← genX 3⟩, ← rnd 10, ← rnd 10, ← rnd 25)
    let xs ← genList 37 word
    let rows ← (List.range 29).mapM fun i => do pure (⟨s!"r{i}", ← genList 3 word⟩ : Row String)
    pure ⟨words, recs, xs.toArray, rows.toArray, ← genList 3 word, ← genList 3 (genList 2 word)⟩

/-- input lengths tried: empty, one item, shorter than 8 lanes, and all -/
def lens (n : Nat) : List Nat := [0, 1, 5, n]

def expect (c : Case) : List String :=
  ((c.words ++ c.words ++ c.words ++ c.words).enum.flatMap fun (i, (_, q)) => (lens c.xs.size).flatMap fun n => c.ks.map fun k =>
    s!"W {i} {n} {k} {q.run k (c.xs.extract 0 n)}") ++
  ((c.words ++ c.words ++ c.words ++ c.words).enum.flatMap fun (i, (_, q)) => (lens c.xs.size).flatMap fun n => c.ks.map fun k =>
    s!"C {i} {n} {k} {q.count k (c.xs.extract 0 n)}") ++
  ([("N", Red.min), ("X", Red.max)].flatMap fun (t, r) => c.words.enum.flatMap fun (i, (_, q)) =>
    (lens c.xs.size).flatMap fun n => c.ks.map fun k =>
      s!"{t} {i} {n} {k} {((q.red r k (c.xs.extract 0 n)).map toString).getD "-"}") ++
  ((c.recs ++ c.recs).enum.flatMap fun (i, (q, _)) => (lens c.rows.size).flatMap fun n => c.pss.map fun ps =>
    let s := q.run ps (c.rows.extract 0 n)
    s!"R {i} {n} {ps.getD 0 0} {ps.getD 1 0} {s.count} {s.total} {s.first.getD "-"} {s.last.getD "-"}")

def cpp (c : Case) : String :=
  let u := fun (l : List UInt64) => ", ".intercalate (l.map (s!"{·}ULL"))
  let rows := ", ".intercalate (c.rows.toList.map fun r => s!"\{\"{r.label}\", {u r.f}}")
  let each := fun (f : Nat → Nat × Pipe → List String) => c.words.enum.flatMap fun (i, lq) => f i lq
  let words := each (fun i (l, q) => [(opt l q).toCpp s!"w{i}", (opt l q.countPipe).toCpp s!"c{i}",
      q.toCppRed .min l s!"n{i}", q.toCppRed .max l s!"x{i}"]) ++
    each (fun i (l, q) => [(opt l q).toCpp s!"wb{i}" true, (opt l q.countPipe).toCpp s!"cb{i}" true]) ++
    each (fun i (l, q) => [(opt l q).toCppRange s!"wr{i}", (opt l q.countPipe).toCppRange s!"cr{i}",
      (opt l q).toCppRange s!"wq{i}" false, (opt l q.countPipe).toCppRange s!"cq{i}" false])
  let fs := ["e.f0", "e.f1", "e.f2"]
  let recs := (c.recs.enum.map fun (i, (q, _)) => q.toCpp 2 s!"r{i}" "Row" fs) ++
    c.recs.enum.map fun (i, (q, b, w, d)) => q.toCppAdapt 2 s!"a{i}" "Row" fs b w d
  let calls := fun (t : String) => ", ".intercalate ((List.range c.words.length).map fun i => s!"&{t}{i}")
  let rcalls := ((List.range c.recs.length).map fun i => s!"&r{i}") ++ (List.range c.recs.length).map fun i => s!"&a{i}"
  "\n".intercalate ([
    "#include <algorithm>", "#include <cstdint>", "#include <cstdio>", "#include <optional>", "#include <string_view>",
    "#include <vector>",
    "struct Row { std::string_view name; std::uint64_t f0, f1, f2; };",
    "struct Summ { std::uint64_t count = 0, total = 0; std::string_view first, last; };"] ++ words ++ recs ++ [
    s!"static std::uint64_t (*const W[])(const std::vector<std::uint64_t>&, std::uint64_t) = \{{calls "w"}, {calls "wb"}, {calls "wr"}, {calls "wq"}};",
    s!"static std::uint64_t (*const C[])(const std::vector<std::uint64_t>&, std::uint64_t) = \{{calls "c"}, {calls "cb"}, {calls "cr"}, {calls "cq"}};",
    s!"static std::optional<std::uint64_t> (*const N[])(const std::vector<std::uint64_t>&, std::uint64_t) = \{{calls "n"}};",
    s!"static std::optional<std::uint64_t> (*const X[])(const std::vector<std::uint64_t>&, std::uint64_t) = \{{calls "x"}};",
    s!"static Summ (*const R[])(const std::vector<Row>&, std::uint64_t, std::uint64_t) = \{{", ".intercalate rcalls}};",
    "int main() {",
    s!"  const std::vector<std::uint64_t> xs = \{{u c.xs.toList}};",
    s!"  const std::vector<Row> rows = \{{rows}};",
    s!"  const std::uint64_t ks[] = \{{u c.ks}};",
    s!"  const std::uint64_t ps[][2] = \{{", ".intercalate (c.pss.map fun p => s!"\{{u p}}")}};",
    s!"  const std::size_t lw[] = \{{", ".intercalate ((lens c.xs.size).map toString)}};",
    s!"  const std::size_t lr[] = \{{", ".intercalate ((lens c.rows.size).map toString)}};",
    "  auto sv = [](std::string_view s) { return s.empty() ? std::string_view(\"-\") : s; };",
    "  for (std::size_t i = 0; i < sizeof W / sizeof *W; ++i) for (std::size_t n : lw) for (std::uint64_t k : ks)",
    "    std::printf(\"W %zu %zu %llu %llu\\n\", i, n, (unsigned long long)k,",
    "      (unsigned long long)W[i](std::vector<std::uint64_t>(xs.begin(), xs.begin() + n), k));",
    "  for (std::size_t i = 0; i < sizeof C / sizeof *C; ++i) for (std::size_t n : lw) for (std::uint64_t k : ks)",
    "    std::printf(\"C %zu %zu %llu %llu\\n\", i, n, (unsigned long long)k,",
    "      (unsigned long long)C[i](std::vector<std::uint64_t>(xs.begin(), xs.begin() + n), k));",
    "  for (auto [t, F] : {std::pair{\"N\", N}, std::pair{\"X\", X}})",
    "    for (std::size_t i = 0; i < sizeof N / sizeof *N; ++i) for (std::size_t n : lw) for (std::uint64_t k : ks) {",
    "      auto o = F[i](std::vector<std::uint64_t>(xs.begin(), xs.begin() + n), k);",
    "      if (o) std::printf(\"%s %zu %zu %llu %llu\\n\", t, i, n, (unsigned long long)k, (unsigned long long)*o);",
    "      else std::printf(\"%s %zu %zu %llu -\\n\", t, i, n, (unsigned long long)k);",
    "    }",
    "  for (std::size_t i = 0; i < sizeof R / sizeof *R; ++i) for (std::size_t n : lr) for (auto& p : ps) {",
    "    Summ s = R[i](std::vector<Row>(rows.begin(), rows.begin() + n), p[0], p[1]);",
    "    std::printf(\"R %zu %zu %llu %llu %llu %llu %.*s %.*s\\n\", i, n, (unsigned long long)p[0], (unsigned long long)p[1],",
    "      (unsigned long long)s.count, (unsigned long long)s.total, (int)sv(s.first).size(), sv(s.first).data(),",
    "      (int)sv(s.last).size(), sv(s.last).data());",
    "  }",
    "}"])

def main (args : List String) : IO Unit := do
  let n := (args.getD 1 "300").toNat!
  match args.head? with
  | some "cpp" => IO.println (cpp (gen n))
  | _ => IO.println ("\n".intercalate (expect (gen n)))
