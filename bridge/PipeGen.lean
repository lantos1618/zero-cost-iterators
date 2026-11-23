import Bridge
import Pipe.Chains
import Pipe.Emit
import Vw.PairView
open IR Check Pipe Chains

/-- (output label, chain, kernel whose contract it is checked against) -/
def registry : List (String × Reduced × String) :=
  [("dot", dot, "dot"), ("l1", l1, "l1"), ("l2", l2, "l2"), ("ham", ham, "ham"), ("osl", osl, "osl"),
   ("qz7", qz7, "l1")]
def controls : List (String × Reduced × String) :=
  [("l1_drop_abs", l1_drop_abs, "l1"), ("l1_abs_to_sq", l1_abs_to_sq, "l1"), ("l1_extra_sq", l1_extra_sq, "l1"),
   ("dot_to_sub", dot_to_sub, "dot"), ("dot_extra_abs", dot_extra_abs, "dot"),
   ("ham_swap_order", ham_swap_order, "ham"), ("ham_mul_zip", ham_mul_zip, "ham"),
   ("osl_to_abs", osl_to_abs, "osl"), ("osl_twice", osl_twice, "osl"), ("l2_to_mul", l2_to_mul, "l2")]

/-- the `.view()` entry point: same labels as `.loop()`, so the emitted bytes must be identical -/
def viewRegistry : List (String × Except String Reduced × String) :=
  [("dot", BytePairs.view.map multiply |>.fuse |>.accumulate 0, "dot"),
   ("l1", BytePairs.view.map subtract |>.map abs |>.fuse |>.accumulate 0, "l1"),
   ("l2", BytePairs.view.map subtract |>.map square |>.fuse |>.accumulate 0, "l2"),
   ("ham", BytePairs.view.map subtract |>.map nonzero |>.fuse |>.accumulate 0, "ham"),
   ("osl", BytePairs.view.map subtract |>.map clampNeg |>.fuse |>.accumulate 0, "osl")]
/-- requests that must be refused at terminal selection -/
def viewRefusals : List (String × Except String Reduced) :=
  [("dot_no_fuse", BytePairs.view.map multiply |>.accumulate 0),
   ("dot_seed5", BytePairs.view.map multiply |>.fuse |>.accumulate 5)]

def refK : String → List Int → List Int → Int
  | "l1" => refL1 | "l2" => refL2 | "ham" => refHam | "osl" => refOsl | _ => refDot

def lcg (seed n : Nat) : List Int :=
  (List.range n).map fun i => (((seed * 1103515245 + 12345 * (i + 1) * 2654435761) / 65536) % 256 : Nat) - 128

def vectors : List (List Int × List Int) :=
  [([], []), ([-128, 127, -128, 127], [-128, -128, 127, 127]), ([127, 127, 127], [-128, -128, -128]),
   ([-128, -128, -128], [127, 127, 127]), ([3, -5, 7], [-2, 4, 1]), ([0, 2, -1], [2, 0, 1]),
   ([5, -5], [5, -5]), (lcg 1 128, lcg 2 128), (lcg 3 128, lcg 4 128), (lcg 5 37, lcg 6 37)]

def emitOne (dir label : String) (r : Reduced) (k : String) : IO Bool := do
  let some c := emitC label r | IO.println s!"{label}: EMIT FAIL (op outside the checker table)"; return false
  let b := emitBend label r
  IO.FS.createDirAll dir
  IO.FS.writeFile s!"{dir}/i8dot.c" c
  IO.FS.writeFile s!"{dir}/prog.bend" b
  let ok := vectors.all fun (xs, ys) => r.den xs ys == refK k xs ys
  let g := match gate c b true with
    | .pass p => if p = lower r then "PASS (term = lower chain)" else "PASS but term ≠ lower chain"
    | .rejectC e => s!"REJECT C: {e}" | .rejectBend e => s!"REJECT Bend: {e}"
    | .mismatch _ _ => "MISMATCH" | .uncertified _ => "UNCERTIFIED"
  IO.println s!"{label}: chain={reprStr r}"
  IO.println s!"  lowered={reprStr (lower r)} derived_guard={r.guard} checker_bound={bound (lower r)}"
  IO.println s!"  in-process exact gate: {g}"
  IO.println s!"  contract[{k}] den=ref on {vectors.length} deterministic vectors: {if ok then "OK" else "FAIL"}"
  pure true

def main (args : List String) : IO UInt32 := do
  match args with
  | [out] =>
    let mut ok := true
    for (l, r, k) in registry do ok := ok && (← emitOne s!"{out}/{l}" l r k)
    for (l, r, k) in controls do ok := ok && (← emitOne s!"{out}/controls/{l}" l r k)
    for (l, v, k) in viewRegistry do
      match v with
      | .ok r => IO.println s!"view entry {l}:"; ok := ok && (← emitOne s!"{out}/view/{l}" l r k)
      | .error e => IO.println s!"view entry {l}: UNEXPECTED REFUSAL {e}"; ok := false
    for (l, v) in viewRefusals do
      match v with
      | .ok _ => IO.println s!"view refusal {l}: UNEXPECTEDLY ACCEPTED"; ok := false
      | .error e => IO.println s!"view refusal {l}: REFUSED as expected ({e})"
    pure (if ok then 0 else 1)
  | _ => IO.println "usage: pipegen OUTDIR"; pure 64
