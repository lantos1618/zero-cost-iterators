import Bridge.IR
/-! Parser for the exact generated `prog.bend` (fixed preamble + one constructor term), with a
printer; `parseBend` succeeds only if printing the parsed term reproduces the term line exactly. -/
namespace BendP
open IR

def tokens (s : String) : List String :=
  let rec go : List Char → List Char → List String
    | [], cur => if cur.isEmpty then [] else [String.mk cur.reverse]
    | c :: r, cur =>
      let flush := if cur.isEmpty then [] else [String.mk cur.reverse]
      if c = '{' ∨ c = '}' ∨ c = ',' then flush ++ [String.singleton c] ++ go r []
      else if c = ' ' then flush ++ go r []
      else go r (c :: cur)
  go s.toList []

def op? : String → Option Op
  | "K.LdA" => some .LdA | "K.LdB" => some .LdB | "K.Mul" => some .Mul | "K.Acc" => some .Acc
  | "K.Wrap" => some .Wrap | "K.StT" => some .StT | "K.LdT" => some .LdT
  | "K.Sub" => some .Sub | "K.Abs" => some .Abs | "K.Sq" => some .Sq | "K.Pos" => some .Pos | "K.Bit" => some .Bit | "K.AbsT" => some .AbsT | "K.Ne0" => some .Ne0 | _ => none

def pOps : Nat → List String → Option (List Op × List String)
  | 0, _ => none
  | _ + 1, "K.ONil" :: "{" :: "}" :: r => some ([], r)
  | f + 1, "K.OCons" :: "{" :: o :: "{" :: "}" :: "," :: r => do
    let op ← op? o
    let (os, r) ← pOps f r
    match r with | "}" :: r => some (op :: os, r) | _ => none
  | _, _ => none

def pStmts : Nat → List String → Option (Prog × List String)
  | 0, _ => none
  | _ + 1, "K.PNil" :: "{" :: "}" :: r => some ([], r)
  | f + 1, "K.PCons" :: "{" :: "K.Alloc" :: "{" :: "}" :: "," :: r => do
    let (ss, r) ← pStmts f r
    match r with | "}" :: r => some (.Alloc :: ss, r) | _ => none
  | f + 1, "K.PCons" :: "{" :: "K.Loop" :: "{" :: r => do
    let (os, r) ← pOps f r
    match r with
    | "}" :: "," :: r => do
      let (ss, r) ← pStmts f r
      match r with | "}" :: r => some (.Loop os :: ss, r) | _ => none
    | _ => none
  | _, _ => none

def showOp : Op → String
  | .LdA => "K.LdA{}" | .LdB => "K.LdB{}" | .Mul => "K.Mul{}" | .Acc => "K.Acc{}"
  | .Wrap => "K.Wrap{}" | .StT => "K.StT{}" | .LdT => "K.LdT{}"
  | .Sub => "K.Sub{}" | .Abs => "K.Abs{}" | .Sq => "K.Sq{}" | .Pos => "K.Pos{}" | .Bit => "K.Bit{}" | .AbsT => "K.AbsT{}" | .Ne0 => "K.Ne0{}"
def showOps : List Op → String
  | [] => "K.ONil{}" | o :: r => s!"K.OCons{"{"}{showOp o}, {showOps r}}"
def showProg : Prog → String
  | [] => "K.PNil{}"
  | .Alloc :: r => s!"K.PCons{"{"}K.Alloc{"{"}}, {showProg r}}"
  | .Loop os :: r => s!"K.PCons{"{"}K.Loop{"{"}{showOps os}}, {showProg r}}"

/-- the whole file: non-empty trimmed lines other than `#` comments must be exactly these -/
def parseBend (src : String) : Except String Prog := do
  let ls := (src.splitOn "\n").map String.trim |>.filter fun l => ¬ l.isEmpty ∧ ¬ l.startsWith "#"
  match ls with
  | ["import Base", "import ./kernel.bend as K", "def prog() -> K.Stmts:", term] =>
    let ts := tokens term
    match pStmts (ts.length + 1) ts with
    | some (p, []) =>
      if showProg p = term then .ok p else .error "round-trip mismatch: printed term differs from file"
    | _ => .error "prog() term outside the K.Stmts constructor grammar"
  | _ => .error "file is not exactly the generated preamble + `def prog() -> K.Stmts:` + one term"

end BendP
