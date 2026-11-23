/-! IR side: a line-by-line transcription of `kernel.bend` (`exec`, `exec_body`, `run_loop`, `start`,
`run_prog`, `init`, `run`, `acc_of`, `wrap8`), with Bend's `Z{p,n}` read as the Int `p - n`.
This transcription is an equational model, NOT a mechanized Bend/BendTT refinement. -/
namespace IR

inductive Op | LdA | LdB | Mul | Acc | Wrap | StT | LdT | Sub | Abs | Sq | Pos | Bit | AbsT | Ne0
  deriving DecidableEq, Repr
inductive PS | Alloc | Loop (ops : List Op)
  deriving DecidableEq, Repr
abbrev Prog := List PS

structure St where
  r0 : Int
  r1 : Int
  acc : Int
  mats : Nat
  tout : List Int
  deriving Repr

/-- kernel.bend `wrap8`: ((v + 128) mod 256) - 128 -/
def wrap8 (v : Int) : Int := (v + 128) % 256 - 128

def exec : Op → Int → Int → Int → St → St
  | .LdA, x, _, _, s => { s with r0 := x }
  | .LdB, _, y, _, s => { s with r1 := y }
  | .Mul, _, _, _, s => { s with r0 := s.r0 * s.r1 }
  | .Acc, _, _, _, s => { s with acc := s.acc + s.r0 }
  | .Wrap, _, _, _, s => { s with acc := wrap8 s.acc }
  | .StT, _, _, _, s => { s with mats := 1 + s.mats, tout := s.tout ++ [s.r0] }
  | .LdT, _, _, t, s => { s with r0 := t }
  | .Sub, _, _, _, s => { s with r0 := s.r0 - s.r1 }
  | .Abs, _, _, _, s => { s with r0 := if s.r0 < 0 then -s.r0 else s.r0 }
  | .Sq, _, _, _, s => { s with r0 := s.r0 * s.r0 }
  | .Pos, _, _, _, s => { s with r0 := if s.r0 < 0 then 0 else s.r0 }
  | .Bit, _, _, _, s => { s with r0 := if s.r0 > 0 then 1 else s.r0 }
  | .AbsT, _, _, _, s => { s with r0 := if s.r0 < 0 then -s.r0 else s.r0 }
  | .Ne0, _, _, _, s => { s with r0 := if s.r0 = 0 then 0 else 1 }

def execBody : List Op → Int → Int → Int → St → St
  | [], _, _, _, s => s
  | o :: r, x, y, t, s => execBody r x y t (exec o x y t s)

def hd : List Int → Int | [] => 0 | h :: _ => h
def tl : List Int → List Int | [] => [] | _ :: t => t

def runLoop (body : List Op) : List Int → List Int → List Int → St → St
  | x :: xs, y :: ys, tin, s => runLoop body xs ys (tl tin) (execBody body x y (hd tin) s)
  | _, _, _, s => s

def start (body : List Op) (xs ys : List Int) (s : St) : St :=
  runLoop body xs ys s.tout { s with tout := [] }

def runProg : Prog → List Int → List Int → St → St
  | [], _, _, s => s
  | .Alloc :: r, xs, ys, s => runProg r xs ys { s with mats := 1 + s.mats }
  | .Loop b :: r, xs, ys, s => runProg r xs ys (start b xs ys s)

def init : St := ⟨0, 0, 0, 0, []⟩
def run (p : Prog) (xs ys : List Int) : St := runProg p xs ys init

def posIR : Prog := [.Loop [.LdA, .LdB, .Mul, .Acc]]
def wrapIR : Prog := [.Loop [.LdA, .LdB, .Mul, .Acc, .Wrap]]
def l1IR : Prog := [.Loop [.LdA, .LdB, .Sub, .AbsT, .Acc]]
def l2IR : Prog := [.Loop [.LdA, .LdB, .Sub, .Sq, .Acc]]
def hamIR : Prog := [.Loop [.LdA, .LdB, .Sub, .Ne0, .Acc]]
def oslIR : Prog := [.Loop [.LdA, .LdB, .Sub, .Pos, .Acc]]

/-- independent Lean references (truncate at the shorter list) -/
def refL1 : List Int → List Int → Int
  | x :: xs, y :: ys => (if x - y < 0 then -(x - y) else x - y) + refL1 xs ys
  | _, _ => 0
def refL2 : List Int → List Int → Int
  | x :: xs, y :: ys => (x - y) * (x - y) + refL2 xs ys
  | _, _ => 0
/-- Hamming: number of unequal positions -/
def refHam : List Int → List Int → Int
  | x :: xs, y :: ys => (if x = y then 0 else 1) + refHam xs ys
  | _, _ => 0
/-- one-sided L1: sum of max(x - y, 0) -/
def refOsl : List Int → List Int → Int
  | x :: xs, y :: ys => (if y < x then x - y else 0) + refOsl xs ys
  | _, _ => 0

def bufIR : Prog := [.Alloc, .Loop [.LdA, .LdB, .Mul, .StT], .Loop [.LdT, .Acc]]

/-- independent reference (Lean side): right-nested exact sum of products, truncating at the shorter list -/
def refDot : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + refDot xs ys
  | _, _ => 0

def overflowIR : Prog := [.Loop [.LdA, .LdB, .Mul, .Mul, .Mul, .Mul, .Acc]]

/-- Optional arithmetic representation lemma, Lean side only: kernel.bend `zadd`/`zmul` transcribed on
Nat pairs, with Z{p,n} read as p - n. A statement about this Lean transcription, not a Bend proof. -/
def zadd (a b : Nat × Nat) : Nat × Nat := (a.1 + b.1, a.2 + b.2)
def zmul (a b : Nat × Nat) : Nat × Nat := (a.1 * b.1 + a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def zval (a : Nat × Nat) : Int := (a.1 : Int) - a.2

end IR
