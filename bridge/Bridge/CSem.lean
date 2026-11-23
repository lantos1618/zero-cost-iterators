import Bridge.CSyntax
/-! Independent big-step semantics of the supported C subset (does not mention the IR).
Modeled: `int`/`int32_t` 32-bit two's complement, `uint32_t` = `unsigned int` (32-bit), `size_t` 64-bit.
Signed overflow (UB), an out-of-bounds or non-int8 element read, an implementation-defined
out-of-range uint32->int32 conversion, use of an undeclared/redeclared variable, an undefined macro,
and falling off the end of `int i8dot` all go to `fault`. Observable: the return value and the single
`*out` cell (`none` = never written by the kernel). There is no other writable memory in the subset. -/
namespace C

def inI32 (z : Int) : Prop := -2147483648 ≤ z ∧ z ≤ 2147483647
instance (z : Int) : Decidable (inI32 z) := by unfold inI32; infer_instance

/-- inputs: `a`, `b` as the int8_t values of the caller's arrays (lists), and `n` -/
structure Env where
  a : List Int
  b : List Int
  n : Nat

inductive Val | i32 (z : Int) | u32 (z : Nat)
  deriving DecidableEq, Repr

structure CSt where
  acc : Option Int
  r0 : Option Int
  r1 : Option Int
  out : Option Int
  deriving DecidableEq, Repr

def CSt.get (st : CSt) : V → Option Int
  | .acc => st.acc | .r0 => st.r0 | .r1 => st.r1
def CSt.set (st : CSt) : V → Int → CSt
  | .acc, z => { st with acc := some z } | .r0, z => { st with r0 := some z } | .r1, z => { st with r1 := some z }

def Env.arr (env : Env) : Arr → List Int | .a => env.a | .b => env.b

def i32op (f : Int → Int → Int) : Option Val → Option Val → Option Val
  | some (.i32 x), some (.i32 y) => if inI32 (f x y) then some (.i32 (f x y)) else none
  | _, _ => none

/-- `i` is the loop index when inside a loop (`none` outside, where `i` is not in scope) -/
def evalE (env : Env) (i : Option Nat) (st : CSt) : E → Option Val
  | .var v => (st.get v).map .i32
  | .lit z => if inI32 z then some (.i32 z) else none
  | .ld x => match i with
    | some k => match (env.arr x)[k]? with
      | some z => if -128 ≤ z ∧ z ≤ 127 then some (.i32 z) else none
      | none => none
    | none => none
  | .mul l r => i32op (· * ·) (evalE env i st l) (evalE env i st r)
  | .add l r => i32op (· + ·) (evalE env i st l) (evalE env i st r)
  | .sub l r => i32op (· - ·) (evalE env i st l) (evalE env i st r)
  | .toU32 e => match evalE env i st e with
    | some (.i32 x) => some (.u32 (x % 4294967296).toNat) | _ => none
  | .andU e k => match evalE env i st e with
    | some (.u32 x) => if k < 4294967296 then some (.u32 (x &&& k)) else none | _ => none
  | .toI32 e => match evalE env i st e with
    | some (.u32 x) => if x ≤ 2147483647 then some (.i32 x) else none | _ => none
  | .neg e => match evalE env i st e with
    | some (.i32 x) => if inI32 (-x) then some (.i32 (-x)) else none | _ => none
  | .condLt c k t e => match st.get c with
    | some x => if x < k then evalE env i st t else evalE env i st e
    | none => none
  | .ne l r => match evalE env i st l, evalE env i st r with
    | some (.i32 x), some (.i32 y) => some (.i32 (if x = y then 0 else 1)) | _, _ => none

def assign (env : Env) (i : Option Nat) (st : CSt) (v : V) (e : E) : Option CSt :=
  match st.get v, evalE env i st e with
  | some _, some (.i32 z) => some (st.set v z)
  | _, _ => none

def execS (env : Env) (i : Option Nat) (st : CSt) : S → Option CSt
  | .assign v e => assign env i st v e
  | .ifGt c k v e => match st.get c with
    | some x => if x > k then assign env i st v e else some st
    | none => none
  | .ifLt c k v e => match st.get c with
    | some x => if x < k then assign env i st v e else some st
    | none => none

def execBody (env : Env) (i : Option Nat) : List S → CSt → Option CSt
  | [], st => some st
  | s :: r, st => (execS env i st s).bind (execBody env i r)

/-- `for (size_t i = 0; i < n; i++) body` with fuel n - i (fuel exhaustion with i < n would fault) -/
def loopK (env : Env) (body : List S) : Nat → Nat → CSt → Option CSt
  | 0, i, st => if i < env.n then none else some st
  | k + 1, i, st => if i < env.n then (execBody env (some i) body st).bind (loopK env body k (i + 1)) else some st

def runFor (env : Env) (body : List S) (st : CSt) : Option CSt := loopK env body env.n 0 st

inductive Out | fault | ret (rv : Int) (out : Option Int)
  deriving DecidableEq, Repr

def lookupDef (m : String) : List Dir → Option Nat
  | [] => none
  | .dfn m' k :: r => if m = m' then some k else lookupDef m r
  | _ :: r => lookupDef m r

def execT (env : Env) (dirs : List Dir) : List T → CSt → Out
  | [], _ => .fault                                  -- fell off the end of a non-void function
  | .decl v z :: r, st => if st.get v = none ∧ inI32 z then execT env dirs r (st.set v z) else .fault
  | .assign v e :: r, st => match assign env none st v e with
    | some st' => execT env dirs r st' | none => .fault
  | .ifGt c k v e :: r, st => match execS env none st (.ifGt c k v e) with
    | some st' => execT env dirs r st' | none => .fault
  | .ifLt c k v e :: r, st => match execS env none st (.ifLt c k v e) with
    | some st' => execT env dirs r st' | none => .fault
  | .guard m rv :: r, st => match lookupDef m dirs with
    | some k => if env.n > k then .ret rv st.out else execT env dirs r st
    | none => .fault
  | .forN b :: r, st => match runFor env b st with
    | some st' => execT env dirs r st' | none => .fault
  | .store v :: r, st => match st.get v with
    | some z => execT env dirs r { st with out := some z } | none => .fault
  | .ret z :: _, st => .ret z st.out

/-- run `int i8dot(a, b, n, out)`; `out0` is the caller's prior content of `*out` -/
def cRun (f : CFile) (env : Env) (out0 : Option Int) : Out :=
  execT env f.dirs f.body ⟨none, none, none, out0⟩

/-- admitted inputs: int8 elements, both arrays readable for n elements, n representable in size_t -/
def Admitted (env : Env) : Prop :=
  (∀ x ∈ env.a, -128 ≤ x ∧ x ≤ 127) ∧ (∀ y ∈ env.b, -128 ≤ y ∧ y ≤ 127) ∧
  env.n ≤ env.a.length ∧ env.n ≤ env.b.length ∧ env.n < 2 ^ 64

end C
