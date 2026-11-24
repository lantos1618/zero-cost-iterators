/-! A small C expression language with its own meaning, used by the generator in place of raw strings.

`CE.eval` is the C meaning: every value is a `std::uint64_t` (`+ - * ^ & |` wrap), comparisons give 0 or 1,
`?:` evaluates only the branch it takes, and `%` or `/` by zero is undefined behaviour (`none`). `CE.print`
is one fixed rule per node with full parentheses; it, and the name each `Slot` prints as, are trusted. The
theorems in `Iter/CLoop.lean` (`E.toC_eval`, `P.toC_eval`, `X.toC_eval`, `Q.toC_eval`, `*_step`) prove the
trees the generator prints mean what the proved loops compute, and are never undefined. -/
namespace Iter.C

/-- the named values a printed expression can read -/
inductive Slot where
  | x | k | b
  | fld (i : Nat)
  | prm (i : Nat)
deriving DecidableEq

inductive Op where
  | add | sub | mul | xor | band | bor | mod | div | eq | lt | ne | ge

inductive CE where
  | var (s : Slot)
  | lit (n : UInt64)
  | bin (o : Op) (a b : CE)
  | cond (c t f : CE)
  | cast (a : CE)

def Op.eval : Op → UInt64 → UInt64 → Option UInt64
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .xor, a, b => some (a ^^^ b)
  | .band, a, b => some (a &&& b)
  | .bor, a, b => some (a ||| b)
  | .mod, a, b => if b = 0 then none else some (a % b)
  | .div, a, b => if b = 0 then none else some (a / b)
  | .eq, a, b => some (if a = b then 1 else 0)
  | .lt, a, b => some (if a < b then 1 else 0)
  | .ne, a, b => some (if a = b then 0 else 1)
  | .ge, a, b => some (if b ≤ a then 1 else 0)

def CE.eval (env : Slot → UInt64) : CE → Option UInt64
  | .var s => some (env s)
  | .lit n => some n
  | .bin o a b => match a.eval env, b.eval env with
    | some u, some v => o.eval u v
    | _, _ => none
  | .cond c t f => match c.eval env with
    | some v => if v = 0 then f.eval env else t.eval env
    | none => none
  | .cast a => a.eval env

def Op.sym : Op → String
  | .add => "+" | .sub => "-" | .mul => "*" | .xor => "^" | .band => "&" | .bor => "|"
  | .mod => "%" | .div => "/" | .eq => "==" | .lt => "<" | .ne => "!=" | .ge => ">="

def CE.print (nm : Slot → String) : CE → String
  | .var s => nm s
  | .lit n => s!"{n}ULL"
  | .bin o a b => s!"({a.print nm} {o.sym} {b.print nm})"
  | .cond c t f => s!"({c.print nm} ? {t.print nm} : {f.print nm})"
  | .cast a => s!"((std::uint64_t){a.print nm})"

/-- `v & (0 - kb)`: `v` when `kb = 1`, `0` when `kb = 0` -/
def maskC (v kb : CE) : CE := .bin .band v (.bin .sub (.lit 0) kb)

/-- `v | (kb - 1)`: `v` when `kb = 1`, all ones when `kb = 0` -/
def minC (v kb : CE) : CE := .bin .bor v (.bin .sub kb (.lit 1))

end Iter.C
