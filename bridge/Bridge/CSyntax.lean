/-! The supported C subset: AST, lexical gate, comment removal, the exact line table, and the parser
from file text to AST. The parser accepts known lines in ANY order (an early store or early return
parses); ordering/scope is decided by `Check.validate`, not here. -/
namespace C

inductive V | acc | r0 | r1
  deriving DecidableEq, Repr
inductive Arr | a | b
  deriving DecidableEq, Repr

/-- expressions; C `int` is 32-bit, `int32_t`=`int`, `uint32_t`=`unsigned int`, `size_t` 64-bit -/
inductive E
  | var (v : V)              -- int32_t local
  | lit (z : Int)            -- int constant
  | ld (x : Arr)             -- (int32_t)x[i] : int8_t element converted to int32_t
  | mul (l r : E) | add (l r : E) | sub (l r : E)   -- signed int arithmetic (overflow = UB)
  | toU32 (e : E)            -- (uint32_t)e
  | andU (e : E) (k : Nat)   -- e & k u (unsigned)
  | toI32 (e : E)            -- (int32_t)e from uint32_t
  | neg (e : E)              -- -e (signed int; overflow = UB)
  | condLt (c : V) (k : Int) (t e : E)  -- c < k ? t : e (only the selected operand is evaluated)
  | ne (l r : E)             -- l != r : int 0 or 1
  deriving DecidableEq, Repr

/-- loop-body statements -/
inductive S
  | assign (v : V) (e : E)                 -- v = e;
  | ifGt (c : V) (k : Int) (v : V) (e : E) -- if (c > k) v = e;
  | ifLt (c : V) (k : Int) (v : V) (e : E) -- if (c < k) v = e;
  deriving DecidableEq, Repr

/-- function-body (top-level) statements -/
inductive T
  | decl (v : V) (z : Int)                 -- int32_t v = z;
  | assign (v : V) (e : E)
  | ifGt (c : V) (k : Int) (v : V) (e : E)
  | ifLt (c : V) (k : Int) (v : V) (e : E)
  | guard (m : String) (rv : Int)          -- if (n > M) return rv;
  | forN (body : List S)                   -- for (size_t i = 0; i < n; i++) { body }
  | store (v : V)                          -- *out = v;
  | ret (z : Int)                          -- return z;
  deriving DecidableEq, Repr

inductive Dir | inc (h : String) | dfn (m : String) (k : Nat)
  deriving DecidableEq, Repr

structure CFile where
  dirs : List Dir
  body : List T
  deriving DecidableEq, Repr

inductive Item | dir (d : Dir) | sig | forOpen | close | stmt (t : T)
  deriving DecidableEq, Repr

def T.toS : T → Option S
  | .assign v e => some (.assign v e)
  | .ifGt c k v e => some (.ifGt c k v e)
  | .ifLt c k v e => some (.ifLt c k v e)
  | _ => none

/-- The trusted line table: each exact (trimmed) line and the C meaning assigned to it. -/
def lineItem (l : String) : Option Item :=
  if l = "#include <stddef.h>" then some (.dir (.inc "stddef.h"))
  else if l = "#include <stdint.h>" then some (.dir (.inc "stdint.h"))
  else if l.startsWith "#define I8DOT_MAX_N " ∧ (l.drop 20).endsWith "u" ∧ ((l.drop 20).dropRight 1).length ≥ 1 ∧
      ((l.drop 20).dropRight 1).all Char.isDigit ∧ ¬ ((l.drop 20).dropRight 1).startsWith "0" then
    some (.dir (.dfn "I8DOT_MAX_N" ((l.drop 20).dropRight 1).toNat!))
  else if l = "int i8dot(const int8_t *a, const int8_t *b, size_t n, int32_t *out) {" then some .sig
  else if l = "if (n > I8DOT_MAX_N) return -1;" then some (.stmt (.guard "I8DOT_MAX_N" (-1)))
  else if l = "int32_t acc = 0;" then some (.stmt (.decl .acc 0))
  else if l = "int32_t r0 = 0;" then some (.stmt (.decl .r0 0))
  else if l = "int32_t r1 = 0;" then some (.stmt (.decl .r1 0))
  else if l = "for (size_t i = 0; i < n; i++) {" then some .forOpen
  else if l = "r0 = (int32_t)a[i];" then some (.stmt (.assign .r0 (.ld .a)))
  else if l = "r1 = (int32_t)b[i];" then some (.stmt (.assign .r1 (.ld .b)))
  else if l = "r0 = r0 * r1;" then some (.stmt (.assign .r0 (.mul (.var .r0) (.var .r1))))
  else if l = "acc = acc + r0;" then some (.stmt (.assign .acc (.add (.var .acc) (.var .r0))))
  else if l = "acc = (int32_t)((uint32_t)acc & 0xFFu);" then
    some (.stmt (.assign .acc (.toI32 (.andU (.toU32 (.var .acc)) 255))))
  else if l = "if (acc > 127) acc = acc - 256;" then
    some (.stmt (.ifGt .acc 127 .acc (.sub (.var .acc) (.lit 256))))
  else if l = "r0 = r0 - r1;" then some (.stmt (.assign .r0 (.sub (.var .r0) (.var .r1))))
  else if l = "if (r0 < 0) r0 = -r0;" then some (.stmt (.ifLt .r0 0 .r0 (.neg (.var .r0))))
  else if l = "r0 = r0 * r0;" then some (.stmt (.assign .r0 (.mul (.var .r0) (.var .r0))))
  else if l = "if (r0 < 0) r0 = 0;" then some (.stmt (.ifLt .r0 0 .r0 (.lit 0)))
  else if l = "if (r0 > 0) r0 = 1;" then some (.stmt (.ifGt .r0 0 .r0 (.lit 1)))
  else if l = "r0 = r0 < 0 ? -r0 : r0;" then some (.stmt (.assign .r0 (.condLt .r0 0 (.neg (.var .r0)) (.var .r0))))
  else if l = "r0 = r0 != 0;" then some (.stmt (.assign .r0 (.ne (.var .r0) (.lit 0))))
  else if l = "}" then some .close
  else if l = "*out = acc;" then some (.stmt (.store .acc))
  else if l = "return 0;" then some (.stmt (.ret 0))
  else none

def tableLines : List String :=
  ["int32_t acc = 0;", "int32_t r0 = 0;", "int32_t r1 = 0;", "if (n > I8DOT_MAX_N) return -1;",
   "r0 = (int32_t)a[i];", "r1 = (int32_t)b[i];", "r0 = r0 * r1;", "acc = acc + r0;",
   "acc = (int32_t)((uint32_t)acc & 0xFFu);", "if (acc > 127) acc = acc - 256;", "*out = acc;", "return 0;", "r0 = r0 - r1;", "if (r0 < 0) r0 = -r0;", "r0 = r0 * r0;",
   "if (r0 < 0) r0 = 0;", "if (r0 > 0) r0 = 1;",
   "r0 = r0 < 0 ? -r0 : r0;", "r0 = r0 != 0;"]

/-- inverse of the table, used only in diagnostics -/
def T.show : T → String
  | .forN b => s!"for (size_t i = 0; i < n; i++) {"{"} <{b.length} stmts> }"
  | t => (tableLines.find? fun l => lineItem l = some (.stmt t)).getD (reprStr t)

/-- lexical gate on the raw text (comments included) -/
def lexGate (cs : List Char) : Except String Unit := do
  for c in cs do
    if c = '\\' then throw "backslash (line splice/escape) not allowed"
    if c = '"' ∨ c = '\'' then throw "string/char literal quote not allowed"
    if c = '%' then throw "'%' (digraph/modulo) not allowed"
    if c = '\r' ∨ c = '\t' then throw "CR/TAB not allowed"
  let rec noQQ : List Char → Bool
    | '?' :: '?' :: _ => false
    | _ :: r => noQQ r
    | [] => true
  unless noQQ cs do throw "'??' (trigraph) not allowed"

/-- left-to-right comment removal (mode 0 code, 1 line comment, 2 block comment);
a block comment becomes one space and must not contain a newline -/
def strip : List Char → Nat → Except String (List Char)
  | [], 2 => .error "unterminated block comment"
  | [], _ => .ok []
  | '\n' :: r, 1 => ('\n' :: ·) <$> strip r 0
  | _ :: r, 1 => strip r 1
  | '*' :: '/' :: r, 2 => (' ' :: ·) <$> strip r 0
  | '\n' :: _, 2 => .error "block comment spans lines"
  | _ :: r, 2 => strip r 2
  | '/' :: '*' :: r, _ => strip r 2
  | '/' :: '/' :: r, _ => strip r 1
  | c :: r, _ => (c :: ·) <$> strip r 0

/-- structural parse of the item stream after the signature; `loop = some sb` inside a for body -/
def parseFn : List (Nat × Item) → List T → Option (List S) → Except String (List T)
  | [], _, _ => .error "unexpected end of file (missing '}')"
  | (no, it) :: rest, acc, none =>
    match it with
    | .close => if rest.isEmpty then .ok acc.reverse
                else .error s!"line {match rest with | (k, _) :: _ => k | [] => 0}: content after the function's closing brace"
    | .forOpen => parseFn rest acc (some [])
    | .stmt t => parseFn rest (t :: acc) none
    | _ => .error s!"line {no}: directive/signature inside the function"
  | (no, it) :: rest, acc, some sb =>
    match it with
    | .close => parseFn rest (.forN sb.reverse :: acc) none
    | .stmt t => match t.toS with
      | some s => parseFn rest acc (some (s :: sb))
      | none => .error s!"line {no}: unsupported statement inside a loop body"
    | .forOpen => .error s!"line {no}: nested loop unsupported"
    | _ => .error s!"line {no}: directive/signature inside a loop"

def lines (cs : List Char) : List (Nat × String) :=
  ((String.mk cs).splitOn "\n").enum.filterMap fun (k, l) =>
    let t := l.trim; if t.isEmpty then none else some (k + 1, t)

def parseFile (src : String) : Except String CFile := do
  let cs := src.toList
  lexGate cs
  let ls := lines (← strip cs 0)
  let items : List (Nat × Item) ← ls.mapM fun (no, l) => match lineItem l with
    | some it => .ok (no, it)
    | none => .error s!"line {no}: unrecognised line {repr l}"
  let dirs := items.takeWhile fun p => match p.2 with | .dir _ => true | _ => false
  let rest : List (Nat × Item) := items.drop dirs.length
  match rest with
  | (_, .sig) :: body =>
    let b ← parseFn body [] none
    pure ⟨dirs.filterMap fun p => match p.2 with | .dir d => some d | _ => none, b⟩
  | (no, _) :: _ => .error s!"line {no}: expected the function signature"
  | [] => .error "no function"

end C
