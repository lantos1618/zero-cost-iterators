# APL reference models behind .view(), over exact Nat (no overflow, no floats).
# Each staged APL reference is proved equal to its fused accumulator loop.
import Base

# ---------- supporting lemmas ----------
def add_zero(+x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# a Data list of Nat (duplicable), so proofs may reuse list arguments
type NL is Data:
  LNil{}
  LCon{h: Nat, t: NL}

# ---------- +/ : APL right fold, and the fused left-fold loop ----------
def sumR(xs: NL) -> Nat:
  match xs:
    case LNil{}:
      0n
    case LCon{+h, +t}:
      Nat.add(h, sumR(t))

def sumL(xs: NL, acc: Nat) -> Nat:
  match xs:
    case LNil{}:
      acc
    case LCon{+h, +t}:
      sumL(t, Nat.add(acc, h))

def sumL_acc(+xs: NL, +acc: Nat) -> {sumL(xs, acc) == Nat.add(acc, sumR(xs)) : Nat}:
  match xs:
    case LNil{}:
      %add_zero(acc) : {_ == Nat.add(acc, 0n) : Nat}
      {==}
    case LCon{+h, +t}:
      %add_assoc(acc, h, sumR(t)) : {sumL(t, Nat.add(acc, h)) == _ : Nat}
      sumL_acc(t, Nat.add(acc, h))

def plus_reduce(+xs: NL) -> {sumL(xs, 0n) == sumR(xs) : Nat}:
  sumL_acc(xs, 0n)

# ---------- M/Y then +/ : aligned (mask, value) pairs, aligned by construction ----------
type MP is Data:
  MNil{}
  MCons{m: Bool, y: Nat, t: MP}

def compress(ps: MP) -> NL:
  match ps:
    case MNil{}:
      LNil{}
    case MCons{m, +y, +t}:
      match m:
        case True{}:
          LCon{y, compress(t)}
        case False{}:
          compress(t)

def msum(ps: MP, acc: Nat) -> Nat:
  match ps:
    case MNil{}:
      acc
    case MCons{m, +y, +t}:
      match m:
        case True{}:
          msum(t, Nat.add(acc, y))
        case False{}:
          msum(t, acc)

def mask_sum(+ps: MP, +acc: Nat) -> {msum(ps, acc) == sumL(compress(ps), acc) : Nat}:
  match ps:
    case MNil{}:
      {==}
    case MCons{m, +y, +t}:
      match m:
        case True{}:
          mask_sum(t, Nat.add(acc, y))
        case False{}:
          mask_sum(t, acc)

# ---------- +\ : item i is +/ of the explicit (i+1)-prefix ----------
def snoc(xs: NL, x: Nat) -> NL:
  match xs:
    case LNil{}:
      LCon{x, LNil{}}
    case LCon{+h, +t}:
      LCon{h, snoc(t, x)}

def scanRef(xs: NL, +seen: NL) -> NL:
  match xs:
    case LNil{}:
      LNil{}
    case LCon{+h, +t}:
      LCon{sumR(snoc(seen, h)), scanRef(t, snoc(seen, h))}

def scanL(xs: NL, +acc: Nat) -> NL:
  match xs:
    case LNil{}:
      LNil{}
    case LCon{+h, +t}:
      LCon{Nat.add(acc, h), scanL(t, Nat.add(acc, h))}

def snoc_sum(+s: NL, +h: Nat) -> {Nat.add(sumR(s), h) == sumR(snoc(s, h)) : Nat}:
  match s:
    case LNil{}:
      %add_zero(h) : {_ == Nat.add(h, 0n) : Nat}
      {==}
    case LCon{+s1, +st}:
      %snoc_sum(st, h) : {Nat.add(Nat.add(s1, sumR(st)), h) == Nat.add(s1, _) : Nat}
      add_assoc(s1, sumR(st), h)

def sumR_snoc(+s: NL, +h: Nat) -> {sumR(snoc(s, h)) == Nat.add(sumR(s), h) : Nat}:
  %snoc_sum(s, h) : {_ == Nat.add(sumR(s), h) : Nat}
  {==}

def scan_gen(+xs: NL, +seen: NL) -> {scanL(xs, sumR(seen)) == scanRef(xs, seen) : NL}:
  match xs:
    case LNil{}:
      {==}
    case LCon{+h, +t}:
      %sumR_snoc(seen, h) : {LCon{_, scanL(t, _)} == LCon{sumR(snoc(seen, h)), scanRef(t, snoc(seen, h))} : NL}
      %scan_gen(t, snoc(seen, h)) : {LCon{sumR(snoc(seen, h)), scanL(t, sumR(snoc(seen, h)))} == LCon{sumR(snoc(seen, h)), _} : NL}
      {==}

def plus_scan(+xs: NL) -> {scanL(xs, 0n) == scanRef(xs, LNil{}) : NL}:
  scan_gen(xs, LNil{})

# ---------- and-reduce of a pure predicate ----------
def pos(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

def band(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      False{}

def allR(xs: NL) -> Bool:
  match xs:
    case LNil{}:
      True{}
    case LCon{+h, +t}:
      band(pos(h), allR(t))

def allL(xs: NL, acc: Bool) -> Bool:
  match xs:
    case LNil{}:
      acc
    case LCon{+h, +t}:
      allL(t, band(acc, pos(h)))

def all_false(+xs: NL) -> {allL(xs, False{}) == False{} : Bool}:
  match xs:
    case LNil{}:
      {==}
    case LCon{+h, +t}:
      all_false(t)

def and_reduce(+xs: NL) -> {allL(xs, True{}) == allR(xs) : Bool}:
  match xs:
    case LNil{}:
      {==}
    case LCon{+h, +t}:
      match h:
        case 0n:
          all_false(t)
        case 1n+q:
          and_reduce(t)

# ---------- A +.x B on aligned pairs: paired multiply, then exact +/ ----------
type NP is Data:
  NNil{}
  NCons{x: Nat, y: Nat, t: NP}

def times(ps: NP) -> NL:
  match ps:
    case NNil{}:
      LNil{}
    case NCons{+x, +y, +t}:
      LCon{Nat.mul(x, y), times(t)}

def dotL(ps: NP, acc: Nat) -> Nat:
  match ps:
    case NNil{}:
      acc
    case NCons{+x, +y, +t}:
      dotL(t, Nat.add(acc, Nat.mul(x, y)))

def dot_acc(+ps: NP, +acc: Nat) -> {dotL(ps, acc) == sumL(times(ps), acc) : Nat}:
  match ps:
    case NNil{}:
      {==}
    case NCons{+x, +y, +t}:
      dot_acc(t, Nat.add(acc, Nat.mul(x, y)))

def inner_product(+ps: NP) -> {dotL(ps, 0n) == sumR(times(ps)) : Nat}:
  %plus_reduce(times(ps)) : {dotL(ps, 0n) == _ : Nat}
  dot_acc(ps, 0n)

# ---------- counterexample: APL -/ 10 3 2 = 10-(3-2) = 9, left fold (10-3)-2 = 5 ----------
def disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

law minus_not_left:
  {Nat.sub(10n, Nat.sub(3n, 2n)) != Nat.sub(Nat.sub(10n, 3n), 2n) : Nat}

def minus_not_left(e):
  %e : disc(Nat.sub(_, 5n))
  Unit{}

law main:
  Nat

def main():
  sumL(scanL(LCon{1n, LCon{2n, LCon{3n, LNil{}}}}, 0n), 0n)
