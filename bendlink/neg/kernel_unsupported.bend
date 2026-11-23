import Base

# ---- exact integers: Z{p, n} denotes the mathematical integer p - n (unbounded Nat parts)
type Z is Data:
  Z{p: Nat, n: Nat}

def z0() -> Z:
  Z{0n, 0n}

def zadd(a: Z, b: Z) -> Z:
  match a:
    case Z{p, n}:
      match b:
        case Z{q, m}:
          Z{Nat.add(p, q), Nat.add(n, m)}

def zmul(a: Z, b: Z) -> Z:
  match a:
    case Z{+p, +n}:
      match b:
        case Z{+q, +m}:
          Z{Nat.add(Nat.mul(p, q), Nat.mul(n, m)), Nat.add(Nat.mul(p, m), Nat.mul(n, q))}

# Copyable (Data) sequences: Base List<T> is not Data-kinded, and loops re-read their inputs.
type Zs is Data:
  ZNil{}
  ZCons{h: Z, t: Zs}

# ---- independent reference: exact integer dot product, threaded left to right
def dot(xs: Zs, ys: Zs, acc: Z) -> Z:
  match xs:
    case ZNil{}:
      acc
    case ZCons{x, xt}:
      match ys:
        case ZNil{}:
          acc
        case ZCons{y, yt}:
          dot(xt, yt, zadd(acc, zmul(x, y)))

# ---- 8-bit two's-complement narrowing (used only by the wrap mutant): wrap8(v) = ((v + 128) mod 256) - 128
# (8-bit, not 16-bit: the checker/runtime Nat is unary and 128n*128n already overflows its stack)
def w8.pos(+r: Nat, lo: Bool) -> Z:
  match lo:
    case True{}:
      Z{r, 0n}
    case False{}:
      Z{0n, Nat.sub(256n, r)}

def w8.nat(+r: Nat) -> Z:
  w8.pos(r, Nat.is_lt(r, 128n))

def w8.neg(+r: Nat, zero: Bool) -> Z:
  match zero:
    case True{}:
      z0()
    case False{}:
      w8.nat(Nat.sub(256n, r))

def w8.negr(+r: Nat) -> Z:
  w8.neg(r, Nat.is_eq(r, 0n))

def w8.sel(+p: Nat, +n: Nat, ge: Bool) -> Z:
  match ge:
    case True{}:
      w8.nat(Nat.mod(Nat.sub(p, n), 256n))
    case False{}:
      w8.negr(Nat.mod(Nat.sub(n, p), 256n))

def wrap8(a: Z) -> Z:
  match a:
    case Z{+p, +n}:
      w8.sel(p, n, Nat.is_le(n, p))

# ---- executable lowered IR. Registers r0, r1 and acc are scalars; tmp is an intermediate array.
type Op is Data:
  LdA{}
  LdB{}
  Mul{}
  Acc{}
  Wrap{}
  StT{}
  LdT{}

type Ops is Data:
  ONil{}
  OCons{h: Op, t: Ops}

type Stmt is Data:
  Alloc{}
  Loop{body: Ops}

type Stmts is Data:
  PNil{}
  PCons{h: Stmt, t: Stmts}

def zsnoc(l: Zs, +x: Z) -> Zs:
  match l:
    case ZNil{}:
      ZCons{x, ZNil{}}
    case ZCons{h, t}:
      ZCons{h, zsnoc(t, x)}

# mats counts executed Alloc and StT (intermediate-buffer allocations and writes); tout is the buffer being written
type St is Data:
  St{r0: Z, r1: Z, acc: Z, mats: Nat, tout: Zs}

def exec(op: Op, +x: Z, +y: Z, +t: Z, st: St) -> St:
  match op:
    case LdA{}:
      match st:
        case St{+r0, +r1, +acc, +mats, tout}:
          St{x, r1, acc, mats, tout}
    case LdB{}:
      match st:
        case St{+r0, +r1, +acc, +mats, tout}:
          St{r0, y, acc, mats, tout}
    case Mul{}:
      match st:
        case St{+r0, +r1, +acc, +mats, tout}:
          St{zmul(r0, r1), r1, acc, mats, tout}
    case Acc{}:
      match st:
        case St{+r0, +r1, +acc, +mats, tout}:
          St{r0, r1, zadd(acc, r0), mats, tout}
    case Wrap{}:
      match st:
        case St{+r0, +r1, +acc, +mats, tout}:
          St{r0, r1, wrap8(acc), mats, tout}
    case StT{}:
      match st:
        case St{+r0, +r1, +acc, +mats, tout}:
          St{r0, r1, acc, 1n+mats, zsnoc(tout, r0)}
    case LdT{}:
      match st:
        case St{+r0, +r1, +acc, +mats, tout}:
          St{t, r1, acc, mats, tout}

def exec_body(ops: Ops, +x: Z, +y: Z, +t: Z, st: St) -> St:
  match ops:
    case ONil{}:
      st
    case OCons{h, rest}:
      exec_body(rest, x, y, t, exec(h, x, y, t, st))

def hd(l: Zs) -> Z:
  match l:
    case ZNil{}:
      z0()
    case ZCons{h, t}:
      h

def tl(l: Zs) -> Zs:
  match l:
    case ZNil{}:
      ZNil{}
    case ZCons{h, t}:
      t

# one iteration per index i < min(|a|, |b|): LdA reads a[i], LdB reads b[i], LdT reads tin[i]
def run_loop(+body: Ops, xs: Zs, ys: Zs, +tin: Zs, st: St) -> St:
  match xs:
    case ZNil{}:
      st
    case ZCons{+x, xt}:
      match ys:
        case ZNil{}:
          st
        case ZCons{+y, yt}:
          run_loop(body, xt, yt, tl(tin), exec_body(body, x, y, hd(tin), st))

# a loop reads the buffer written by the previous loop and starts a fresh one
def start(+body: Ops, +xs: Zs, +ys: Zs, st: St) -> St:
  match st:
    case St{r0, r1, acc, mats, tout}:
      run_loop(body, xs, ys, tout, St{r0, r1, acc, mats, ZNil{}})

def bump(st: St) -> St:
  match st:
    case St{r0, r1, acc, mats, tout}:
      St{r0, r1, acc, 1n+mats, tout}

def run_prog(prog: Stmts, +xs: Zs, +ys: Zs, st: St) -> St:
  match prog:
    case PNil{}:
      st
    case PCons{s, rest}:
      match s:
        case Alloc{}:
          run_prog(rest, xs, ys, bump(st))
        case Loop{body}:
          run_prog(rest, xs, ys, start(body, xs, ys, st))

def init() -> St:
  St{z0(), z0(), z0(), 0n, ZNil{}}

def run(prog: Stmts, +xs: Zs, +ys: Zs) -> St:
  run_prog(prog, xs, ys, init())

def acc_of(st: St) -> Z:
  match st:
    case St{r0, r1, acc, mats, tout}:
      acc

def mats_of(st: St) -> Nat:
  match st:
    case St{r0, r1, acc, mats, tout}:
      mats

def extra(x: Nat) -> Nat:
  x + 1
