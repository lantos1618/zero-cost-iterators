import Base
import ./kernel.bend as K
import ./prog.bend as P
import ./LAWS.bend as L

# the fused body the proofs are about: r0 := a[i]; r1 := b[i]; r0 := r0 * r1; acc := acc + r0
def body() -> K.Ops:
  K.OCons{K.LdA{}, K.OCons{K.LdB{}, K.OCons{K.Mul{}, K.OCons{K.Acc{}, K.ONil{}}}}}

law loop_exact:
  for xs: K.Zs
  for ys: K.Zs
  for tin: K.Zs
  for r0: K.Z
  for r1: K.Z
  for acc: K.Z
  for mats: Nat
  for tout: K.Zs
  {K.acc_of(K.run_loop(body(), xs, ys, tin, K.St{r0, r1, acc, mats, tout})) == K.dot(xs, ys, acc) : K.Z}

def loop_exact(xs, ys, tin, r0, r1, acc, mats, tout):
  match xs:
    case K.ZNil{}:
      {==}
    case K.ZCons{+x, xt}:
      match ys:
        case K.ZNil{}:
          {==}
        case K.ZCons{+y, yt}:
          loop_exact(xt, yt, K.tl(tin), K.zmul(x, y), y, K.zadd(acc, K.zmul(x, y)), mats, tout)

law loop_mats:
  for xs: K.Zs
  for ys: K.Zs
  for tin: K.Zs
  for r0: K.Z
  for r1: K.Z
  for acc: K.Z
  for mats: Nat
  for tout: K.Zs
  {K.mats_of(K.run_loop(body(), xs, ys, tin, K.St{r0, r1, acc, mats, tout})) == mats : Nat}

def loop_mats(xs, ys, tin, r0, r1, acc, mats, tout):
  match xs:
    case K.ZNil{}:
      {==}
    case K.ZCons{+x, xt}:
      match ys:
        case K.ZNil{}:
          {==}
        case K.ZCons{+y, yt}:
          loop_mats(xt, yt, K.tl(tin), K.zmul(x, y), y, K.zadd(acc, K.zmul(x, y)), mats, tout)

def L.exact(xs, ys):
  loop_exact(xs, ys, K.ZNil{}, K.z0(), K.z0(), K.z0(), 0n, K.ZNil{})

def L.nobuf(xs, ys):
  loop_mats(xs, ys, K.ZNil{}, K.z0(), K.z0(), K.z0(), 0n, K.ZNil{})
