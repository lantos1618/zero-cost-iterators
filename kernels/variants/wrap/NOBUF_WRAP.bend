import Base
import ./kernel.bend as K
import ./prog.bend as P

# the wrap mutant still satisfies LAW 2 (no buffer) for all inputs
def body() -> K.Ops:
  K.OCons{K.LdA{}, K.OCons{K.LdB{}, K.OCons{K.Mul{}, K.OCons{K.Acc{}, K.OCons{K.Wrap{}, K.ONil{}}}}}}

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
          loop_mats(xt, yt, K.tl(tin), K.zmul(x, y), y, K.wrap8(K.zadd(acc, K.zmul(x, y))), mats, tout)

law wrap_nobuf:
  for xs: K.Zs
  for ys: K.Zs
  {K.mats_of(K.run(P.prog(), xs, ys)) == 0n : Nat}

def wrap_nobuf(xs, ys):
  loop_mats(xs, ys, K.ZNil{}, K.z0(), K.z0(), K.z0(), 0n, K.ZNil{})
