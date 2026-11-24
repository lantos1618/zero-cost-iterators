import Base
import ./kernel.bend as K
import ./prog.bend as P

# i8red: the osl loop body; the law says the actual evaluator's loop equals the independent Bend reference posd
def body() -> K.Ops:
  K.OCons{K.LdA{}, K.OCons{K.LdB{}, K.OCons{K.Sub{}, K.OCons{K.Pos{}, K.OCons{K.Acc{}, K.ONil{}}}}}}

law loop_exact:
  for xs: K.Zs
  for ys: K.Zs
  for tin: K.Zs
  for r0: K.Z
  for r1: K.Z
  for acc: K.Z
  for mats: Nat
  for tout: K.Zs
  {K.acc_of(K.run_loop(body(), xs, ys, tin, K.St{r0, r1, acc, mats, tout})) == K.posd(xs, ys, acc) : K.Z}

def loop_exact(xs, ys, tin, r0, r1, acc, mats, tout):
  match xs:
    case K.ZNil{}:
      {==}
    case K.ZCons{+x, xt}:
      match ys:
        case K.ZNil{}:
          {==}
        case K.ZCons{+y, yt}:
          loop_exact(xt, yt, K.tl(tin), K.zpos(K.zsub(x, y)), y, K.zadd(acc, K.zpos(K.zsub(x, y))), mats, tout)

law prog_exact:
  for xs: K.Zs
  for ys: K.Zs
  {K.acc_of(K.run(P.prog(), xs, ys)) == K.posd(xs, ys, K.z0) : K.Z}

def prog_exact(xs, ys):
  loop_exact(xs, ys, K.ZNil{}, K.z0, K.z0, K.z0, 0n, K.ZNil{})
