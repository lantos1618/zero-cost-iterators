import Base
import ./kernel.bend as K
import ./prog.bend as P

# K.run       : the executable lowered IR evaluator (kernel.bend)
# P.prog()    : the IR program that gen.py also emits as C (prog.bend is generated from ir/<variant>.json)
# K.dot       : independent exact-integer reference (no IR)
# K.mats_of   : number of executed intermediate-buffer operations (Alloc + StT)

# LAW 1, exact integer sum: for all inputs, the lowered program returns the exact integer dot product.
law exact:
  for xs: K.Zs
  for ys: K.Zs
  {K.acc_of(K.run(P.prog(), xs, ys)) == K.dot(xs, ys, K.z0()) : K.Z}

# LAW 2, zero intermediate materialization: for all inputs, the lowered program executes no
# buffer allocation and no buffer write.
law nobuf:
  for xs: K.Zs
  for ys: K.Zs
  {K.mats_of(K.run(P.prog(), xs, ys)) == 0n : Nat}
