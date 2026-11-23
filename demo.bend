import Base
import ./kernel.bend as K
import ./prog.bend as P

# runtime execution of the positive IR on a small witness: a = [3, -5, 7], b = [-2, 4, 1] (exact -19)
# (small values only: Bend Nat is unary; 128n * 128n overflows the machine stack)
def main() -> K.Z:
  K.acc_of(K.run(P.prog(), K.ZCons{K.Z{3n, 0n}, K.ZCons{K.Z{0n, 5n}, K.ZCons{K.Z{7n, 0n}, K.ZNil{}}}}, K.ZCons{K.Z{0n, 2n}, K.ZCons{K.Z{4n, 0n}, K.ZCons{K.Z{1n, 0n}, K.ZNil{}}}}))
