import Base
import ./prog.bend as P
import ./kernel.bend as K
def main() -> K.Z:
  K.acc_of(K.run(P.prog(), K.ZCons{K.Z{3n,0n}, K.ZNil{}}, K.ZCons{K.Z{0n,5n}, K.ZNil{}}))
