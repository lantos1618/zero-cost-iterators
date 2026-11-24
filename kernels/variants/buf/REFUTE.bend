import Base
import ./kernel.bend as K
import ./prog.bend as P

def a1() -> K.Zs:
  K.ZCons{K.Z{1n, 0n}, K.ZNil{}}

def b1() -> K.Zs:
  K.ZCons{K.Z{1n, 0n}, K.ZNil{}}

# a = [3, -5, 7], b = [-2, 4, 1]: exact -19
def a3() -> K.Zs:
  K.ZCons{K.Z{3n, 0n}, K.ZCons{K.Z{0n, 5n}, K.ZCons{K.Z{7n, 0n}, K.ZNil{}}}}

def b3() -> K.Zs:
  K.ZCons{K.Z{0n, 2n}, K.ZCons{K.Z{4n, 0n}, K.ZCons{K.Z{1n, 0n}, K.ZNil{}}}}

def discN(m: Nat) -> Type:
  match m:
    case 0n:
      Empty
    case 1n+q:
      Unit

# one Alloc + one StT per element
law buf_mats_value:
  {K.mats_of(K.run(P.prog(), a1(), b1())) == 2n : Nat}

def buf_mats_value():
  {==}

# the negation of LAW 2 (nobuf) at this witness
law buf_refutes_nobuf:
  {K.mats_of(K.run(P.prog(), a1(), b1())) != 0n : Nat}

def buf_refutes_nobuf(h):
  %h : discN(_)
  Unit{}

# same exact sum as the reference on a finite witness (checked by computation, not universally)
law buf_exact_witness:
  {K.acc_of(K.run(P.prog(), a3(), b3())) == K.dot(a3(), b3(), K.z0()) : K.Z}

def buf_exact_witness():
  {==}

# Z{p, n} is not canonical: 7 - 26 = -19
law buf_value:
  {K.acc_of(K.run(P.prog(), a3(), b3())) == K.Z{7n, 26n} : K.Z}

def buf_value():
  {==}
