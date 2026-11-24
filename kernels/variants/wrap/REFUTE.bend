import Base
import ./kernel.bend as K
import ./prog.bend as P

# witness a = [12], b = [11]: exact 132, wrapped accumulator -124
def a1() -> K.Zs:
  K.ZCons{K.Z{12n, 0n}, K.ZNil{}}

def b1() -> K.Zs:
  K.ZCons{K.Z{11n, 0n}, K.ZNil{}}

def discZ(z: K.Z) -> Type:
  match z:
    case K.Z{p, n}:
      match p:
        case 0n:
          Unit
        case 1n+q:
          Empty

law wrap_value:
  {K.acc_of(K.run(P.prog(), a1(), b1())) == K.Z{0n, 124n} : K.Z}

def wrap_value():
  {==}

law ref_value:
  {K.dot(a1(), b1(), K.z0()) == K.Z{132n, 0n} : K.Z}

def ref_value():
  {==}

# the negation of LAW 1 (exact) at this witness
law wrap_refutes_exact:
  {K.acc_of(K.run(P.prog(), a1(), b1())) != K.dot(a1(), b1(), K.z0()) : K.Z}

def wrap_refutes_exact(h):
  %h : discZ(_)
  Unit{}
