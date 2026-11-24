# NEGATIVE CONTROL reset_generic: must be rejected
# groupFold over a FINITE THREE-KEY domain K = {KA, KB, KC}, payload of ANY Data type A
# (no arithmetic on payloads). The per-key state is the ordered trace of that key's payloads, so any
# ordered per-key fold factors through it. One interleaved pass `gf` retains a separate trace per key;
# the independent reference selects each key's payloads in original order (filter) on its own.
# Witnesses instantiate A = String: interleaved keys and the order-sensitive bracket step
# acc -> "[" ++ acc ++ "|" ++ s ++ "]". Not modeled here: an unbounded key type and first-seen key
# order (both proved generically in Lean, Vw/Group.lean).
import Base

type K is Data:
  KA{}
  KB{}
  KC{}

type TL<-A: Data> is Data:
  TNil{}
  TCon{h: A, t: TL<A>}

type EL<-A: Data> is Data:
  ENil{}
  ECon{k: K, v: A, t: EL<A>}

type T3<-A: Data> is Data:
  T3{a: TL<A>, b: TL<A>, c: TL<A>}

def snoc(-A: Data, xs: TL<A>, x: A) -> TL<A>:
  match xs:
    case TNil{}:
      TCon{x, TNil{}}
    case TCon{+h, +t}:
      TCon{h, snoc(A, t, x)}

def app(-A: Data, xs: TL<A>, ys: TL<A>) -> TL<A>:
  match xs:
    case TNil{}:
      ys
    case TCon{+h, +t}:
      TCon{h, app(A, t, ys)}

# ---------- the fused interleaved pass: one traversal, retained state per key ----------
def gf(-A: Data, xs: EL<A>, ta: TL<A>, tb: TL<A>, tc: TL<A>) -> T3<A>:
  match xs:
    case ENil{}:
      T3{ta, tb, tc}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          gf(A, t, snoc(A, ta, v), tb, tc)
        case KB{}:
          gf(A, t, ta, snoc(A, tb, v), tc)
        case KC{}:
          gf(A, t, ta, tb, snoc(A, tc, v))

def slotA(-A: Data, s: T3<A>) -> TL<A>:
  match s:
    case T3{+a, +b, +c}:
      a

def slotB(-A: Data, s: T3<A>) -> TL<A>:
  match s:
    case T3{+a, +b, +c}:
      b

def slotC(-A: Data, s: T3<A>) -> TL<A>:
  match s:
    case T3{+a, +b, +c}:
      c

# ---------- independent reference: stable per-key selection ----------
def selA(-A: Data, xs: EL<A>) -> TL<A>:
  match xs:
    case ENil{}:
      TNil{}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          TCon{v, selA(A, t)}
        case KB{}:
          selA(A, t)
        case KC{}:
          selA(A, t)

def selB(-A: Data, xs: EL<A>) -> TL<A>:
  match xs:
    case ENil{}:
      TNil{}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          selB(A, t)
        case KB{}:
          TCon{v, selB(A, t)}
        case KC{}:
          selB(A, t)

def selC(-A: Data, xs: EL<A>) -> TL<A>:
  match xs:
    case ENil{}:
      TNil{}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          selC(A, t)
        case KB{}:
          selC(A, t)
        case KC{}:
          TCon{v, selC(A, t)}

# ---------- supporting lemmas ----------
def app_nil(-A: Data, +xs: TL<A>) -> {app(A, xs, TNil{}) == xs : TL<A>}:
  match xs:
    case TNil{}:
      {==}
    case TCon{+h, +t}:
      %app_nil(A, t) : {TCon{h, app(A, t, TNil{})} == TCon{h, _} : TL<A>}
      {==}

def app_snoc(-A: Data, +a: TL<A>, +v: A, +s: TL<A>) -> {app(A, snoc(A, a, v), s) == app(A, a, TCon{v, s}) : TL<A>}:
  match a:
    case TNil{}:
      {==}
    case TCon{+h, +t}:
      %app_snoc(A, t, v, s) : {TCon{h, app(A, snoc(A, t, v), s)} == TCon{h, _} : TL<A>}
      {==}

# ---------- per-key laws, generalized over the retained state ----------
def gfA_gen(-A: Data, +xs: EL<A>, +ta: TL<A>, +tb: TL<A>, +tc: TL<A>) -> {slotA(A, gf(A, xs, ta, tb, tc)) == app(A, ta, selA(A, xs)) : TL<A>}:
  match xs:
    case ENil{}:
      %app_nil(A, ta) : {_ == app(A, ta, TNil{}) : TL<A>}
      {==}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          %app_snoc(A, ta, v, selA(A, t)) : {slotA(A, gf(A, t, snoc(A, ta, v), tb, tc)) == _ : TL<A>}
          gfA_gen(A, t, snoc(A, ta, v), tb, tc)
        case KB{}:
          gfA_gen(A, t, ta, snoc(A, tb, v), tc)
        case KC{}:
          gfA_gen(A, t, ta, tb, snoc(A, tc, v))

def gfB_gen(-A: Data, +xs: EL<A>, +ta: TL<A>, +tb: TL<A>, +tc: TL<A>) -> {slotB(A, gf(A, xs, ta, tb, tc)) == app(A, tb, selB(A, xs)) : TL<A>}:
  match xs:
    case ENil{}:
      %app_nil(A, tb) : {_ == app(A, tb, TNil{}) : TL<A>}
      {==}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          gfB_gen(A, t, snoc(A, ta, v), tb, tc)
        case KB{}:
          %app_snoc(A, tb, v, selB(A, t)) : {slotB(A, gf(A, t, ta, snoc(A, tb, v), tc)) == _ : TL<A>}
          gfB_gen(A, t, ta, snoc(A, tb, v), tc)
        case KC{}:
          gfB_gen(A, t, ta, tb, snoc(A, tc, v))

def gfC_gen(-A: Data, +xs: EL<A>, +ta: TL<A>, +tb: TL<A>, +tc: TL<A>) -> {slotC(A, gf(A, xs, ta, tb, tc)) == app(A, tc, selC(A, xs)) : TL<A>}:
  match xs:
    case ENil{}:
      %app_nil(A, tc) : {_ == app(A, tc, TNil{}) : TL<A>}
      {==}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          gfC_gen(A, t, snoc(A, ta, v), tb, tc)
        case KB{}:
          gfC_gen(A, t, ta, snoc(A, tb, v), tc)
        case KC{}:
          %app_snoc(A, tc, v, selC(A, t)) : {slotC(A, gf(A, t, ta, tb, snoc(A, tc, v))) == _ : TL<A>}
          gfC_gen(A, t, ta, tb, snoc(A, tc, v))

# ---------- groupFold = stable group-then-fold, for every input and every payload type ----------
def groupA(-A: Data, +xs: EL<A>) -> {slotA(A, gf(A, xs, TNil{}, TNil{}, TNil{})) == selA(A, xs) : TL<A>}:
  gfA_gen(A, xs, TNil{}, TNil{}, TNil{})

def groupB(-A: Data, +xs: EL<A>) -> {slotB(A, gf(A, xs, TNil{}, TNil{}, TNil{})) == selB(A, xs) : TL<A>}:
  gfB_gen(A, xs, TNil{}, TNil{}, TNil{})

def groupC(-A: Data, +xs: EL<A>) -> {slotC(A, gf(A, xs, TNil{}, TNil{}, TNil{})) == selC(A, xs) : TL<A>}:
  gfC_gen(A, xs, TNil{}, TNil{}, TNil{})

# ---------- String witnesses: interleaved keys, order-sensitive bracket fold ----------
def evs() -> EL<String>:
  ECon{KA{}, "1", ECon{KB{}, "2", ECon{KA{}, "3", ECon{KC{}, "4", ECon{KB{}, "5", ECon{KA{}, "6", ENil{}}}}}}}

def br(xs: TL<String>, acc: String) -> String:
  match xs:
    case TNil{}:
      acc
    case TCon{+h, +t}:
      br(t, String.append("[", String.append(acc, String.append("|", String.append(h, "]")))))

law witness_state:
  {gf(String, evs(), TNil{}, TNil{}, TNil{}) == T3{TCon{"1", TCon{"3", TCon{"6", TNil{}}}}, TCon{"2", TCon{"5", TNil{}}}, TCon{"4", TNil{}}} : T3<String>}

def witness_state():
  {==}

law witness_bracket:
  {br(slotA(String, gf(String, evs(), TNil{}, TNil{}, TNil{})), "") == "[[[|1]|3]|6]" : String}

def witness_bracket():
  {==}

law witness_empty:
  {gf(String, ENil{}, TNil{}, TNil{}, TNil{}) == T3{TNil{}, TNil{}, TNil{}} : T3<String>}

def witness_empty():
  {==}

# ---------- broken implementations, refuted by checked inequalities ----------
# reset mutant: forgets the retained state of a repeated key
def gfReset(-A: Data, xs: EL<A>, ta: TL<A>, tb: TL<A>, tc: TL<A>) -> T3<A>:
  match xs:
    case ENil{}:
      T3{ta, tb, tc}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          gfReset(A, t, TCon{v, TNil{}}, tb, tc)
        case KB{}:
          gfReset(A, t, ta, TCon{v, TNil{}}, tc)
        case KC{}:
          gfReset(A, t, ta, tb, TCon{v, TNil{}})

# order mutant: pushes onto the front, reversing order within a key
def gfFront(-A: Data, xs: EL<A>, ta: TL<A>, tb: TL<A>, tc: TL<A>) -> T3<A>:
  match xs:
    case ENil{}:
      T3{ta, tb, tc}
    case ECon{k, +v, +t}:
      match k:
        case KA{}:
          gfFront(A, t, TCon{v, ta}, tb, tc)
        case KB{}:
          gfFront(A, t, ta, TCon{v, tb}, tc)
        case KC{}:
          gfFront(A, t, ta, tb, TCon{v, tc})

def tlen(-A: Data, xs: TL<A>) -> Nat:
  match xs:
    case TNil{}:
      0n
    case TCon{+h, +t}:
      1n+tlen(A, t)

def disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

law reset_differs:
  {slotA(String, gf(String, evs(), TNil{}, TNil{}, TNil{})) != slotA(String, gfReset(String, evs(), TNil{}, TNil{}, TNil{})) : TL<String>}

def reset_differs(e):
  %e : disc(Nat.sub(tlen(String, _), 1n))
  Unit{}

def bdisc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

law front_differs:
  {br(slotA(String, gf(String, evs(), TNil{}, TNil{}, TNil{})), "") != br(slotA(String, gfFront(String, evs(), TNil{}, TNil{}, TNil{})), "") : String}

def front_differs(e):
  %e : bdisc(String.eq(_, "[[[|1]|3]|6]"))
  Unit{}

def reset_generic(-A: Data, +xs: EL<A>) -> {slotA(A, gfReset(A, xs, TNil{}, TNil{}, TNil{})) == selA(A, xs) : TL<A>}:
  match xs:
    case ENil{}:
      {==}
    case ECon{k, +v, +t}:
      reset_generic(A, t)

law main:
  String

def main():
  br(slotA(String, gf(String, evs(), TNil{}, TNil{}, TNil{})), "")
