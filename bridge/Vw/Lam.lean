import Vw.Plan
/-! A compilable pure lambda subset: typed Int/Bool expressions over the element `x` and ONE captured
immutable scalar `c`. Overflow policy: CHECKED signed 32-bit; any out-of-range intermediate traps
(`none`). Lowering: a postfix stack program. Proved equal to source evaluation for ALL inputs. -/
namespace Lam

inductive Ty | int | bool deriving DecidableEq, Repr
abbrev Ty.den : Ty → Type | .int => Int | .bool => Bool

inductive E : Ty → Type
  | x : E .int
  | cap : E .int
  | lit (n : Int) : E .int
  | add (a b : E .int) : E .int
  | sub (a b : E .int) : E .int
  | mul (a b : E .int) : E .int
  | max (a b : E .int) : E .int
  | lt (a b : E .int) : E .bool
  | eq (a b : E .int) : E .bool
  | and (a b : E .bool) : E .bool
  | not (a : E .bool) : E .bool

def chk (v : Int) : Option Int := if -2147483648 ≤ v ∧ v ≤ 2147483647 then some v else none

def eval : {t : Ty} → E t → Int → Int → Option t.den
  | _, .x, x, _ => chk x
  | _, .cap, _, c => chk c
  | _, .lit n, _, _ => chk n
  | _, .add a b, x, c => do let u ← eval a x c; let v ← eval b x c; chk (u + v)
  | _, .sub a b, x, c => do let u ← eval a x c; let v ← eval b x c; chk (u - v)
  | _, .mul a b, x, c => do let u ← eval a x c; let v ← eval b x c; chk (u * v)
  | _, .max a b, x, c => do let u ← eval a x c; let v ← eval b x c; pure (if u ≤ v then v else u)
  | _, .lt a b, x, c => do let u ← eval a x c; let v ← eval b x c; pure (decide (u < v))
  | _, .eq a b, x, c => do let u ← eval a x c; let v ← eval b x c; pure (decide (u = v))
  | _, .and a b, x, c => do let u ← eval a x c; let v ← eval b x c; pure (u && v)
  | _, .not a, x, c => do let u ← eval a x c; pure (!u)

inductive I | px | pc | lit (n : Int) | add | sub | mul | max | lt | eq | and | not deriving DecidableEq, Repr

def b2i (b : Bool) : Int := if b then 1 else 0
def enc : {t : Ty} → t.den → Int | .int, v => v | .bool, b => b2i b

def step (x c : Int) : I → List Int → Option (List Int)
  | .px, s => (chk x).map (· :: s)
  | .pc, s => (chk c).map (· :: s)
  | .lit n, s => (chk n).map (· :: s)
  | .add, v :: u :: s => (chk (u + v)).map (· :: s)
  | .sub, v :: u :: s => (chk (u - v)).map (· :: s)
  | .mul, v :: u :: s => (chk (u * v)).map (· :: s)
  | .max, v :: u :: s => some ((if u ≤ v then v else u) :: s)
  | .lt, v :: u :: s => some (b2i (decide (u < v)) :: s)
  | .eq, v :: u :: s => some (b2i (decide (u = v)) :: s)
  | .and, v :: u :: s => some (b2i (u ≠ 0 && v ≠ 0) :: s)
  | .not, u :: s => some (b2i (u = 0) :: s)
  | _, _ => none

def exec (x c : Int) : List I → List Int → Option (List Int)
  | [], s => some s
  | i :: is, s => (step x c i s).bind (exec x c is)

def compile : {t : Ty} → E t → List I
  | _, .x => [.px] | _, .cap => [.pc] | _, .lit n => [.lit n]
  | _, .add a b => compile a ++ compile b ++ [.add]
  | _, .sub a b => compile a ++ compile b ++ [.sub]
  | _, .mul a b => compile a ++ compile b ++ [.mul]
  | _, .max a b => compile a ++ compile b ++ [.max]
  | _, .lt a b => compile a ++ compile b ++ [.lt]
  | _, .eq a b => compile a ++ compile b ++ [.eq]
  | _, .and a b => compile a ++ compile b ++ [.and]
  | _, .not a => compile a ++ [.not]

theorem exec_append (x c : Int) : ∀ (p q : List I) s, exec x c (p ++ q) s = (exec x c p s).bind (exec x c q)
  | [], q, s => rfl
  | i :: p, q, s => by
    simp only [List.cons_append, exec]; cases step x c i s <;> simp [exec_append x c p q]

theorem bin {t1 t2 : Ty} (x c : Int) (k : List I) (s : List Int) (a b : List I) (op : I) (u : Option t1.den) (v : Option t2.den)
    (ha : ∀ k s, exec x c (a ++ k) s = u.bind fun w => exec x c k (enc w :: s))
    (hb : ∀ k s, exec x c (b ++ k) s = v.bind fun w => exec x c k (enc w :: s)) :
    exec x c (a ++ (b ++ op :: k)) s = u.bind fun p => v.bind fun q => (step x c op (enc q :: enc p :: s)).bind (exec x c k) := by
  rw [ha]; cases u <;> simp [hb, exec]

/-- LOWERING CORRECTNESS for every expression, every x, every captured c, every continuation -/
theorem compile_ok : ∀ {t : Ty} (e : E t) (x c : Int) (k : List I) (s : List Int),
    exec x c (compile e ++ k) s = (eval e x c).bind fun v => exec x c k (enc v :: s)
  | _, .x, x, c, k, s => by simp [compile, eval, exec, step, enc]; cases chk x <;> rfl
  | _, .cap, x, c, k, s => by simp [compile, eval, exec, step, enc]; cases chk c <;> rfl
  | _, .lit n, x, c, k, s => by simp [compile, eval, exec, step, enc]; cases chk n <;> rfl
  | _, .add a b, x, c, k, s => by
    simp only [compile, List.append_assoc, List.singleton_append]
    rw [bin x c k s _ _ _ _ _ (compile_ok a x c) (compile_ok b x c)]
    simp only [eval]; cases eval a x c <;> cases eval b x c <;> simp [step, enc, Option.bind]
    all_goals (generalize chk _ = r; cases r <;> rfl)
  | _, .sub a b, x, c, k, s => by
    simp only [compile, List.append_assoc, List.singleton_append]
    rw [bin x c k s _ _ _ _ _ (compile_ok a x c) (compile_ok b x c)]
    simp only [eval]; cases eval a x c <;> cases eval b x c <;> simp [step, enc, Option.bind]
    all_goals (generalize chk _ = r; cases r <;> rfl)
  | _, .mul a b, x, c, k, s => by
    simp only [compile, List.append_assoc, List.singleton_append]
    rw [bin x c k s _ _ _ _ _ (compile_ok a x c) (compile_ok b x c)]
    simp only [eval]; cases eval a x c <;> cases eval b x c <;> simp [step, enc, Option.bind]
    all_goals (generalize chk _ = r; cases r <;> rfl)
  | _, .max a b, x, c, k, s => by
    simp only [compile, List.append_assoc, List.singleton_append]
    rw [bin x c k s _ _ _ _ _ (compile_ok a x c) (compile_ok b x c)]
    simp only [eval]; cases eval a x c <;> cases eval b x c <;> simp [step, enc, Option.bind]
  | _, .lt a b, x, c, k, s => by
    simp only [compile, List.append_assoc, List.singleton_append]
    rw [bin x c k s _ _ _ _ _ (compile_ok a x c) (compile_ok b x c)]
    simp only [eval]; cases eval a x c <;> cases eval b x c <;> simp [step, enc, Option.bind]
  | _, .eq a b, x, c, k, s => by
    simp only [compile, List.append_assoc, List.singleton_append]
    rw [bin x c k s _ _ _ _ _ (compile_ok a x c) (compile_ok b x c)]
    simp only [eval]; cases eval a x c <;> cases eval b x c <;> simp [step, enc, Option.bind]
  | _, .and a b, x, c, k, s => by
    simp only [compile, List.append_assoc, List.singleton_append]
    rw [bin x c k s _ _ _ _ _ (compile_ok a x c) (compile_ok b x c)]
    simp only [eval]; cases eval a x c <;> cases eval b x c <;> simp [step, enc, Option.bind]
    all_goals (rename_i p q; cases p <;> cases q <;> rfl)
  | _, .not a, x, c, k, s => by
    simp only [compile, List.append_assoc, List.singleton_append]
    rw [compile_ok a x c]
    simp only [eval]; cases eval a x c <;> simp [step, enc, exec, Option.bind]
    rename_i p; cases p <;> rfl

theorem lowered_eq (e : E t) (x c : Int) : exec x c (compile e) [] = (eval e x c).map fun v => [enc v] := by
  have := compile_ok e x c [] []; rw [List.append_nil] at this; rw [this]; cases eval e x c <;> rfl

/-- example: `fun x => 3*x - c < 100` with captured c -/
def pred : E .bool := .lt (.sub (.mul (.lit 3) .x) .cap) (.lit 100)
theorem pred_ex : eval pred 40 25 = some true ∧ eval pred 2147483647 0 = none := by decide
end Lam

namespace Vw.View
/-- a compiled-lambda map stage; a trap is kept IN ORDER as `none` in the stream -/
def mapE (v : View Int) (e : Lam.E .int) (c : Int) : View (Option Int) := v.map fun x => Lam.eval e x c
end Vw.View
