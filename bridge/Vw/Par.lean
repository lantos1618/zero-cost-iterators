import Vw.Plan
/-! `.parallelize k`: legality is decided by the TERMINAL. Accepted only when the terminal carries a
monoid (associative, two-sided identity); an unordered combine additionally needs commutativity.
"Accepted" means the chunked schedule below is proved equal to the ordered result and is executed
by this Lean evaluator chunk by chunk; there is NO parallel runtime or GPU backend here. -/
namespace Vw
variable {α : Type}

structure Mon (α : Type) where
  op : α → α → α
  e : α
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  idl : ∀ a, op e a = a
  idr : ∀ a, op a e = a
  comm : Option (PLift (∀ a b, op a b = op b a))
  name : String

theorem foldl_shift (M : Mon α) : ∀ (a : α) (l : List α), l.foldl M.op a = M.op a (l.foldl M.op M.e)
  | a, [] => by simp [M.idr]
  | a, x :: xs => by
    simp only [List.foldl]
    rw [foldl_shift M (M.op a x) xs, foldl_shift M (M.op M.e x) xs, M.idl, M.assoc]

/-- consecutive blocks of k; the short tail block is KEPT (every item is reduced once) -/
def blocksF : Nat → Nat → List α → List (List α)
  | 0, _, xs => [xs]
  | f + 1, k, xs => if xs.length ≤ k then [xs] else xs.take k :: blocksF f k (xs.drop k)
def blocks (k : Nat) (xs : List α) : List (List α) := blocksF xs.length k xs
theorem blocksF_flatten : ∀ (f k : Nat) (xs : List α), (blocksF f k xs).flatten = xs
  | 0, _, xs => by simp [blocksF]
  | f + 1, k, xs => by
    unfold blocksF; split
    · simp
    · simp [blocksF_flatten f k (xs.drop k)]

theorem foldl_flatten (M : Mon α) : ∀ (L : List (List α)) (a : α),
    L.flatten.foldl M.op a = (L.map (·.foldl M.op M.e)).foldl M.op a
  | [], a => rfl
  | c :: L, a => by
    simp only [List.flatten_cons, List.foldl_append, List.map_cons, List.foldl_cons]
    rw [foldl_flatten M L, foldl_shift M a c]

/-- ordered chunked schedule: reduce each block, combine block results left to right -/
def parReduce (M : Mon α) (k : Nat) (xs : List α) : α :=
  ((blocks k xs).map (·.foldl M.op M.e)).foldl M.op M.e
theorem parReduce_eq (M : Mon α) (k : Nat) (xs : List α) : parReduce M k xs = xs.foldl M.op M.e := by
  rw [parReduce, ← foldl_flatten, blocks, blocksF_flatten]

theorem foldl_eq_foldr (M : Mon α) : ∀ l : List α, l.foldl M.op M.e = l.foldr M.op M.e
  | [] => rfl
  | x :: xs => by
    simp only [List.foldl, List.foldr]; rw [foldl_shift, M.idl, foldl_eq_foldr M xs]

/-- unordered schedule (block results combined in REVERSE order): needs commutativity -/
def parReduceAny (M : Mon α) (k : Nat) (xs : List α) : α :=
  ((blocks k xs).map (·.foldl M.op M.e)).reverse.foldl M.op M.e
theorem parReduceAny_eq (M : Mon α) (hc : ∀ a b, M.op a b = M.op b a) (k : Nat) (xs : List α) :
    parReduceAny M k xs = xs.foldl M.op M.e := by
  rw [parReduceAny, foldl_eq_foldr, List.foldr_reverse, ← parReduce_eq M k xs, parReduce]
  congr 1; funext a b; exact hc b a

def intAdd : Mon Int := ⟨(· + ·), 0, Int.add_assoc, Int.zero_add, Int.add_zero, some ⟨Int.add_comm⟩, "Int +"⟩
def intMul : Mon Int := ⟨(· * ·), 1, Int.mul_assoc, Int.one_mul, Int.mul_one, some ⟨Int.mul_comm⟩, "Int *"⟩
def natAdd : Mon Nat := ⟨(· + ·), 0, Nat.add_assoc, Nat.zero_add, Nat.add_zero, some ⟨Nat.add_comm⟩, "Nat +"⟩
/-- sequence concatenation: associative, NOT commutative -/
def listApp : Mon (List Nat) := ⟨(· ++ ·), [], List.append_assoc, List.nil_append, List.append_nil, none, "List ++"⟩
def strApp : Mon String := ⟨(· ++ ·), "", String.append_assoc, String.empty_append, String.append_empty, none, "String ++"⟩
def boolAnd : Mon Bool := ⟨(· && ·), true, Bool.and_assoc, Bool.true_and, Bool.and_true, some ⟨Bool.and_comm⟩, "Bool &&"⟩
end Vw

namespace Vw.View
open Vw
variable {α : Type}
def reduce (v : View α) (M : Mon α) : Except String α :=
  match v.chunks with
  | none => .ok (v.items.foldl M.op M.e)
  | some 0 => .error "refused: parallelize(0)"
  | some k => .ok (parReduce M k v.items)
def reduceUnordered (v : View α) (M : Mon α) : Except String α :=
  match v.chunks, M.comm with
  | some (k + 1), some _ => .ok (parReduceAny M (k + 1) v.items)
  | some _, none => .error ("refused: unordered combine needs a commutative op; " ++ M.name ++ " is not")
  | _, _ => .error "refused: reduceUnordered needs parallelize(k ≥ 1)"
/-- accumulate seed = foldl seed (+), ordered Int addition -/
def accumulate (v : View Int) (seed : Int) : Except String Int := (v.reduce intAdd).map (seed + ·)

theorem reduce_ok (v : View α) (M : Mon α) (h : v.chunks ≠ some 0) :
    v.reduce M = .ok ((den v.plan).foldl M.op M.e) := by
  unfold reduce; split
  · simp [items_eq]
  · contradiction
  · simp [parReduce_eq, items_eq]
theorem reduceUnordered_ok (v : View α) (M : Mon α) (r : α) (h : v.reduceUnordered M = .ok r) :
    r = (den v.plan).foldl M.op M.e := by
  unfold reduceUnordered at h; split at h
  · rename_i c _ _; cases h
    exact (parReduceAny_eq M c.down _ _).trans (by rw [items_eq])
  all_goals cases h
theorem accumulate_ok (v : View Int) (seed : Int) (h : v.chunks ≠ some 0) :
    v.accumulate seed = .ok ((den v.plan).foldl (· + ·) seed) := by
  simp only [accumulate, reduce_ok v intAdd h, Except.map]
  congr 1; exact (foldl_shift intAdd seed _).symm
end Vw.View
