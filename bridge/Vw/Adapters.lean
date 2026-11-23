import Vw.Machine
/-! Adapters: each is an executable machine plus an INDEPENDENT whole-list reference meaning,
with a proof that feeding the machine from its initial state yields the reference. -/
namespace Vw
variable {σ α β : Type}

structure Ad (σ α : Type) where
  m : M σ α
  ref : List σ → List α
  ok : ∀ xs, (m.feed m.init xs).2 = ref xs
  ab : Absorb m
  name : String
  /-- retained state, as stated for the README (not a proof object) -/
  state : String

def idM : M σ σ := ⟨Unit, (), fun s x => (s, [x]), fun _ => false⟩
theorem idM_step (s : Unit) (x : σ) : (idM (σ := σ)).step s x = (s, [x]) := rfl
theorem idM_feed : ∀ (s : Unit) (xs : List σ), ((idM (σ := σ)).feed s xs).2 = xs
  | _, [] => by simp [M.feed]
  | s, x :: xs => by simp [M.feed, idM_step, idM_feed _ xs]

def Ad.comp (a : Ad σ α) (b : Ad α β) : Ad σ β where
  m := a.m.comp b.m
  ref := fun xs => b.ref (a.ref xs)
  ok := fun xs => by
    show ((a.m.comp b.m).feed (a.m.init, b.m.init) xs).2 = _
    rw [comp_feed]; simp only; rw [a.ok, b.ok]
  ab := comp_absorb _ _ a.ab b.ab
  name := a.name ++ " > " ++ b.name
  state := a.state ++ " + " ++ b.state

/-- map f : stateless -/
def mapM (f : σ → α) : M σ α := ⟨Unit, (), fun s x => (s, [f x]), fun _ => false⟩
theorem mapM_step (f : σ → α) s x : (mapM f).step s x = (s, [f x]) := rfl
theorem mapM_feed (f : σ → α) : ∀ s xs, ((mapM f).feed s xs).2 = xs.map f
  | _, [] => by simp [M.feed]
  | s, x :: xs => by simp [M.feed, mapM_step, mapM_feed f _ xs]
def map (f : σ → α) : Ad σ α := ⟨mapM f, (·.map f), mapM_feed f (), fun _ _ h => by simp [mapM] at h, "map", "none"⟩

/-- filter p : stateless -/
def filterM (p : σ → Bool) : M σ σ := ⟨Unit, (), fun s x => (s, if p x then [x] else []), fun _ => false⟩
theorem filterM_step (p : σ → Bool) s x : (filterM p).step s x = (s, if p x then [x] else []) := rfl
theorem filterM_feed (p : σ → Bool) : ∀ s xs, ((filterM p).feed s xs).2 = xs.filter p
  | _, [] => by simp [M.feed]
  | s, x :: xs => by
    by_cases h : p x = true <;> simp [M.feed, filterM_step, filterM_feed p _ xs, List.filter_cons, h]
def filter (p : σ → Bool) : Ad σ σ := ⟨filterM p, (·.filter p), filterM_feed p (), fun _ _ h => by simp [filterM] at h, "filter", "none"⟩

/-- take n : one Nat counter; done (stops pulling) once n items were emitted -/
def takeM (n : Nat) : M σ σ := ⟨Nat, n, fun k x => if k = 0 then (0, []) else (k - 1, [x]), fun k => k == 0⟩
theorem takeM_step (n k : Nat) (x : σ) : (takeM n).step k x = if k = 0 then (0, []) else (k - 1, [x]) := rfl
theorem takeM_feed (n : Nat) : ∀ (k : Nat) (xs : List σ), ((takeM n).feed k xs).2 = xs.take k := by
  intro k xs; induction xs generalizing k with
  | nil => simp [M.feed]
  | cons x xs ih =>
    cases k with
    | zero => have := ih 0; simp_all [M.feed, takeM]
    | succ k => simp [M.feed, takeM_step, ih]
def take (n : Nat) : Ad σ σ :=
  ⟨takeM n, (·.take n), takeM_feed n n, fun k _ h => by simp [takeM] at h ⊢; simp [h], "take", "1 Nat counter"⟩

/-- drop n : one Nat counter; never done -/
def dropM (n : Nat) : M σ σ := ⟨Nat, n, fun k x => if k = 0 then (0, [x]) else (k - 1, []), fun _ => false⟩
theorem dropM_step (n k : Nat) (x : σ) : (dropM n).step k x = if k = 0 then (0, [x]) else (k - 1, []) := rfl
theorem dropM_feed (n : Nat) : ∀ (k : Nat) (xs : List σ), ((dropM n).feed k xs).2 = xs.drop k := by
  intro k xs; induction xs generalizing k with
  | nil => simp [M.feed]
  | cons x xs ih => cases k <;> simp [M.feed, dropM_step, ih]
def drop (n : Nat) : Ad σ σ := ⟨dropM n, (·.drop n), dropM_feed n n, fun _ _ h => by simp [dropM] at h, "drop", "1 Nat counter"⟩

/-- enumerate : one Nat index, 0-based -/
def enumM : M σ (Nat × σ) := ⟨Nat, 0, fun i x => (i + 1, [(i, x)]), fun _ => false⟩
theorem enumM_step (i : Nat) (x : σ) : (enumM (σ := σ)).step i x = (i + 1, [(i, x)]) := rfl
theorem enumM_feed : ∀ (i : Nat) (xs : List σ), ((enumM (σ := σ)).feed i xs).2 = xs.enumFrom i := by
  intro i xs; induction xs generalizing i with
  | nil => simp [M.feed]
  | cons x xs ih => simp [M.feed, enumM_step, ih]
def enumerate : Ad σ (Nat × σ) := ⟨enumM, List.enum, enumM_feed 0, fun _ _ h => by simp [enumM] at h, "enumerate", "1 Nat index"⟩

/-- inclusive scan: the seed is NOT emitted; output i is f(..f(seed,x0)..,xi). Reference = tail of scanl -/
def scanM (f : β → σ → β) (seed : β) : M σ β := ⟨β, seed, fun a x => (f a x, [f a x]), fun _ => false⟩
/-- independent reference: output i is the left fold of the first i+1 items (APL-style +\\ meaning) -/
def prefixFolds (f : β → σ → β) (a : β) (xs : List σ) : List β :=
  (List.range xs.length).map fun i => (xs.take (i + 1)).foldl f a
theorem prefixFolds_cons (f : β → σ → β) (a : β) (x : σ) (xs : List σ) :
    prefixFolds f a (x :: xs) = f a x :: prefixFolds f (f a x) xs := by
  simp [prefixFolds, List.range_succ_eq_map, Function.comp_def]
theorem scanM_step (f : β → σ → β) seed a x : (scanM f seed).step a x = (f a x, [f a x]) := rfl
theorem scanM_feed (f : β → σ → β) (seed : β) : ∀ (a : β) (xs : List σ),
    ((scanM f seed).feed a xs).2 = prefixFolds f a xs := by
  intro a xs; induction xs generalizing a with
  | nil => simp [M.feed, prefixFolds]
  | cons x xs ih => rw [prefixFolds_cons]; simp [M.feed, scanM_step, ih]
def scan (f : β → σ → β) (seed : β) : Ad σ β :=
  ⟨scanM f seed, prefixFolds f seed, scanM_feed f seed seed, fun _ _ h => by simp [scanM] at h,
   "scan", "1 accumulator"⟩

/-- finite flatMap: inner list emitted in order before the next outer pull -/
def flatMapM (g : σ → List α) : M σ α := ⟨Unit, (), fun s x => (s, g x), fun _ => false⟩
theorem flatMapM_step (g : σ → List α) s x : (flatMapM g).step s x = (s, g x) := rfl
theorem flatMapM_feed (g : σ → List α) : ∀ s xs, ((flatMapM g).feed s xs).2 = xs.flatMap g
  | _, [] => by simp [M.feed]
  | s, x :: xs => by simp [M.feed, flatMapM_step, flatMapM_feed g _ xs]
def flatMap (g : σ → List α) : Ad σ α :=
  ⟨flatMapM g, (·.flatMap g), flatMapM_feed g (), fun _ _ h => by simp [flatMapM] at h, "flatMap", "none (inner list from g)"⟩

/-- independent reference for global distinct: keep the head, delete its later copies, recurse -/
def dedupRef [DecidableEq σ] : List σ → List σ
  | [] => []
  | x :: xs => x :: dedupRef (xs.filter (fun y => y ≠ x))
termination_by xs => xs.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _)
theorem dedupRef_nil [DecidableEq σ] : dedupRef ([] : List σ) = [] := by rw [dedupRef]
theorem dedupRef_cons [DecidableEq σ] (x : σ) xs : dedupRef (x :: xs) = x :: dedupRef (xs.filter (fun y => y ≠ x)) := by rw [dedupRef]

/-- global distinct: retains the list of already-emitted values (grows with #distinct) -/
def distinctM [DecidableEq σ] : M σ σ :=
  ⟨List σ, [], fun seen x => if x ∈ seen then (seen, []) else (seen ++ [x], [x]), fun _ => false⟩
theorem distinctM_step [DecidableEq σ] (seen : List σ) (x : σ) : (distinctM (σ := σ)).step seen x = if x ∈ seen then (seen, []) else (seen ++ [x], [x]) := rfl
theorem distinctM_feed [DecidableEq σ] : ∀ (seen : List σ) (xs : List σ),
    ((distinctM (σ := σ)).feed seen xs).2 = dedupRef (xs.filter (fun y => y ∉ seen)) := by
  intro seen xs; induction xs generalizing seen with
  | nil => simp [M.feed, dedupRef_nil]
  | cons x xs ih =>
    by_cases h : x ∈ seen
    · simp [M.feed, distinctM_step, h, ih, List.filter_cons]
    · simp only [M.feed, distinctM_step, h, if_false, ih, List.filter_cons, decide_not, Bool.not_eq_true',
        decide_eq_false_iff_not, not_false_eq_true, if_true, List.singleton_append, dedupRef_cons, List.filter_filter]
      congr 2; apply List.filter_congr; intro y _
      by_cases h1 : y = x <;> by_cases h2 : y ∈ seen <;> simp_all
def distinct [DecidableEq σ] : Ad σ σ :=
  ⟨distinctM, dedupRef, fun xs => by show (distinctM.feed [] xs).2 = _; rw [distinctM_feed]; congr 1; exact List.filter_eq_self.2 (by simp), fun _ _ h => by simp [distinctM] at h,
   "distinct", "list of values seen so far (unbounded; O(#distinct))"⟩

end Vw
