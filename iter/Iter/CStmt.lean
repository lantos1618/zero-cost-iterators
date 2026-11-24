import Iter.CExpr
/-! C statements with their own meaning, next to the expressions of `Iter/CExpr.lean`.

`CS.exec` runs a statement on a store (`Slot → UInt64`) and gives `none` if an expression is undefined,
`.ret v` if a `return` was taken, and `.ok store` if control falls through. `CS.print` is one fixed rule per
node; it is trusted, like `CE.print`. Generators that build a `CS` and prove its `exec` prints programs whose
control flow, not only their expressions, is covered by a theorem. -/
namespace Iter.C

inductive CS where
  | skip
  /-- `s = e;` -/
  | assign (s : Slot) (e : CE)
  /-- `if (!c) return r;` -/
  | guard (c r : CE)
  | seq (a b : CS)
  /-- `if (c) { t }` -/
  | when (c : CE) (t : CS)
  /-- `for (std::uint64_t x : xs) { body }`: `x` is each input item in turn; a `return` leaves the loop -/
  | each (body : CS)

inductive Out where
  | ok (env : Slot → UInt64)
  | ret (v : UInt64)

def upd (env : Slot → UInt64) (s : Slot) (v : UInt64) : Slot → UInt64 :=
  fun t => if t = s then v else env t

@[simp] theorem upd_same (env : Slot → UInt64) (s : Slot) (v : UInt64) : upd env s v s = v := by simp [upd]
theorem upd_other (env : Slot → UInt64) {s t : Slot} (v : UInt64) (h : t ≠ s) : upd env s v t = env t := by
  simp [upd, h]

/-- the meaning of a statement over the input `xs`: `none` is undefined behaviour, `.ret` a `return`,
`.ok env` falling through with the new variables -/
def CS.exec (xs : List UInt64) : CS → (Slot → UInt64) → Option Out
  | .skip, env => some (.ok env)
  | .assign s e, env => (e.eval env).map fun v => .ok (upd env s v)
  | .guard c r, env => match c.eval env with
    | none => none
    | some v => if v = 0 then (r.eval env).map .ret else some (.ok env)
  | .seq a b, env => match a.exec xs env with
    | some (.ok env') => b.exec xs env'
    | o => o
  | .when c t, env => match c.eval env with
    | none => none
    | some v => if v = 0 then some (.ok env) else t.exec xs env
  | .each body, env => xs.foldl (fun o x => match o with
    | some (.ok e) => body.exec xs (upd e .x x)
    | o => o) (some (.ok env))

def CS.print (nm : Slot → String) (ret : String → String) : CS → List String
  | .skip => []
  | .assign s e => [s!"{nm s} = {e.print nm};"]
  | .guard c r => [s!"if (!{c.print nm}) return {ret (r.print nm)};"]
  | .seq a b => a.print nm ret ++ b.print nm ret
  | .when c t => [s!"if ({c.print nm}) \{"] ++ (t.print nm ret).map ("  " ++ ·) ++ ["}"]
  | .each body => ["for (std::uint64_t x : xs) {"] ++ (body.print nm ret).map ("  " ++ ·) ++ ["}"]

end Iter.C
