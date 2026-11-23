import Bridge.IR
import Bridge.CSyntax
import Bridge.BendParse
/-! The authoritative acceptance path. `validate f` lifts the parsed C file to an IR program `p` and
accepts only if `render p = some f`, i.e. the file is exactly the canonical rendering of `p`:
fixed directives, guard, the three declarations, one `for` per IR loop with its statements in order,
then `*out = acc;`, `return 0;`. -/
namespace Check
open C IR

def dirsFor (k : Nat) : List Dir := [.inc "stddef.h", .inc "stdint.h", .dfn "I8DOT_MAX_N" k]
def stdDirs : List Dir := dirsFor 131071
/-- per-reduction length guard: the largest n whose worst-case accumulation fits int32 -/
def bound (p : Prog) : Nat :=
  if p = l1IR then 8421504 else if p = l2IR then 33025 else if p = hamIR then 2147483647
  else if p = oslIR then 8421504 else 131071

def opS : Op → Option (List S)
  | .LdA => some [.assign .r0 (.ld .a)]
  | .LdB => some [.assign .r1 (.ld .b)]
  | .Mul => some [.assign .r0 (.mul (.var .r0) (.var .r1))]
  | .Acc => some [.assign .acc (.add (.var .acc) (.var .r0))]
  | .Wrap => some [.assign .acc (.toI32 (.andU (.toU32 (.var .acc)) 255)),
                   .ifGt .acc 127 .acc (.sub (.var .acc) (.lit 256))]
  | .StT => none
  | .LdT => none
  | .Sub => some [.assign .r0 (.sub (.var .r0) (.var .r1))]
  | .Abs => some [.ifLt .r0 0 .r0 (.neg (.var .r0))]
  | .Sq => some [.assign .r0 (.mul (.var .r0) (.var .r0))]
  | .Pos => some [.ifLt .r0 0 .r0 (.lit 0)]
  | .Bit => some [.ifGt .r0 0 .r0 (.lit 1)]
  | .AbsT => some [.assign .r0 (.condLt .r0 0 (.neg (.var .r0)) (.var .r0))]
  | .Ne0 => some [.assign .r0 (.ne (.var .r0) (.lit 0))]

def mapO {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: r => do let b ← f x; let bs ← mapO f r; pure (b :: bs)

def renderOps : List Op → Option (List S)
  | [] => some []
  | o :: r => do let a ← opS o; let b ← renderOps r; pure (a ++ b)

def renderPS : PS → Option T
  | .Alloc => none
  | .Loop [] => none
  | .Loop ops => T.forN <$> renderOps ops

def prologue : List T := [.guard "I8DOT_MAX_N" (-1), .decl .acc 0, .decl .r0 0, .decl .r1 0]
def epilogue : List T := [.store .acc, .ret 0]

def render (p : Prog) : Option CFile :=
  match p with
  | [] => none
  | _ => do let ls ← mapO renderPS p; pure ⟨dirsFor (bound p), prologue ++ ls ++ epilogue⟩

/-- lifting heuristic (only completeness depends on it; soundness goes through `render`) -/
def liftS : List S → Option (List Op)
  | [] => some []
  | .assign .acc (.toI32 (.andU (.toU32 (.var .acc)) 255)) :: .ifGt .acc 127 .acc (.sub (.var .acc) (.lit 256)) :: r =>
    (Op.Wrap :: ·) <$> liftS r
  | .assign .r0 (.ld .a) :: r => (Op.LdA :: ·) <$> liftS r
  | .assign .r0 (.sub (.var .r0) (.var .r1)) :: r => (Op.Sub :: ·) <$> liftS r
  | .ifLt .r0 0 .r0 (.neg (.var .r0)) :: r => (Op.Abs :: ·) <$> liftS r
  | .assign .r0 (.mul (.var .r0) (.var .r0)) :: r => (Op.Sq :: ·) <$> liftS r
  | .ifLt .r0 0 .r0 (.lit 0) :: r => (Op.Pos :: ·) <$> liftS r
  | .ifGt .r0 0 .r0 (.lit 1) :: r => (Op.Bit :: ·) <$> liftS r
  | .assign .r0 (.condLt .r0 0 (.neg (.var .r0)) (.var .r0)) :: r => (Op.AbsT :: ·) <$> liftS r
  | .assign .r0 (.ne (.var .r0) (.lit 0)) :: r => (Op.Ne0 :: ·) <$> liftS r
  | .assign .r1 (.ld .b) :: r => (Op.LdB :: ·) <$> liftS r
  | .assign .r0 (.mul (.var .r0) (.var .r1)) :: r => (Op.Mul :: ·) <$> liftS r
  | .assign .acc (.add (.var .acc) (.var .r0)) :: r => (Op.Acc :: ·) <$> liftS r
  | _ => none

def liftBody (b : List T) : Option Prog :=
  mapO (fun t => match t with
    | .forN s => PS.Loop <$> liftS s
    | _ => none) (b.filter fun t => match t with | .forN _ => true | _ => false)

/-- unverified diagnostic: first position where the body leaves the grammar -/
def explain (f : CFile) : String :=
  if (match f.dirs with | [.dfn "I8DOT_MAX_N" _] => false | [_, _, .dfn "I8DOT_MAX_N" k] => f.dirs ≠ dirsFor k | _ => true) then s!"directives {reprStr f.dirs} ≠ the fixed include/define block" else
  if f.dirs ≠ dirsFor (match liftBody f.body with | some p => bound p | none => 131071) then
    s!"length guard: #define I8DOT_MAX_N must equal the certified bound {match liftBody f.body with | some p => bound p | none => 131071} for this loop body (found {reprStr f.dirs})" else
  let rec pre : List T → List T → Nat → String
    | t :: r, e :: es, k => if t = e then pre r es (k + 1) else s!"statement {k}: expected `{e.show}`, found `{t.show}`"
    | [], e :: _, k => s!"statement {k}: expected `{e.show}`, found end of body"
    | r, [], k => loops r k 0
  , loops : List T → Nat → Nat → String
    | .forN _ :: r, k, c => loops r (k + 1) (c + 1)
    | r, k, c => if c = 0 then s!"statement {k}: expected `for (size_t i = 0; i < n; i++) {"{"}`, found {(r.head?.map T.show).getD "end of body"}"
                 else post r epilogue k
  , post : List T → List T → Nat → String
    | t :: r, e :: es, k => if t = e then post r es (k + 1) else s!"statement {k}: expected `{e.show}` (after the last loop), found `{t.show}`"
    | [], e :: _, k => s!"statement {k}: expected `{e.show}`, found end of body"
    | t :: _, [], k => s!"statement {k}: trailing `{t.show}` after `return 0;`"
    | [], [], _ => "loop body outside the supported op sequences (e.g. empty loop or unknown op order)"
  pre f.body prologue 0

def validate (f : CFile) : Except String Prog :=
  match liftBody f.body with
  | some p => if render p = some f then .ok p else .error (explain f)
  | none => .error (explain f)

/-- exact (non-wrapping) reductions: dot, L1, squared L2 -/
def exactCert (p : Prog) : Bool := decide (p = posIR) || decide (p = l1IR) || decide (p = l2IR) ||
  decide (p = hamIR) || decide (p = oslIR)
/-- programs whose C-semantics totality is proved (`Proofs.cRun_wrap`, `Proofs.cert_total`) -/
def certified (p : Prog) : Bool := decide (p = posIR) || decide (p = wrapIR) || decide (p = l1IR) || decide (p = l2IR) ||
  decide (p = hamIR) || decide (p = oslIR)

inductive Verdict | pass (p : Prog) | rejectC (why : String) | rejectBend (why : String) | mismatch (c b : Prog)
  | uncertified (p : Prog)

def gate (csrc bsrc : String) (exact : Bool) : Verdict :=
  match C.parseFile csrc with
  | .error e => .rejectC e
  | .ok f => match validate f with
    | .error e => .rejectC e
    | .ok p => match BendP.parseBend bsrc with
      | .error e => .rejectBend e
      | .ok q =>
        if p ≠ q then .mismatch p q
        else if exact then (if exactCert q then .pass p else .mismatch p q)
        else if certified q then .pass p else .uncertified p

/-- match gate: the C file is the canonical rendering of exactly the IR term in prog.bend, AND that term is certified total -/
def matchGate (csrc bsrc : String) : Bool := match gate csrc bsrc false with | .pass _ => true | _ => false
/-- exact gate: match gate AND that IR is one of the exact reductions posIR (dot), l1IR, l2IR, hamIR, oslIR -/
def exactGate (csrc bsrc : String) : Bool := match gate csrc bsrc true with | .pass _ => true | _ => false

end Check
