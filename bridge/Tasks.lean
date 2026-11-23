import TaskCore
/-! `tasks`: one native CLI, three everyday file-driven commands on the typed `.view()` API. -/
open Tasks

def usage : String :=
  "usage:\n  tasks logsum FILE [--level INFO|WARN|ERROR] [--service NAME] [--min-latency N]\n" ++
  "  tasks sales FILE [--min-qty N]\n  tasks manifest FILE [--trace]\n" ++
  "exit: 0 ok | 1 manifest has an invalid entry | 2 unreadable file, invalid UTF-8 or record parse error | 64 usage\n"

def die (code : UInt32) (msg : String) : IO UInt32 := do IO.eprint msg; pure code
def usageErr (m : String) : IO UInt32 := die 64 s!"tasks: {m}\n{usage}"

/-- whole file into memory, then strict UTF-8 decode -/
def readText (path : String) : IO (Except String String) := do
  try
    let b ← IO.FS.readBinFile path
    match String.fromUTF8? b with
    | some s => pure (.ok s)
    | none => pure (.error s!"{path}: invalid UTF-8 (file rejected, nothing replaced)")
  catch e => pure (.error s!"{path}: {e}")

partial def flags (valued switches : List String) : List String → Except String (List (String × String))
  | [] => .ok []
  | f :: rest =>
    if switches.contains f then (flags valued switches rest).map ((f, "") :: ·)
    else if valued.contains f then match rest with
      | v :: rest' => (flags valued switches rest').map ((f, v) :: ·)
      | [] => .error s!"option {f} needs a value"
    else .error s!"unknown option '{f}'"

def natFlag (fs : List (String × String)) (f : String) : Except String Nat :=
  match fs.lookup f with
  | none => .ok 0
  | some v => if isNatStr v then .ok v.toNat! else .error s!"{f} needs a decimal number, got '{v}'"

def cmdLog (path : String) (fs : List (String × String)) : IO UInt32 := do
  let lvl := (fs.lookup "--level").getD "ERROR"
  unless ["INFO", "WARN", "ERROR"].contains lvl do return (← usageErr "--level must be INFO, WARN or ERROR")
  match natFlag fs "--min-latency" with
  | .error m => usageErr m
  | .ok ml =>
    let o : LogOpts := { level := lvl, service := fs.lookup "--service", minLatency := ml }
    match ← readText path with
    | .error e => die 2 (e ++ "\n")
    | .ok txt =>
      let ls := splitLines txt
      match parseLines parseLogLine logSkip ls with
      | .error (n, m) => die 2 s!"{path}:{n}: {m}\n"
      | .ok rs => match logPipe o rs with
        | .error e => die 2 (e ++ "\n")
        | .ok s => do IO.print (logReport path ls.length rs.length o s); pure 0

def cmdSales (path : String) (fs : List (String × String)) : IO UInt32 := do
  match natFlag fs "--min-qty" with
  | .error m => usageErr m
  | .ok mq =>
    let o : SalesOpts := { minQty := mq }
    match ← readText path with
    | .error e => die 2 (e ++ "\n")
    | .ok txt =>
      match parseSales (splitLines txt) with
      | .error (n, m) => die 2 s!"{path}:{n}: {m}\n"
      | .ok rs => match salesPipe o rs with
        | .error e => die 2 (e ++ "\n")
        | .ok g => do IO.print (salesReport path rs.length o g); pure 0

def cmdManifest (path : String) (fs : List (String × String)) : IO UInt32 := do
  let tr := fs.any (·.1 == "--trace")
  match ← readText path with
  | .error e => die 2 (e ++ "\n")
  | .ok txt =>
    let ls := splitLines txt
    let r := manifestPipe tr ls
    let tail := fun (_ : Unit) => do
      if tr then IO.eprintln s!"trace: model findPulls={manifestPulls false ls} (untraced recount); lines buffered before find={ls.length}"
    match r with
    | .error e => die 2 (e ++ "\n")
    | .ok none => do
      IO.print s!"file: {path}\nread: whole file buffered and split into {ls.length} lines before checking\nresult: OK ({ls.length} entries valid)\n"
      tail (); pure 0
    | .ok (some (i, l)) => do
      IO.print s!"file: {path}\nread: whole file buffered and split into {ls.length} lines before checking\nresult: INVALID at line {i + 1}: {(checkEntry l).getD "?"}\nentry: {l}\n"
      tail (); pure 1

def main (args : List String) : IO UInt32 := do
  match args with
  | cmd :: path :: rest =>
    if path.startsWith "--" then usageErr "FILE must come right after the command" else
    match cmd with
    | "logsum" => match flags ["--level", "--service", "--min-latency"] [] rest with
      | .error m => usageErr m | .ok fs => cmdLog path fs
    | "sales" => match flags ["--min-qty"] [] rest with
      | .error m => usageErr m | .ok fs => cmdSales path fs
    | "manifest" => match flags [] ["--trace"] rest with
      | .error m => usageErr m | .ok fs => cmdManifest path fs
    | _ => usageErr s!"unknown command '{cmd}'"
  | [c] => if ["logsum", "sales", "manifest"].contains c then usageErr "missing FILE" else usageErr s!"unknown command '{c}'"
  | [] => usageErr "missing command"
