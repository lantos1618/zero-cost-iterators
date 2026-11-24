import TaskCore
/-! `tasks`: one native CLI, three everyday file-driven commands on the `Iter` API. -/
open Tasks

def exitOk : UInt32 := 0
def exitInvalid : UInt32 := 1   -- manifest has an invalid entry
def exitInput : UInt32 := 2     -- unreadable file, invalid UTF-8 or record parse error
def exitUsage : UInt32 := 64

def optLevel := "--level"
def optService := "--service"
def optMinLatency := "--min-latency"
def optMinQty := "--min-qty"
def optTrace := "--trace"

def usage : String :=
  s!"usage:\n  tasks logsum FILE [{optLevel} {"|".intercalate logLevels}] [{optService} NAME] [{optMinLatency} N]\n" ++
  s!"  tasks sales FILE [{optMinQty} N]\n  tasks manifest FILE [{optTrace}]\n" ++
  s!"exit: {exitOk} ok | {exitInvalid} manifest has an invalid entry | " ++
  s!"{exitInput} unreadable file, invalid UTF-8 or record parse error | {exitUsage} usage\n"

/-- every way a command fails; `main` turns each into its message and exit code -/
inductive Failure where
  | usage (msg : String)
  | input (msg : String)

abbrev Cmd := ExceptT Failure IO

/-- whole file into memory, then strict UTF-8 decode -/
def readText (path : String) : Cmd String := do
  match ← (IO.FS.readBinFile path).toBaseIO with
  | .error e => throw (.input s!"{path}: {e}")
  | .ok b =>
    match String.fromUTF8? b with
    | some s => pure s
    | none => throw (.input s!"{path}: invalid UTF-8 (file rejected, nothing replaced)")

/-- read and split the file, then parse its lines; a parse error names the file and line -/
def parsed {α : Type} (path : String) (parse : List String → Except (Nat × String) α) :
    Cmd (List String × α) := do
  let ls := splitLines (← readText path)
  match parse ls with
  | .error (n, m) => throw (.input s!"{path}:{n}: {m}")
  | .ok rs => pure (ls, rs)

partial def flags (valued switches : List String) : List String → Except String (List (String × String))
  | [] => .ok []
  | f :: rest =>
    if switches.contains f then (flags valued switches rest).map ((f, "") :: ·)
    else if valued.contains f then match rest with
      | v :: rest' => (flags valued switches rest').map ((f, v) :: ·)
      | [] => .error s!"option {f} needs a value"
    else .error s!"unknown option '{f}'"

def natFlag (fs : List (String × String)) (f : String) : Cmd Nat :=
  match fs.lookup f with
  | none => pure 0
  | some v => if isNatStr v then pure v.toNat! else throw (.usage s!"{f} needs a decimal number, got '{v}'")

def cmdLog (path : String) (fs : List (String × String)) : Cmd UInt32 := do
  let level := (fs.lookup optLevel).getD ({} : LogOpts).level
  unless logLevels.contains level do throw (.usage s!"{optLevel} must be {oneOf logLevels}")
  let o : LogOpts := { level, service := fs.lookup optService, minLatency := ← natFlag fs optMinLatency }
  let (ls, rs) ← parsed path (parseLines parseLogLine logSkip ·)
  IO.print (logReport path ls.length rs.length o (logPipe o rs))
  pure exitOk

def cmdSales (path : String) (fs : List (String × String)) : Cmd UInt32 := do
  let o : SalesOpts := { minQty := ← natFlag fs optMinQty }
  let (_, rs) ← parsed path parseSales
  IO.print (salesReport path rs.length o (salesPipe o rs))
  pure exitOk

def cmdManifest (path : String) (fs : List (String × String)) : Cmd UInt32 := do
  let tr := fs.any (·.1 == optTrace)
  let ls := splitLines (← readText path)
  let (result, code) : String × UInt32 := match manifestPipe tr ls with
    | none => (s!"OK ({ls.length} entries valid)\n", exitOk)
    | some (i, l) => (s!"INVALID at line {i + 1}: {(checkEntry l).getD "?"}\nentry: {l}\n", exitInvalid)
  IO.print s!"file: {path}\nread: whole file buffered and split into {ls.length} lines before checking\nresult: {result}"
  if tr then
    IO.eprintln s!"trace: pulls={manifestPulls false ls} (counted rerun); lines buffered before find={ls.length}"
  pure code

structure Command where
  name : String
  valued : List String
  switches : List String
  run : String → List (String × String) → Cmd UInt32

def commands : List Command :=
  [⟨"logsum", [optLevel, optService, optMinLatency], [], cmdLog⟩,
   ⟨"sales", [optMinQty], [], cmdSales⟩,
   ⟨"manifest", [], [optTrace], cmdManifest⟩]

def dispatch : List String → Cmd UInt32
  | name :: path :: rest => do
    if path.startsWith "--" then throw (.usage "FILE must come right after the command")
    let some c := commands.find? (·.name == name) | throw (.usage s!"unknown command '{name}'")
    match flags c.valued c.switches rest with
    | .error m => throw (.usage m)
    | .ok fs => c.run path fs
  | [name] => throw (.usage (if commands.any (·.name == name) then "missing FILE" else s!"unknown command '{name}'"))
  | [] => throw (.usage "missing command")

def main (args : List String) : IO UInt32 := do
  match ← (dispatch args).run with
  | .ok code => pure code
  | .error (.usage m) => IO.eprint s!"tasks: {m}\n{usage}"; pure exitUsage
  | .error (.input m) => IO.eprintln m; pure exitInput
