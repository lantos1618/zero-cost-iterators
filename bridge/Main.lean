import Bridge
open Check

def usage : IO UInt32 := do
  IO.println "usage: i8check (exact|match) FILE.c PROG.bend | i8check csem FILE.c"; pure 64

def csem (path : String) : IO UInt32 := do
  match C.parseFile (← IO.FS.readFile path) with
  | .error e => IO.println s!"C parse REJECT: {e}"; pure 2
  | .ok f =>
    IO.println s!"parsed C AST body: {f.body.map C.T.show}"
    for (nm, a, b) in [("empty", ([] : List Int), ([] : List Int)), ("mixed_signs", [3, -5, 7], [-2, 4, 1]),
        ("extremes", [-128, 127, -128, 127], [-128, -128, 127, 127]), ("all_min_3", [-128, -128, -128], [-128, -128, -128]), ("wrap_witness_12x11", [12], [11])] do
      let r := C.cRun f ⟨a, b, a.length⟩ none
      IO.println s!"C-subset semantics (Lean) {nm}: {reprStr r}   refDot={IR.refDot a b} refL1={IR.refL1 a b} refL2={IR.refL2 a b} refHam={IR.refHam a b} refOsl={IR.refOsl a b}"
    pure 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["csem", c] => csem c
  | [mode, c, b] =>
    unless mode = "exact" ∨ mode = "match" do return (← usage)
    let v := gate (← IO.FS.readFile c) (← IO.FS.readFile b) (mode = "exact")
    IO.println s!"i8check gate={mode} c={c} bend={b}"
    match v with
    | .pass p => IO.println s!"IR (C lift = prog.bend term): {reprStr p}"; IO.println "VERDICT: PASS"; pure 0
    | .rejectC e => IO.println s!"REJECT: {e}"; IO.println "VERDICT: REJECT (C file outside the validated grammar)"; pure 2
    | .mismatch p q =>
      IO.println s!"C lifts to {reprStr p}; prog.bend is {reprStr q}{if mode = "exact" then "; exact gate requires posIR, l1IR, l2IR, hamIR or oslIR" else ""}"
      IO.println "VERDICT: IR MISMATCH"; pure 3
    | .uncertified p =>
      IO.println s!"C lift = prog.bend term = {reprStr p}, but this IR has no totality proof (certified: posIR, wrapIR, l1IR, l2IR, hamIR, oslIR only)"
      IO.println "VERDICT: UNCERTIFIED (matching but uncertified program)"; pure 5
    | .rejectBend e => IO.println s!"BEND REJECT: {e}"; IO.println "VERDICT: REJECT (prog.bend outside the generated grammar)"; pure 4
  | _ => usage
