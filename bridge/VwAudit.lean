import Lean
import Vw
/-! Axiom audit for every theorem declared in a `Vw.*` module: prints each name with its axioms and
fails (error) if any depends on something other than propext / Classical.choice / Quot.sound. -/
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n := 0
  let mut bad := 0
  let mut names : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? nm then
      let mod := env.header.moduleNames[idx.toNat]!
      if (mod.toString.startsWith "Vw") && (match ci with | .thmInfo _ => true | _ => false) && !nm.isInternal then
        n := n + 1
        let axs ← liftCoreM (collectAxioms nm)
        names := names.push s!"AUDIT {nm} {mod} {axs.toList}"
        if !axs.all (ok.contains ·) then bad := bad + 1
  for s in names.qsort (· < ·) do IO.println s
  IO.println s!"Vw theorems audited: {n}, with nonstandard axioms: {bad}"
  if bad != 0 then throwError "nonstandard axioms"
