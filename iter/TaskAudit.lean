import Lean
import TaskCore
import Iter
/-! Axiom audit for every theorem declared in Iter and TaskCore: prints each name with its axioms and
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
      if (mod.toString.startsWith "TaskCore" || mod.toString.startsWith "Iter") && (match ci with | .thmInfo _ => true | _ => false) && !nm.isInternal && !(match nm with | .str _ s => s.startsWith "eq_" || s == "induct" | _ => false) then
        n := n + 1
        let axs ← liftCoreM (collectAxioms nm)
        names := names.push s!"AUDIT {nm} {mod} {axs.toList}"
        if !axs.all (ok.contains ·) then bad := bad + 1
  for s in names.qsort (· < ·) do IO.println s
  IO.println s!"Iter + TaskCore theorems audited: {n}, with nonstandard axioms: {bad}"
  if bad != 0 then throwError "nonstandard axioms"
