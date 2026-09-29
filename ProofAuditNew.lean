import Lean
import Subsp
import Subsp.new.stop

/-! Audit every definition and theorem in the project, including generated proofs.
Run `lake build Subsp Subsp.old.stop`, then `lake env lean ProofAuditOld.lean`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) => do
    let idx ← env.getModuleIdxFor? name
    if (`Subsp).isPrefixOf env.header.moduleNames[idx.toNat]! &&
        (info.isTheorem || info.isDefinition) then some name else none
  for name in names.mergeSort Name.quickLt do
    elabCommand (← `(command| #print axioms $(mkIdent name)))
    let axioms ← collectAxioms name
    unless axioms.all (fun ax => ax == ``propext || ax == ``Quot.sound) do
      logError m!"Unexpected axioms in {name}: {axioms}"
  logInfo m!"Audited {names.length} project declarations."
