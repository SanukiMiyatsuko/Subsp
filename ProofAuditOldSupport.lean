import Lean
import Subsp
import Subsp.old.stop_low_dims
import Subsp.old.stop_collapse
import Subsp.old.stop_nf_core
import Subsp.old.stop_source_successor

/-! Audit the completed legacy support lemmas independently of the open theorem.
Run `lake build Subsp.old.stop_low_dims Subsp.old.stop_nf_core Subsp.old.stop_source_successor`, then
`lake env lean ProofAuditOldSupport.lean`.
`ProofAuditOld.lean` remains the complete audit, including `OT_SubNF_order_iso`.
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
