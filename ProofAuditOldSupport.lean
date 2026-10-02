import Lean
import Subsp
import Subsp.old.stop_ot_comp0
import Subsp.old.stop_trans_algebra
import Subsp.old.stop_translation_dim
import Subsp.old.stop_target_image

/-! Audit every completed legacy theorem independently of the open theorem.
Run `lake build Subsp.old.stop_ot_comp0 Subsp.old.stop_trans_algebra Subsp.old.stop_translation_dim`, then
`lake env lean ProofAuditOldSupport.lean`.
`ProofAuditOld.lean` additionally imports `Subsp.old.stop`, including `OT_SubNF_order_iso`.
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
