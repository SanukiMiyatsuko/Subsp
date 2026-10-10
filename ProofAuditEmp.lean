import Lean
import Subsp
import Subsp.multi.emp.stop

/-! Audit every definition and theorem used by the `multi` emp system, including generated
proofs: everything must depend only on `propext` and `Quot.sound`.
Run `lake build Subsp.multi.emp.stop`, then `lake env lean ProofAuditEmp.lean`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) => do
    let idx ← env.getModuleIdxFor? name
    if (`Subsp).isPrefixOf env.header.moduleNames[idx.toNat]! &&
        (info.isTheorem || info.isDefinition) then some name else none
  for name in names.mergeSort Name.quickLt do
    let axioms ← collectAxioms name
    unless axioms.all (fun ax => ax == ``propext || ax == ``Quot.sound) do
      logError m!"Unexpected axioms in {name}: {axioms}"
  logInfo m!"Audited {names.length} project declarations."

#print axioms NOT_SubNF_order_iso
#print axioms emp.NOTFundLt_iff_lt
