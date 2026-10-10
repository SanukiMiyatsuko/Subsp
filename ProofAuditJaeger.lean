import Lean
import Subsp.OCF.Jaeger.Constructive.WellOrder

/-! Audit every definition and theorem of the constructive well-ordering proof for Jäger's
notation system (`Subsp/OCF/Jaeger/Constructive`), including generated proofs.
Run `lake build Subsp.OCF.Jaeger.Constructive.WellOrder`, then
`lake env lean ProofAuditJaeger.lean`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) => do
    let idx ← env.getModuleIdxFor? name
    if (`Subsp.OCF.Jaeger.Constructive).isPrefixOf env.header.moduleNames[idx.toNat]! &&
        (info.isTheorem || info.isDefinition) then some name else none
  for name in names.mergeSort Name.quickLt do
    let axioms ← collectAxioms name
    unless axioms.all (fun ax => ax == ``propext || ax == ``Quot.sound) do
      logError m!"Unexpected axioms in {name}: {axioms}"
  logInfo m!"Audited {names.length} declarations of Subsp.OCF.Jaeger.Constructive."

#print axioms OCF.Jaeger.Term.lt_wellFounded
#print axioms OCF.Jaeger.Term.lt_isWellOrder
