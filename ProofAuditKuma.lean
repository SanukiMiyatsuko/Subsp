import Lean
import Subsp.multi.kuma.stop

/-! Audit every definition and theorem of the `multi` kumakuma proofs (`Subsp/multi/kuma`),
including generated proofs, together with the constructive Jäger theory they use.
Run `lake build Subsp.multi.kuma.stop`, then `lake env lean ProofAuditKuma.lean`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.toList.filterMap fun (name, info) => do
    let idx ← env.getModuleIdxFor? name
    let m := env.header.moduleNames[idx.toNat]!
    if ((`Subsp.multi.kuma).isPrefixOf m || (`Subsp.OCF.Jaeger.Constructive).isPrefixOf m) &&
        (info.isTheorem || info.isDefinition) then some name else none
  for name in names.mergeSort Name.quickLt do
    let axioms ← collectAxioms name
    unless axioms.all (fun ax => ax == ``propext || ax == ``Quot.sound) do
      logError m!"Unexpected axioms in {name}: {axioms}"
  logInfo m!"Audited {names.length} declarations of Subsp.multi.kuma and Subsp.OCF.Jaeger.Constructive."

#print axioms kumakuma.NOT_order_embedding
#print axioms kumakuma.NOT_lt_wellFounded
#print axioms kumakuma.NOTFundLt_iff_lt
#print axioms kumakuma.NOTFundLt_wellFounded
