# Recovered ephemeral scratch-file inventory

These scratch filenames were observed in the local Lean 4.34.0 worktree during
the 2026-09-26 surjectivity investigation, but their exact transient bytes were
lost when the execution runtime reset before the requested branch snapshot.

A same-name Lean recovery-note file is committed for each entry.  No source has
been guessed or fabricated.

- BoundsCalc.lean
- BruteFundIneqAll.lean
- BruteRestricted.lean
- CheckPre3.lean
- DecoderTest.lean
- FindEcPre3d3.lean
- FindEcPre3.lean
- FindPre3.lean
- SearchSpecificPre.lean
- TestUncardProp.lean
- TestUncard.lean
- UncardProof.lean

Their durable mathematical content is represented by the worklog and the
reconstructed/validated files stop_surj_decode.lean, stop_surj_general.lean,
stop_surj_higher.lean, Surj1.lean, DecodeGen.lean, CounterStatement.lean, and
TransInjectiveNF.lean.
