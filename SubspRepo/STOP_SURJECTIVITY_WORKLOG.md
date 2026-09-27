# stop.lean / trans surjectivity worklog

Date: 2026-09-26

Local validation environment used during the exploration:
- Lean v4.34.0
- commit 293d5d0c0c3f3dded4688b3ccd6a33939ac5102b
- no mathlib

## Main result already on this branch

The first sorry in Subsp/new/stop.lean, new.T.OT_iff_NF, was filled constructively.
Its axiom audit reported only propext and Quot.sound.

The second original statement

    new.T.isOT lam s ↔ T.isSubNF lam (trans s)

is false as stated.  CounterStatement.lean records a lam = 2 counterexample:
the right hand side is true while the specific source term is not NF, hence not OT.

## Facts established during the follow-up

1. trans is injective on new.T.isNF.
   See TransInjectiveNF.lean.

2. Consequently trans is injective on OT.

3. The intended replacement appears to be a relation between the sets

    {s : new.T lam // new.T.isOT lam s}
    {t : T // T.isSubNF lam t}

   rather than a pointwise iff for an arbitrary preselected source s.

4. Surjectivity onto isSubNF was fully proved locally for lam = 0 and lam = 1.
   The original full scratch proof was in Surj1.lean.  Where exact transient bytes
   were recoverable they are preserved in the accompanying files; see the
   recovery notes for any one-off scratch files lost when the execution runtime
   was reset.

5. stop_surj_decode.lean developed the coefficient decoder infrastructure:
   T.unec, T.oneChain, T.uncard1 and their section/normal-form lemmas.
   The key section T.card_times 1 (T.uncard1 h) = h was kernel checked under
   the hypotheses used there.

6. stop_surj_general.lean developed the general P 0 reconstruction:
   a vector with only coordinate 0 nonzero, its transAux calculation,
   reconstruction of NF terms, and the strengthened NFComp reconstruction.

7. stop_surj_higher.lean contains the stable higher-coordinate skeleton.
   General lam >= 2 surjectivity is not yet finished.

## Decoder experiments

DecodeGen.lean and the Probe*.lean files are experimental.  They intentionally
use executable decidability tests such as decide.  They live only in SubspRepo
and must not be imported into the final Subsp library under the README rules.

A naive canonical decoder passed shallow tests but stronger/deeper checks found
counterexamples.  In particular the simple rule that concentrates all higher
information into coordinates 0 and 1 is not yet justified.

The earlier attempt to derive surjectivity solely from fundamental-sequence
commutation was also rejected: trans (fund s n) and fund1 (trans s) are not
equal in general.

## Important separation

Subsp/ contains candidate final library code and must satisfy README constraints.
SubspRepo/ contains scratch work, brute-force checks, counterexamples, backup
proofs, and partially developed constructions.  Files marked RECOVERY NOTE are
historical scratch filenames whose exact transient bytes were no longer
available after the execution environment reset; no source was fabricated for
them.

## Completed continuation (2026-09-27)

The local main library now proves all the declarations in `Subsp/new/stop.lean`
without proof placeholders, retaining the local replacement of the false
pointwise equivalence by `OT_imp_NF1`, `exists_OT_of_SubNF`, and
`trans_injective_OT`.

The general surjectivity proof is in `Subsp/new/stop_surj_*.lean`:

- `stop_surj_uncollapse` reconstructs a normal input with bounded support for
  `early_collapse`, including the case missed by the original simple decoder.
- `stop_surj_card` inverts `card_times 1` while preserving normal form, bounds,
  and exponent depth.
- `stop_surj_vector` and `stop_surj_principal` reconstruct all higher coordinates.
- `stop_surj_support` carries support bounds through reconstruction and proves
  that inputs with bounded support produce `isNFComp` terms.
- `stop_surj_general` inducts on exponent depth and then on the tail, completing
  reconstruction for every dimension at least two.
- `stop_surj_low` preserves the checked dimension-zero and dimension-one proofs.

Validation: Lean 4.34.0, `lake build Subsp.new.stop`. Axiom audits for the main
normal-form, order, surjectivity, injectivity, and well-foundedness theorems all
report only `propext` and `Quot.sound`. No experimental decoder is imported into
the main library.

## Proof cleanup (2026-09-27)

The `stop*.lean` proof modules were reduced from 11,236 to 9,297 lines.
Unused auxiliary declarations were removed using the elaborated proof dependency
graph, and duplicate lemmas now share one proof. The low-dimensional
surjectivity arguments use structural induction and reuse the same reconstructed
normal form. Well-foundedness uses `InvImage.wf` and `Subrelation.wf`.

The public normal-form, surjectivity, injectivity, well-foundedness, and order
isomorphism results remain available. `T.isSubNF` now uses `ot_trans_bound` for
its existing cutoff. `SubspRepo/StopAxiomAudit.lean` checks that this condition
agrees with the original definition and collects the main axiom audits, which
were removed from the library files.

## Consolidation by role (2026-09-27)

The 21 main proof files are now consolidated into six modules:
`stop_algebra`, `stop_nf_order`, `stop_ot`, `stop_inverse`,
`stop_surjectivity`, and the public entry point `stop`.
The README describes the role of each module. All 275 declaration names,
statements, and proof bodies were preserved. Imports of the removed modules
in working files now refer to their consolidated replacements; filenames in
earlier worklog entries describe the historical layout.

## Second proof cleanup (2026-09-27)

The six consolidated modules were reduced from 9,417 to 8,797 lines.
Ten size-based inductions were replaced by structural induction. The three
remaining measure inductions are used for support descent, the simultaneous
normal-form/order argument, and exponent-depth reconstruction.

Bounded and unbounded order preservation now share one proof. The finite-term
and LF normal-form proofs share a constructor lemma, repeated vector comparisons
share one inversion lemma, and the Omega-domain exclusion uses the coordinate
bound directly. The inverse construction shares its fixed-part decomposition.
The duplicate `cb_P0_mid_le`, one unused intermediate proof, and unused hypotheses
of `ec_good0_mono` and `cb_shift_le_of_le` were removed. Unused local binding names
were replaced by anonymous bindings.

The public theorem statements, including `OT_SubNF_order_iso`, are unchanged.
Validation: `lake build Subsp.new.stop`, the 15 public axiom audits in
`SubspRepo/StopAxiomAudit.lean`, and tactic-aware unused-variable linting of all
six modules pass. The elaborated dependency graph has no unreachable auxiliary
declarations relative to the public results and main-library uses. The source
review found no README-prohibited tactics, unproved declarations, or new axioms.

## Structural consolidation (2026-09-27)

A further review found semantic duplication that the unused-declaration check
did not detect. After removing its unused hypothesis, `ec_good0_mono` had the
same assumptions as `bridge_early_collapse_lt`, in a different order. Its call
now uses the latter theorem; the duplicate and its four dedicated helper
theorems were removed.

The three wrapping lemmas `cs_self_lt_wrap`, `StopUncollapse.good_index0_lt`, and
`StopSurjCard.index1_good_lt_wrap` were replaced by `bridge_good_index_lt_wrap`.
This works for every natural-number index and does not require normal form.
Its proof has no axiom dependencies. Checked instances are recorded in
`SubspRepo/StopImprovementAudit.lean`.

These changes reduce the six modules from 8,797 to 8,558 lines. The retained
declarations' signatures are unchanged, including all public order-isomorphism
results. The library build and the 15 public axiom audits pass.
