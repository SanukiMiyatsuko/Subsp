import Subsp.new.stop

-- Run with: lake env lean SubspRepo/StopAxiomAudit.lean
-- Every declaration below may depend only on propext and Quot.sound.
#print axioms NF_is_NF1
#print axioms order_embeding
#print axioms trans_injective_on_NF
#print axioms wellfounded_NF
#print axioms new.T.OT_iff_NF
#print axioms wellfounded_OT
#print axioms OT_imp_NF1
#print axioms exists_OT_of_SubNF
#print axioms trans_injective_OT
#print axioms trans_OT
#print axioms trans_OT_injective
#print axioms trans_OT_surjective
#print axioms trans_OT_lt_iff
#print axioms trans_OT_le_iff
#print axioms OT_SubNF_order_iso

-- Factoring out ot_trans_bound preserves the original SubNF condition.
example (n : Nat) (s : T) :
    T.isSubNF n s ↔ T.isNF1 s ∧
      match n with
      | 0 => s < T.P 0 (T.P 0 T.Z T.Z) T.Z
      | 1 => s < T.P 0 (T.P 1 T.Z T.Z) T.Z
      | k + 2 => s < T.P 0
          (T.P 1 (T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) T.Z) T.Z) T.Z := by
  cases n with
  | zero => rfl
  | succ k =>
      cases k with
      | zero => rfl
      | succ k => rfl
