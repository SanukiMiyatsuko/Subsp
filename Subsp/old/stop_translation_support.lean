import Subsp.old.stop_nf_core
import Subsp.old.stop_source_fund_nf

/-! Basic support embeddings used by the legacy translation support proof. -/

namespace LegacyTranslation

theorem source_vec_idx_mem_Gi {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (i : Fin k) (hui : u ≤ i.val) :
    v.idx i ∈ new.Vec.Gi u v := by
  exact (new.Vec.mem_Gi_iff u v (v.idx i)).2
    ⟨i, hui, Or.inl rfl⟩

theorem source_coord_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (i : Fin lam) (hui : u ≤ i.val) :
    v.idx i ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a (v.idx i)).2
    (Or.inl ⟨i, hui, Or.inl rfl⟩)

theorem source_coord_support_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (i : Fin lam) (hui : u ≤ i.val)
    (hz : z ∈ new.T.Gi u (v.idx i)) :
    z ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a z).2
    (Or.inl ⟨i, hui, Or.inr hz⟩)

theorem source_tail_support_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.T.Gi u a) :
    z ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a z).2 (Or.inr hz)

theorem trans_tail_le {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (h : T.isNF1 (trans (new.T.P v a))) :
    trans a ≤ trans (new.T.P v a) := by
  rw [trans_as_add]
  exact add_right_le_of_NF _ _ h

theorem trans_head_support_mem {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam) (x : T)
    (hx : x ∈ T.G1 u (transAux v).1) :
    x ∈ T.G1 u (trans (new.T.P v a)) := by
  rw [trans_as_add, G1_add]
  exact List.mem_append_left _ hx

theorem trans_tail_support_mem {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam) (x : T)
    (hx : x ∈ T.G1 u (trans a)) :
    x ∈ T.G1 u (trans (new.T.P v a)) := by
  rw [trans_as_add, G1_add]
  exact List.mem_append_right _ hx

end LegacyTranslation
