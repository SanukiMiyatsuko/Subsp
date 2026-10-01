import Subsp.old.stop_source_domain_split

/-! Support invariance above a lower coordinate replacement. -/

namespace new

theorem T.mem_Gi_PZ_rplc_lower_iff {lam : Nat}
    (u : Nat) (ls : Vec (T lam) lam) (j : Fin lam) (z x : T lam)
    (hju : j.val < u) :
    x ∈ T.Gi u (T.P (ls.rplc j z) T.Z) ↔
      x ∈ T.Gi u (T.P ls T.Z) := by
  rw [T.mem_Gi_P, T.mem_Gi_P]
  constructor
  · rintro (⟨i, hui, hi⟩ | ht)
    · have hij : i.val ≠ j.val := by omega
      rw [Vec.rplc_idx_of_ne _ _ _ _ hij] at hi
      exact Or.inl ⟨i, hui, hi⟩
    · cases ht
  · rintro (⟨i, hui, hi⟩ | ht)
    · have hij : i.val ≠ j.val := by omega
      rw [Vec.rplc_idx_of_ne _ _ _ _ hij]
      exact Or.inl ⟨i, hui, hi⟩
    · cases ht

theorem T.isNFComp_rplc_lower {lam : Nat}
    (u : Nat) (ls : Vec (T lam) lam) (j : Fin lam) (z : T lam)
    (hju : j.val < u)
    (hbase : T.isNFComp u (T.P ls T.Z))
    (hnf : T.isNF (T.P (ls.rplc j z) T.Z)) :
    T.isNFComp u (T.P (ls.rplc j z) T.Z) := by
  refine ⟨hnf, ?_⟩
  intro x hx
  exact hbase.2 x ((T.mem_Gi_PZ_rplc_lower_iff u ls j z x hju).mp hx)

end new
