import Subsp.old.stop_source_domain_split

/-! Support invariance above a lower coordinate replacement. -/

namespace new

theorem Vec.ext_idx {lam m : Nat} (v w : Vec (T lam) m)
    (h : ∀ i : Fin m, v.idx i = w.idx i) : v = w := by
  induction m with
  | zero => cases v; cases w; rfl
  | succ k ih =>
      cases v with
      | snoc _ vs vx =>
        cases w with
        | snoc _ ws wx =>
          have hlast : vx = wx := by
            simpa [Vec.idx] using h (Fin.last k)
          have hpref : vs = ws := ih vs ws (fun i => by
            simpa [Vec.idx, i.isLt] using h i.castSucc)
          cases hpref
          cases hlast
          rfl

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
      refine Or.inl ⟨i, hui, ?_⟩
      simpa only [Vec.rplc_idx_of_ne _ _ _ _ hij] using hi
    · cases ht

theorem T.PZ_le_rplc_zero {lam : Nat}
    (ls : Vec (T lam) lam) (j : Fin lam) (z : T lam)
    (hz : ls.idx j = T.Z) :
    T.P ls T.Z ≤ T.P (ls.rplc j z) T.Z := by
  cases z with
  | Z =>
      have he : ls.rplc j T.Z = ls := by
        apply Vec.ext_idx
        intro i
        by_cases hij : i.val = j.val
        · rw [Fin.eq_of_val_eq hij, Vec.rplc_idx_same, hz]
        · rw [Vec.rplc_idx_of_ne _ _ _ _ hij]
      rw [he]
      exact T.le_refl _
  | P v b =>
      apply Or.inl
      apply T.P_lt_P_of_compareVec_lt
      apply Vec.compare_lt_of_pivot _ _ j
      · intro i hji
        rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hji)]
      · rw [Vec.rplc_idx_same, hz]
        rfl

theorem T.isNFComp_rplc_lower {lam : Nat}
    (u : Nat) (ls : Vec (T lam) lam) (j : Fin lam) (z : T lam)
    (hju : j.val < u) (hz : ls.idx j = T.Z)
    (hbase : T.isNFComp u (T.P ls T.Z))
    (hnf : T.isNF (T.P (ls.rplc j z) T.Z)) :
    T.isNFComp u (T.P (ls.rplc j z) T.Z) := by
  refine ⟨hnf, ?_⟩
  intro x hx
  apply T.lt_of_lt_of_le _ _ _
    (hbase.2 x ((T.mem_Gi_PZ_rplc_lower_iff u ls j z x hju).mp hx))
  exact T.PZ_le_rplc_zero ls j z hz

end new
