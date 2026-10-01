import Subsp.old.stop_source_interpolation

/-! Lift indexed support interpolation through the pivot of a principal term. -/

namespace new

theorem T.IDom_rplc_min {lam : Nat}
    (u : Nat) (z : T lam) (ls : Vec (T lam) lam)
    (m : Fin lam) (d : Dom lam) (b : T lam)
    (hmin : T.domVecMinIdx ls = some (m, d))
    (hblt : b < ls.idx m)
    (hinner : u ≤ m.val → T.IDom u z b (ls.idx m)) :
    T.IDom u z (T.P (ls.rplc m b) T.Z) (T.P ls T.Z) := by
  have hcmp : compareVec (ls.rplc m b) ls = Ordering.lt :=
    Vec.compare_rplc_lt ls m b hblt
  refine ⟨T.P_lt_P_of_compareVec_lt _ _ _ _ hcmp, ?_⟩
  intro c hlc hch x hx
  cases c with
  | Z => rcases hlc with h | h <;> cases h
  | P mid add =>
      have hbetween := Vec.interval_pivot_properties (ls.rplc m b) mid ls m
        (fun j hj => Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj))
        (by simpa only [Vec.rplc_idx_same] using hblt)
        (T.vector_rel_of_P_le_P _ _ _ _ hlc)
        (T.vector_rel_of_P_le_P _ _ _ _ hch)
      rcases (T.mem_Gi_P u (ls.rplc m b) T.Z x).mp hx with ⟨q, huq, hq⟩ | ht
      · rcases Nat.lt_trichotomy q.val m.val with hqm | hqm | hmq
        · have hz : ls.idx q = T.Z :=
            T.dom_zero_eq_Z _ ((T.domVecMinIdx_some_spec ls m d hmin).2.2 q hqm)
          have hlow : (ls.rplc m b).idx q = T.Z := by
            rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hqm), hz]
          rw [hlow] at hq
          rcases hq with rfl | hq
          · refine Or.inr ⟨T.Z, List.mem_append_right _ ?_, T.le_refl _⟩
            simp [T.GZ]
          · cases hq
        · obtain rfl := Fin.eq_of_val_eq hqm
          rw [Vec.rplc_idx_same] at hq
          rcases hq with rfl | hx
          · refine Or.inr ⟨mid.idx q,
              List.mem_append_left _
                ((T.mem_Gi_P u mid add _).mpr
                  (Or.inl ⟨q, huq, Or.inl rfl⟩)), ?_⟩
            simpa only [Vec.rplc_idx_same] using hbetween.2.1
          · have hbmid : b ≤ mid.idx q := by
              simpa only [Vec.rplc_idx_same] using hbetween.2.1
            rcases (hinner huq).2 (mid.idx q) hbmid hbetween.2.2 x hx with
              hxb | ⟨y, hy, hxy⟩
            · exact Or.inr ⟨mid.idx q, List.mem_append_left _
                ((T.mem_Gi_P u mid add _).mpr (Or.inl ⟨q, huq, Or.inl rfl⟩)),
                Or.inl (T.lt_of_lt_of_le _ _ _ hxb hbmid)⟩
            · refine Or.inr ⟨y, ?_, hxy⟩
              rcases List.mem_append.mp hy with hy | hy
              · exact List.mem_append_left _
                  ((T.mem_Gi_P u mid add y).mpr
                    (Or.inl ⟨q, huq, Or.inr hy⟩))
              · exact List.mem_append_right _ hy
        · have heq : (ls.rplc m b).idx q = mid.idx q := by
            exact (Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hmq)).trans
              (hbetween.1 q hmq).symm
          rw [heq] at hq
          refine Or.inr ⟨x, List.mem_append_left _
            ((T.mem_Gi_P u mid add x).mpr (Or.inl ⟨q, huq, hq⟩)), T.le_refl _⟩
      · cases ht

end new
