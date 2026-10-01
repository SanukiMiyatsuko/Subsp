import Subsp.old.stop_source_mul

/-! Interval and support lifting lemmas for indexed source vectors. -/

namespace new

theorem T.vector_rel_of_P_le_P {lam : Nat}
    (v w : Vec (T lam) lam) (a b : T lam)
    (h : T.P v a ≤ T.P w b) :
    compareVec v w = Ordering.lt ∨ v = w := by
  rcases h with h | h
  · change (match compareVec v w with
      | .eq => compareT a b | ord => ord) = .lt at h
    cases hc : compareVec v w with
    | lt => exact Or.inl rfl
    | eq => exact Or.inr (Vec_eq_sound _ _ hc)
    | gt => simp [hc] at h
  · cases T_eq_sound _ _ h
    exact Or.inr rfl

theorem Vec.interval_pivot_properties {lam m : Nat}
    (low mid high : Vec (T lam) m) (i : Fin m)
    (heqAbove : ∀ j : Fin m, i.val < j.val →
      low.idx j = high.idx j)
    (hpivot : low.idx i < high.idx i)
    (hlm : compareVec low mid = Ordering.lt ∨ low = mid)
    (hmh : compareVec mid high = Ordering.lt ∨ mid = high) :
    (∀ j : Fin m, i.val < j.val →
        mid.idx j = high.idx j) ∧
      low.idx i ≤ mid.idx i ∧
      mid.idx i ≤ high.idx i := by
  rcases hlm with hlt | rfl
  · obtain ⟨p, hpEq, hpLt⟩ := Vec.compare_lt_has_pivot low mid hlt
    have hpi : p.val ≤ i.val := by
      apply Nat.le_of_not_gt
      intro hip
      rcases hmh with h | rfl
      · obtain ⟨q, hqEq, hqLt⟩ := Vec.compare_lt_has_pivot mid high h
        rcases Nat.lt_trichotomy q.val p.val with hqp | heq | hpq
        · rw [hqEq p hqp, ← heqAbove p hip] at hpLt
          exact strict_partial_order.irrefl _ hpLt
        · obtain rfl := Fin.eq_of_val_eq heq
          have hc := T_trans _ _ _ hpLt hqLt
          rw [← heqAbove q hip] at hc
          simp only [T_refl] at hc
          cases hc
        · rw [← hpEq q hpq, heqAbove q (by omega)] at hqLt
          exact strict_partial_order.irrefl _ hqLt
      · rw [← heqAbove p hip] at hpLt
        exact strict_partial_order.irrefl _ hpLt
    have hhigh (j : Fin m) (hj : i.val < j.val) :
        mid.idx j = high.idx j :=
      (hpEq j (by omega)).symm.trans (heqAbove j hj)
    refine ⟨hhigh, ?_, ?_⟩
    · rcases Nat.lt_or_eq_of_le hpi with h | h
      · rw [hpEq i h]
        exact T.le_refl _
      · rw [Fin.eq_of_val_eq h] at hpLt
        exact Or.inl hpLt
    · rcases hmh with h | rfl
      · obtain ⟨q, hqEq, hqLt⟩ := Vec.compare_lt_has_pivot mid high h
        have hqi : q.val ≤ i.val := by
          apply Nat.le_of_not_gt
          intro hiq
          rw [hhigh q hiq] at hqLt
          exact strict_partial_order.irrefl _ hqLt
        rcases Nat.lt_or_eq_of_le hqi with h | h
        · rw [hqEq i h]
          exact T.le_refl _
        · rw [Fin.eq_of_val_eq h] at hqLt
          exact Or.inl hqLt
      · exact T.le_refl _
  · exact ⟨heqAbove, T.le_refl _, Or.inl hpivot⟩

theorem T.SDom_rplc_min {lam : Nat}
    (z : T lam) (ls : Vec (T lam) lam)
    (m : Fin lam) (d : Dom lam) (b : T lam)
    (hmin : T.domVecMinIdx ls = some (m, d))
    (hinner : T.SDom z b (ls.idx m)) :
    T.SDom z (T.P (ls.rplc m b) T.Z) (T.P ls T.Z) := by
  have hcmp : compareVec (ls.rplc m b) ls = Ordering.lt :=
    Vec.compare_rplc_lt ls m b hinner.1
  refine ⟨T.P_lt_P_of_compareVec_lt _ _ _ _ hcmp, ?_⟩
  intro u c hlc hch x hx
  cases c with
  | Z => rcases hlc with h | h <;> cases h
  | P mid add =>
      have hbetween := Vec.interval_pivot_properties (ls.rplc m b) mid ls m
        (fun j hj => Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj))
        (by simpa only [Vec.rplc_idx_same] using hinner.1)
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
          · refine ⟨T.Z, List.mem_append_right _ ?_, T.le_refl _⟩
            simp [T.GZ]
          · cases hq
        · obtain rfl := Fin.eq_of_val_eq hqm
          rw [Vec.rplc_idx_same] at hq
          rcases hq with rfl | hx
          · refine ⟨mid.idx q,
              List.mem_append_left _
                ((T.mem_Gi_P u mid add _).mpr
                  (Or.inl ⟨q, huq, Or.inl rfl⟩)), ?_⟩
            simpa only [Vec.rplc_idx_same] using hbetween.2.1
          · obtain ⟨y, hy, hxy⟩ :=
              hinner.2 u (mid.idx q)
                (by simpa only [Vec.rplc_idx_same] using hbetween.2.1)
                hbetween.2.2 x hx
            refine ⟨y, ?_, hxy⟩
            rcases List.mem_append.mp hy with hy | hy
            · exact List.mem_append_left _
                ((T.mem_Gi_P u mid add y).mpr
                  (Or.inl ⟨q, huq, Or.inr hy⟩))
            · exact List.mem_append_right _ hy
        · have heq : (ls.rplc m b).idx q = mid.idx q := by
            exact (Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hmq)).trans
              (hbetween.1 q hmq).symm
          rw [heq] at hq
          refine ⟨x, List.mem_append_left _
            ((T.mem_Gi_P u mid add x).mpr (Or.inl ⟨q, huq, hq⟩)), T.le_refl _⟩
      · cases ht

end new
