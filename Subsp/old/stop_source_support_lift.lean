import Subsp.old.stop_source_dom
import Subsp.old.stop_source_interval

/-! Support-domain lifting through the remaining legacy source constructors. -/

namespace new

theorem T.mul_PZ_lt_of_compareVec_lt {lam : Nat}
    (u v : Vec (T lam) lam) (t : T lam)
    (hvec : compareVec u v = Ordering.lt) :
    T.mul (T.P u T.Z) t < T.P v T.Z := by
  cases t with
  | Z => exact .Z_lt_P _ _ _
  | P ts add =>
      rw [T.mul]
      exact T.P_lt_P_of_compareVec_lt _ _ _ _ hvec

theorem T.SDom_mul_PZ {lam : Nat}
    (u v : Vec (T lam) lam) (t : T lam)
    (hvec : compareVec u v = Ordering.lt)
    (hbase : T.SDom T.Z (T.P u T.Z) (T.P v T.Z)) :
    T.SDom T.Z (T.mul (T.P u T.Z) t) (T.P v T.Z) := by
  refine ⟨T.mul_PZ_lt_of_compareVec_lt u v t hvec, ?_⟩
  intro level c hmc hcv x hx
  cases t with
  | Z => cases hx
  | P ts add =>
      apply hbase.2 level c
        (T.le_trans _ _ _
          (T.P_le_P_same u T.Z _
            (T.Z_le (T.mul (T.P u T.Z) add))) hmc)
        hcv x
      exact T.Gi_mul_PZ_subset level u (T.P ts add) x hx

theorem T.SDom_rplc_lower {lam : Nat}
    (z : T lam) (ls : Vec (T lam) lam)
    (m j : Fin lam) (d : Dom lam) (b : T lam)
    (hjm : j.val < m.val)
    (hmin : T.domVecMinIdx ls = some (m, d))
    (hinner : T.SDom T.Z b (ls.idx m)) :
    T.SDom z
      (T.P ((ls.rplc m b).rplc j z) T.Z)
      (T.P ls T.Z) := by
  let low := (ls.rplc m b).rplc j z
  have hlowm : low.idx m = b := by
    dsimp [low]
    rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega), Vec.rplc_idx_same]
  have hcmp : compareVec low ls = Ordering.lt := by
    apply Vec.compare_lt_of_pivot _ _ m
    · intro q hmq
      dsimp [low]
      rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega),
        Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hmq)]
    · rw [hlowm]
      exact hinner.1
  refine ⟨T.P_lt_P_of_compareVec_lt _ _ _ _ hcmp, ?_⟩
  intro level c hlc hch x hx
  cases c with
  | Z => rcases hlc with h | h <;> cases h
  | P mid add =>
      have hbetween := Vec.interval_pivot_properties low mid ls m
        (fun q hmq => by
          dsimp [low]
          rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega),
            Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hmq)])
        (by rw [hlowm]; exact hinner.1)
        (T.vector_rel_of_P_le_P _ _ _ _ hlc)
        (T.vector_rel_of_P_le_P _ _ _ _ hch)
      rcases (T.mem_Gi_P level low T.Z x).mp hx with ⟨q, hlq, hq⟩ | ht
      · rcases Nat.lt_trichotomy q.val m.val with hqm | hqm | hmq
        · by_cases hqj : q.val = j.val
          · obtain rfl := Fin.eq_of_val_eq hqj
            have hlowj : low.idx j = z := by
              dsimp [low]
              rw [Vec.rplc_idx_same]
            rw [hlowj] at hq
            refine ⟨x, List.mem_append_right _ ?_, T.le_refl _⟩
            rcases hq with rfl | hq
            · simp [T.GZ]
            · simp [T.GZ, hq]
          · have hz : ls.idx q = T.Z :=
              T.dom_zero_eq_Z _ ((T.domVecMinIdx_some_spec ls m d hmin).2.2 q hqm)
            have hlowq : low.idx q = T.Z := by
              dsimp [low]
              rw [Vec.rplc_idx_of_ne _ _ _ _ hqj,
                Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hqm), hz]
            rw [hlowq] at hq
            rcases hq with rfl | hq
            · refine ⟨T.Z, List.mem_append_right _ ?_, T.le_refl _⟩
              simp [T.GZ]
            · cases hq
        · obtain rfl := Fin.eq_of_val_eq hqm
          rw [hlowm] at hq
          rcases hq with rfl | hx
          · refine ⟨mid.idx q,
              List.mem_append_left _
                ((T.mem_Gi_P level mid add _).mpr
                  (Or.inl ⟨q, hlq, Or.inl rfl⟩)), ?_⟩
            exact hbetween.2.1
          · obtain ⟨y, hy, hxy⟩ :=
              hinner.2 level (mid.idx q) hbetween.2.1 hbetween.2.2 y hx
            refine ⟨y, ?_, hxy⟩
            rcases List.mem_append.mp hy with hy | hy
            · exact List.mem_append_left _
                ((T.mem_Gi_P level mid add y).mpr
                  (Or.inl ⟨q, hlq, Or.inr hy⟩))
            · have hyz : y = T.Z := by
                simpa [T.GZ] using hy
              subst y
              exact List.mem_append_right _ (by simp [T.GZ])
        · have heq : low.idx q = mid.idx q := by
            dsimp [low]
            rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega),
              Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hmq)]
            exact (hbetween.1 q hmq).symm
          rw [heq] at hq
          refine ⟨x, List.mem_append_left _
            ((T.mem_Gi_P level mid add x).mpr
              (Or.inl ⟨q, hlq, hq⟩)), T.le_refl _⟩
      · cases ht

end new
