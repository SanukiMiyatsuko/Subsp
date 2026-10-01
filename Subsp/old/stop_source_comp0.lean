import Subsp.old.stop_source_master_helpers

/-! Level-zero component closure under the least-coordinate replacement. -/

namespace new

theorem Vec.compare_lt_after_pivot_update {lam m : Nat}
    (a old newv : Vec (T lam) m) (i : Fin m)
    (heqAbove : ∀ j : Fin m, i.val < j.val →
      old.idx j = newv.idx j)
    (hold : compareVec a old = Ordering.lt)
    (hpivot : a.idx i < newv.idx i) :
    compareVec a newv = Ordering.lt := by
  obtain ⟨q, hAbove, hLt⟩ := Vec.compare_lt_has_pivot a old hold
  by_cases hqi : q.val ≤ i.val
  · apply Vec.compare_lt_of_pivot a newv i
    · intro j hij
      exact (hAbove j (by omega)).trans (heqAbove j hij)
    · exact hpivot
  · apply Vec.compare_lt_of_pivot a newv q
    · intro j hqj
      exact (hAbove j hqj).trans (heqAbove j (by omega))
    · rw [← heqAbove q (by omega)]
      exact hLt

theorem T.coord_lt_of_NFComp0_P {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNFComp 0 (T.P ls add)) :
    ∀ i : Fin lam, ls.idx i < T.P ls add := by
  intro i
  exact hs.2 _ ((T.mem_Gi_P 0 ls add _).mpr
    (Or.inl ⟨i, Nat.zero_le _, Or.inl rfl⟩))

theorem T.term_lt_P_of_self_at0 {lam : Nat}
    (x : T lam) (v w : Vec (T lam) lam)
    (q : Fin lam)
    (hx : T.isNFComp 0 x)
    (hold : x < T.P v T.Z)
    (hwq : w.idx q = x)
    (hhigh : ∀ j : Fin lam, q.val < j.val →
      w.idx j = v.idx j) :
    x < T.P w T.Z := by
  cases x with
  | Z => rfl
  | P xs xadd =>
      have hvlt : compareVec xs v = .lt := by
        change (match compareVec xs v with
          | .eq => compareT xadd T.Z | ord => ord) = .lt at hold
        cases hc : compareVec xs v with
        | lt => rfl
        | eq =>
            rw [hc] at hold
            cases xadd <;> cases hold
        | gt => simp [hc] at hold
      apply T.P_lt_P_of_compareVec_lt
      apply Vec.compare_lt_after_pivot_update xs v w q
        (fun j hj => (hhigh j hj).symm) hvlt
      rw [hwq]
      exact T.coord_lt_of_NFComp0_P xs xadd hx q

theorem T.PZ_isNF_of_comp0_coords {lam : Nat}
    (ls : Vec (T lam) lam)
    (h : ∀ i : Fin lam, T.isNFComp 0 (ls.idx i)) :
    T.isNF (T.P ls T.Z) := by
  refine T.isNF.p ls T.Z (fun i => (h i).1) T.isNF.z ?_ (T.Z_le _)
  intro i x hx
  exact (h i).2 x (T.Gi_antitone 0 i.val (Nat.zero_le _) _ x hx)

theorem T.rplc_min_NFComp0_closed {lam : Nat}
    (ls : Vec (T lam) lam) (m : Fin lam)
    (d : Dom lam) (a : T lam)
    (hs : T.isNFComp 0 (T.P ls T.Z))
    (hmin : T.domVecMinIdx ls = some (m, d))
    (ha : T.isNFComp 0 a)
    (halt : a < ls.idx m) :
    T.isNFComp 0 (T.P (ls.rplc m a) T.Z) := by
  have hspec := T.domVecMinIdx_some_spec ls m d hmin
  have holdCoord (i : Fin lam) : T.isNFComp 0 (ls.idx i) := by
    refine ⟨(T.isNF_P_inv ls T.Z hs.1).1 i |>.1, ?_⟩
    intro x hx
    exact hs.2 x ((T.mem_Gi_P 0 ls T.Z x).mpr
      (Or.inl ⟨i, Nat.zero_le _, Or.inr hx⟩))
  have hcoord (i : Fin lam) :
      T.isNFComp 0 ((ls.rplc m a).idx i) := by
    by_cases hi : i.val = m.val
    · rw [Fin.eq_of_val_eq hi, Vec.rplc_idx_same]
      exact ha
    · rw [Vec.rplc_idx_of_ne _ _ _ _ hi]
      exact holdCoord i
  have hilt (i : Fin lam) :
      (ls.rplc m a).idx i < T.P (ls.rplc m a) T.Z := by
    by_cases hi : i.val < m.val
    · rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hi),
        T.dom_zero_eq_Z _ (hspec.2.2 i hi)]
      rfl
    · refine T.term_lt_P_of_self_at0 _ ls _ i (hcoord i) ?_ rfl ?_
      · by_cases him : i.val = m.val
        · rw [Fin.eq_of_val_eq him, Vec.rplc_idx_same]
          exact strict_partial_order.trans _ _ _ halt
            (T.coord_lt_of_NFComp0_P ls T.Z hs m)
        · rw [Vec.rplc_idx_of_ne _ _ _ _ him]
          exact T.coord_lt_of_NFComp0_P ls T.Z hs i
      · intro j hj
        exact Vec.rplc_idx_of_ne _ _ _ _ (by omega)
  refine ⟨T.PZ_isNF_of_comp0_coords _ hcoord, ?_⟩
  intro y hy
  rcases (T.mem_Gi_P 0 (ls.rplc m a) T.Z y).mp hy with
      ⟨i, _, rfl | hyg⟩ | hz
  · exact hilt i
  · exact strict_partial_order.trans _ _ _ ((hcoord i).2 y hyg) (hilt i)
  · cases hz

end new
