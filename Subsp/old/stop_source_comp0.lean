import Subsp.old.stop_source_master_helpers

/-! Level-zero support helpers for the indexed legacy source syntax. -/

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

end new
