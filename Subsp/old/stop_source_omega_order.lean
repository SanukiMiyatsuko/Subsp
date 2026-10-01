import Subsp.old.stop_source_dom
import Subsp.old.stop_source_interval

/-! Order lemmas for indexed uncountable source fundamental sequences. -/

namespace new

theorem Vec.compare_rplc_same_index_lt {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) (a b : T lam)
    (h : a < b) :
    compareVec (v.rplc i a) (v.rplc i b) = Ordering.lt := by
  apply Vec.compare_lt_of_pivot _ _ i
  · intro j hj
    rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj),
      Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj)]
  · simpa only [Vec.rplc_idx_same] using h

theorem T.fund_Omega_ne_Z_indexed {lam : Nat}
    (s t : T lam) (i : Fin lam)
    (hd : T.dom s = .Omega i) :
    T.fund s t ≠ T.Z := by
  cases s with
  | Z => cases hd
  | P ls add =>
      by_cases hadd : add = T.Z
      · subst add
        cases hmin : T.domVecMinIdx ls with
        | none =>
            have hbad : (Dom.one : Dom lam) = .Omega i := by
              simpa [T.dom, hmin] using hd
            cases hbad
        | some md =>
            obtain ⟨m, d⟩ := md
            rw [T.fund, ite_eq_left rfl, hmin]
            cases d with
            | zero => intro h; cases h
            | omega => intro h; cases h
            | Omega j =>
                dsimp only
                split <;> intro h <;> cases h
            | one =>
                obtain ⟨mv, mh⟩ := m
                cases mv with
                | zero =>
                    have hbad : (Dom.omega : Dom lam) = .Omega i := by
                      simpa [T.dom, hmin] using hd
                    cases hbad
                | succ r => intro h; cases h
      · rw [T.fund_P_tail_eq ls add t hadd]
        intro h
        cases h

theorem T.fund_Omega_strict_mono_indexed {lam : Nat}
    (s x y : T lam) (i : Fin lam)
    (hd : T.dom s = .Omega i) (hxy : x < y) :
    T.fund s x < T.fund s y := by
  induction s using (measure T.size).wf.induction generalizing x y i with
  | h s ih =>
      cases s with
      | Z => cases hd
      | P ls add =>
          by_cases hadd : add = T.Z
          · subst add
            rw [T.dom, ite_eq_left rfl] at hd
            cases hmin : T.domVecMinIdx ls with
            | none => rw [hmin] at hd; cases hd
            | some md =>
                obtain ⟨m, d⟩ := md
                rw [hmin] at hd
                have hspec := T.domVecMinIdx_some_spec ls m d hmin
                cases d with
                | zero => cases hd
                | omega => cases hd
                | one =>
                    by_cases hm0 : m.val = 0
                    · simp [hm0] at hd
                    · simp only [hm0, ite_false] at hd
                      cases hd
                      obtain ⟨mv, mh⟩ := m
                      cases mv with
                      | zero => exact False.elim (hm0 rfl)
                      | succ r =>
                          rw [T.fund, ite_eq_left rfl, hmin,
                            T.fund, ite_eq_left rfl, hmin]
                          exact T.P_lt_P_of_compareVec_lt _ _ _ _
                            (Vec.compare_rplc_same_index_lt
                              (ls.rplc ⟨r + 1, mh⟩
                                (T.fund (ls.idx ⟨r + 1, mh⟩) T.Z))
                              ⟨r, Nat.lt_of_succ_lt mh⟩ x y hxy)
                | Omega j =>
                    by_cases hjm : j ≤ m
                    · simp only [hjm, ite_true] at hd
                      cases hd
                      rw [T.fund, ite_eq_left rfl, hmin,
                        T.fund, ite_eq_left rfl, hmin]
                      exact T.P_lt_P_of_compareVec_lt _ _ _ _
                        (Vec.compare_rplc_same_index_lt ls m _ _
                          (ih (ls.idx m) (T.idx_size_lt_P ls T.Z m)
                            x y j hspec.2.1 hxy))
                    · simp [hjm] at hd
          · rw [T.fund_P_tail_eq ls add x hadd,
              T.fund_P_tail_eq ls add y hadd]
            exact T.P_tail_lt ls _ _
              (ih add (T.add_size_lt_P ls add) x y i
                (by simpa [T.dom, hadd] using hd) hxy)

theorem T.iter_fund_lt_next_indexed {lam : Nat}
    (s t : T lam) (i : Fin lam)
    (hd : T.dom s = .Omega i) :
    T.iter (fun x => T.fund s x) t <
      T.fund s (T.iter (fun x => T.fund s x) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z =>
      rw [T.iter]
      cases he : T.fund s T.Z with
      | Z => exact False.elim (T.fund_Omega_ne_Z_indexed s T.Z i hd he)
      | P ls add => rfl
  | P us add _ ih =>
      exact T.fund_Omega_strict_mono_indexed s _ _ i hd ih
  | nil => trivial
  | snoc => trivial

end new
