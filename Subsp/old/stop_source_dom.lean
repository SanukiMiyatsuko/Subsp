import Subsp.old.stop_source_mul

/-! Domain-sensitive source fundamental-sequence lemmas. -/

namespace new

theorem T.fund_P_tail_eq {lam : Nat}
    (ls : Vec (T lam) lam) (add t : T lam)
    (hadd : add ≠ T.Z) :
    T.fund (T.P ls add) t = T.P ls (T.fund add t) := by
  rw [T.fund, ite_eq_right hadd]


theorem T.fund_Omega_ne_Z {lam : Nat}
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
            | zero =>
                intro h
                cases h
            | omega =>
                intro h
                cases h
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
                | succ r =>
                    intro h
                    cases h
      · rw [T.fund_P_tail_eq ls add t hadd]
        intro h
        cases h


theorem Vec.compare_rplc_same_index_lt {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m)
    (a b : T lam) (hab : a < b) :
    compareVec (v.rplc i a) (v.rplc i b) = Ordering.lt := by
  apply Vec.compare_lt_of_pivot _ _ i
  · intro j hij
    rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hij),
      Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hij)]
  · simpa only [Vec.rplc_idx_same] using hab

end new
