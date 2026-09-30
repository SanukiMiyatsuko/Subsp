import Subsp.old.subsp

namespace new

theorem T.domVecMinIdx_spec {lam m : Nat} (v : Vec (T lam) m) :
    match T.domVecMinIdx v with
    | none => ∀ i : Fin m, T.dom (v.idx i) = .zero
    | some (i, d) =>
        d ≠ .zero ∧ T.dom (v.idx i) = d ∧
          ∀ j : Fin m, j.val < i.val →
            T.dom (v.idx j) = .zero := by
  induction v with
  | nil => intro i; exact i.elim0
  | snoc k xs x ih =>
      rw [T.domVecMinIdx]
      cases hrec : T.domVecMinIdx xs with
      | some p =>
          obtain ⟨i, d⟩ := p
          rw [hrec] at ih
          refine ⟨ih.1, ?_, ?_⟩
          · simpa [Vec.idx, i.isLt] using ih.2.1
          · intro j hj
            have hjk := Nat.lt_trans hj i.isLt
            simpa [Vec.idx, hjk] using ih.2.2 ⟨j.val, hjk⟩ hj
      | none =>
          rw [hrec] at ih
          by_cases hx : T.dom x = .zero
          · rw [ite_eq_left hx]
            intro i
            by_cases hi : i.val < k
            · simpa [Vec.idx, hi] using ih ⟨i.val, hi⟩
            · simpa [Vec.idx, hi] using hx
          · rw [ite_eq_right hx]
            refine ⟨hx, by simp [Vec.idx], ?_⟩
            intro j hj
            change j.val < k at hj
            simpa [Vec.idx, hj] using ih ⟨j.val, hj⟩

theorem T.domVecMinIdx_none_all_zero {lam m : Nat}
    (v : Vec (T lam) m) (h : T.domVecMinIdx v = none) :
    ∀ i : Fin m, T.dom (v.idx i) = .zero := by
  simpa only [h] using T.domVecMinIdx_spec v

theorem T.domVecMinIdx_some_spec {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) (d : Dom lam)
    (h : T.domVecMinIdx v = some (i, d)) :
    d ≠ .zero ∧ T.dom (v.idx i) = d ∧
      ∀ j : Fin m, j.val < i.val →
        T.dom (v.idx j) = .zero := by
  simpa only [h] using T.domVecMinIdx_spec v

theorem Vec.rplc_idx_same {A : Type} {n : Nat}
    (v : Vec A n) (i : Fin n) (a : A) :
    (v.rplc i a).idx i = a := by
  simp [Vec.rplc, Vec.ofFn_idx]

theorem Vec.rplc_idx_of_ne {A : Type} {n : Nat}
    (v : Vec A n) (i j : Fin n) (a : A)
    (h : j.val ≠ i.val) :
    (v.rplc i a).idx j = v.idx j := by
  simp [Vec.rplc, Vec.ofFn_idx, h]
  rfl

theorem Vec.compare_lt_of_pivot {lam m : Nat}
    (v w : Vec (T lam) m) (i : Fin m)
    (heq : ∀ j : Fin m, i.val < j.val →
      v.idx j = w.idx j)
    (hlt : v.idx i < w.idx i) :
    compareVec v w = Ordering.lt := by
  induction m with
  | zero => exact i.elim0
  | succ k ih =>
      cases v with
      | snoc _ xs x =>
        cases w with
        | snoc _ ys y =>
          by_cases hik : i.val = k
          · have hieq : i = Fin.last k := Fin.eq_of_val_eq hik
            have hxy : x < y := by simpa [hieq, Vec.idx] using hlt
            change compareT x y = .lt at hxy
            simp [compareVec, hxy]
          · have hiklt : i.val < k := by omega
            have hxy : x = y := by simpa [Vec.idx] using heq (Fin.last k) hiklt
            have hlt' : xs.idx ⟨i.val, hiklt⟩ < ys.idx ⟨i.val, hiklt⟩ := by
              simpa [Vec.idx, hiklt] using hlt
            have heq' : ∀ j : Fin k, i.val < j.val → xs.idx j = ys.idx j := by
              intro j hj
              simpa [Vec.idx, j.isLt] using heq j.castSucc hj
            simpa [compareVec, hxy, T_refl] using ih xs ys ⟨i.val, hiklt⟩ heq' hlt'

theorem Vec.compare_rplc_lt {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) (a : T lam)
    (h : a < v.idx i) :
    compareVec (v.rplc i a) v = Ordering.lt := by
  apply Vec.compare_lt_of_pivot _ _ i
  · exact fun j hj => Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj)
  · simpa only [Vec.rplc_idx_same] using h

theorem Vec.compare_rplc_rplc_lt {lam m : Nat}
    (v : Vec (T lam) m) (i j : Fin m)
    (a b : T lam) (hji : j.val < i.val)
    (ha : a < v.idx i) :
    compareVec ((v.rplc i a).rplc j b) v =
      Ordering.lt := by
  apply Vec.compare_lt_of_pivot _ _ i
  · intro q hq
    rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega), Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hq)]
  · simpa only [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hji), Vec.rplc_idx_same] using ha

theorem T.P_lt_P_of_compareVec_lt {lam : Nat}
    (v w : Vec (T lam) lam) (a b : T lam)
    (h : compareVec v w = Ordering.lt) :
    T.P v a < T.P w b := by
  simp only [LT.lt, T.lt, compareT, h]

theorem T.fund_PZ_none {lam : Nat}
    (ls : Vec (T lam) lam) (t : T lam)
    (hmin : T.domVecMinIdx ls = none) :
    T.fund (T.P ls T.Z) t = T.Z := by
  rw [T.fund, ite_eq_left rfl, hmin]

theorem T.mul_PZ_lt_of_compareVec_lt {lam : Nat}
    (u v : Vec (T lam) lam) (t : T lam)
    (h : compareVec u v = Ordering.lt) :
    T.mul (T.P u T.Z) t < T.P v T.Z := by
  cases t with
  | Z => rfl
  | P tls add => exact T.P_lt_P_of_compareVec_lt _ _ _ _ h

theorem T.fund_lt_self {lam : Nat}
    (s t : T lam) (hne : s ≠ T.Z) :
    T.fund s t < s := by
  induction s using (measure T.size).wf.induction generalizing t with
  | h s ih =>
      cases s with
      | Z => exact False.elim (hne rfl)
      | P ls add =>
          by_cases hadd : add = T.Z
          · subst add
            cases hmin : T.domVecMinIdx ls with
            | none => rw [T.fund_PZ_none ls t hmin]; rfl
            | some md =>
                obtain ⟨m, d⟩ := md
                have hspec := T.domVecMinIdx_some_spec ls m d hmin
                have hmne : ls.idx m ≠ T.Z := by
                  intro hz
                  have hd := hspec.2.1
                  rw [hz] at hd
                  exact hspec.1 hd.symm
                have hrec (u) : T.fund (ls.idx m) u < ls.idx m :=
                  ih _ (T.idx_size_lt_P ls T.Z m) u hmne
                rw [T.fund, ite_eq_left rfl, hmin]
                by_cases hd1 : d = .one
                · subst d
                  obtain ⟨mv, mh⟩ := m
                  cases mv with
                  | zero =>
                      exact T.mul_PZ_lt_of_compareVec_lt _ _ _
                        (Vec.compare_rplc_lt _ _ _ (hrec T.Z))
                  | succ r =>
                      exact T.P_lt_P_of_compareVec_lt _ _ _ _
                        (Vec.compare_rplc_rplc_lt _ _ _ _ _
                          (Nat.lt_succ_self r) (hrec T.Z))
                · simp only [hd1, ite_false]
                  split <;>
                    exact T.P_lt_P_of_compareVec_lt _ _ _ _
                      (Vec.compare_rplc_lt _ _ _ (hrec _))
          · rw [T.fund, ite_eq_right hadd]
            change (match compareVec ls ls with
              | .eq => compareT (T.fund add t) add | ord => ord) = .lt
            rw [Vec_refl]
            exact ih _ (T.add_size_lt_P ls add) t hadd

end new
