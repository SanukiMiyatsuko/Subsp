import Subsp.Base

namespace new

inductive Dom (lam : Nat) where
| zero
| one
| omega
| Omega (i : Fin lam)
deriving DecidableEq

mutual
  def T.dom {lam : Nat} : T lam → Dom lam
  | .Z => .zero
  | .P ls add =>
    if add = Z then
      match domVecMinIdx ls with
      | none => .one
      | some (m, domSm) =>
        match domSm with
        | .one =>
          if m.val = 0 then .omega
          else .Omega m
        | .Omega i =>
          if i ≤ m then
            .Omega i
          else .omega
        | _ => .omega
    else dom add

  def T.domVecMinIdx {lam m : Nat} : Vec (T lam) m → Option (Fin m × Dom lam)
  | .nil => none
  | .snoc k xs x =>
    match domVecMinIdx xs with
    | some (i, d) => some (i.castSucc, d)
    | none =>
      let dx := dom x
      if dx = .zero then none
      else some (Fin.last k, dx)
end

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

-- theorem T.dom_PZ_one_iff {lam : Nat} (ls : Vec (T lam) lam) :
--     T.dom (T.P ls T.Z) = .one ↔ T.domVecMinIdx ls = none := by
--   simp only [T.dom, ite_true]
--   cases T.domVecMinIdx ls with
--   | none => simp
--   | some md =>
--       obtain ⟨m, d⟩ := md
--       by_cases hd : d = Dom.one <;> by_cases hm : m.val = 0 <;> simp [hd, hm]

-- theorem T.dom_PZ_Omega {lam : Nat} (ls : Vec (T lam) lam)
--     (hd : T.dom (T.P ls T.Z) = .Omega) :
--     ∃ (k : Nat) (h : k + 1 < lam), T.domVecMinIdx ls = some (⟨k + 1, h⟩, Dom.one) := by
--   cases hmin : T.domVecMinIdx ls with
--   | none => simp [T.dom, hmin] at hd
--   | some md =>
--       obtain ⟨⟨k, hk⟩, d⟩ := md
--       have hh : d = Dom.one ∧ k ≠ 0 := by
--         by_cases hd1 : d = Dom.one <;> by_cases hm : k = 0 <;> simp_all [T.dom]
--       obtain ⟨rfl, hm⟩ := hh
--       cases k with
--       | zero => exact False.elim (hm rfl)
--       | succ k => exact ⟨k, hk, rfl⟩

-- theorem T.dom_zero_eq_Z {lam : Nat} (s : T lam)
--     (hdom : T.dom s = .zero) : s = T.Z := by
--   cases s with
--   | Z => rfl
--   | P ls add =>
--       by_cases hadd : add = T.Z
--       · subst add
--         simp only [T.dom, ite_true] at hdom
--         split at hdom
--         · cases hdom
--         · split at hdom
--           · split at hdom <;> cases hdom
--           · cases hdom
--       · rw [T.dom, ite_eq_right hadd] at hdom
--         exact False.elim (hadd (T.dom_zero_eq_Z add hdom))

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

theorem Vec.idx_mem_toList {A : Type} {n : Nat}
    (v : Vec A n) (i : Fin n) :
    v.idx i ∈ Vec.toList v := by
  induction v with
  | nil => exact i.elim0
  | snoc k xs last ih =>
      simp only [Vec.idx, Vec.toList]
      split
      · exact List.mem_append_left _ (ih _)
      · simp

theorem Vec.mem_toList_exists_idx {A : Type} {n : Nat}
    (v : Vec A n) (x : A) (hx : x ∈ Vec.toList v) :
    ∃ i : Fin n, v.idx i = x := by
  induction v with
  | nil => cases hx
  | snoc k xs last ih =>
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨i, hi⟩ := ih hx
        exact ⟨i.castSucc, by simpa [Vec.idx, i.isLt] using hi⟩
      · exact ⟨Fin.last k, by simpa [Vec.idx] using (List.mem_singleton.mp hx).symm⟩

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

theorem Vec.compare_lt_has_pivot {lam m : Nat}
    (v w : Vec (T lam) m)
    (h : compareVec v w = Ordering.lt) :
    ∃ i : Fin m,
      (∀ j : Fin m, i.val < j.val →
        v.idx j = w.idx j) ∧
      v.idx i < w.idx i := by
  induction m with
  | zero => cases v; cases w; cases h
  | succ k ih =>
      cases v with
      | snoc _ xs x =>
        cases w with
        | snoc _ ys y =>
          cases hc : compareT x y with
          | lt =>
              refine ⟨Fin.last k, ?_, ?_⟩
              · intro j hj; change k < j.val at hj; omega
              · simpa [Vec.idx] using (show x < y from hc)
          | eq =>
              obtain ⟨i, hiAbove, hiLt⟩ := ih xs ys (by simpa [compareVec, hc] using h)
              refine ⟨i.castSucc, ?_, ?_⟩
              · intro j hij
                by_cases hjk : j.val < k
                · simpa [Vec.idx, hjk] using hiAbove ⟨j.val, hjk⟩ hij
                · simpa [Vec.idx, hjk] using T_eq_sound x y hc
              · simpa [Vec.idx, i.isLt] using hiLt
          | gt => simp [compareVec, hc] at h

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

theorem Vec.compare_lt_preserve_from_index {lam m : Nat}
    (a v w : Vec (T lam) m) (q : Fin m)
    (hvw : ∀ j : Fin m, q.val ≤ j.val →
      v.idx j = w.idx j)
    (hne : a.idx q ≠ v.idx q)
    (hlt : compareVec a v = Ordering.lt) :
    compareVec a w = Ordering.lt := by
  obtain ⟨i, hiAbove, hiLt⟩ := Vec.compare_lt_has_pivot a v hlt
  have hqi : q.val ≤ i.val := Nat.le_of_not_gt (fun h => hne (hiAbove q h))
  apply Vec.compare_lt_of_pivot a w i
  · intro j hij
    exact (hiAbove j hij).trans (hvw j (by omega))
  · rw [← hvw i hqi]
    exact hiLt

theorem Vec.compare_lt_after_pivot_update {lam m : Nat}
    (a old newv : Vec (T lam) m) (i : Fin m)
    (heqAbove :
      ∀ j : Fin m, i.val < j.val →
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

theorem T.P_vector_field_ne_self {lam : Nat}
    (xs : Vec (T lam) lam) (add : T lam)
    (q : Fin lam) :
    xs.idx q ≠ T.P xs add := by
  intro heq
  have h := Vec.idx_size_lt xs q
  rw [heq] at h
  simp only [T.size] at h
  omega

theorem T.P_lt_P_of_compareVec_lt {lam : Nat}
    (v w : Vec (T lam) lam) (a b : T lam)
    (h : compareVec v w = Ordering.lt) :
    T.P v a < T.P w b := by
  simp only [LT.lt, T.lt, compareT, h]

theorem T.Z_le {lam : Nat} (s : T lam) : T.Z ≤ s := by
  cases s <;> first | exact Or.inl rfl | exact Or.inr rfl

def T.fund {lam : Nat} (s t : T lam) : T lam :=
  match s with
  | Z => Z
  | P ls add =>
    if add = Z then
      match domVecMinIdx ls with
      | none => Z
      | some (m, d) =>
        match d with
        | .one =>
          match m with
          | ⟨0, _⟩ =>
            let updatedLs := ls.rplc m (T.fund ls[m] Z)
            mul (P updatedLs Z) t
          | ⟨m' + 1, h⟩ =>
            P ((ls.rplc m (fund ls[m] Z)).rplc ⟨m', Nat.lt_of_succ_lt h⟩ t) Z
        | .Omega i =>
          if i ≤ m then
            P (ls.rplc m (fund ls[m] t)) Z
          else
            let F := fun x => fund ls[m] x
            P (ls.rplc m (fund ls[m] (iter F t))) Z
        | _ =>
          P (ls.rplc m (fund ls[m] t)) Z
    else P ls (fund add t)
termination_by (T.size s, T.size t)
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left _ _ (T.idx_size_lt_P ls _ m)
    | exact Prod.Lex.left _ _ (T.add_size_lt_P ls add)

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

-- theorem T.fund_lt_self {lam : Nat}
--     (s t : T lam) (hne : s ≠ T.Z) :
--     T.fund s t < s := by
--   induction s using (measure T.size).wf.induction generalizing t with
--   | h s ih =>
--       cases s with
--       | Z => exact False.elim (hne rfl)
--       | P ls add =>
--           by_cases hadd : add = T.Z
--           · subst add
--             cases hmin : T.domVecMinIdx ls with
--             | none => rw [T.fund_PZ_none ls t hmin]; rfl
--             | some md =>
--                 obtain ⟨m, d⟩ := md
--                 have hspec := T.domVecMinIdx_some_spec ls m d hmin
--                 have hmne : ls.idx m ≠ T.Z := by
--                   intro hz
--                   have hd := hspec.2.1
--                   rw [hz] at hd
--                   exact hspec.1 hd.symm
--                 have hrec (u) : T.fund (ls.idx m) u < ls.idx m :=
--                   ih _ (T.idx_size_lt_P ls T.Z m) u hmne
--                 rw [T.fund, ite_eq_left rfl, hmin]
--                 by_cases hd1 : d = .one
--                 · subst d
--                   obtain ⟨mv, mh⟩ := m
--                   cases mv with
--                   | zero => exact T.mul_PZ_lt_of_compareVec_lt _ _ _ (Vec.compare_rplc_lt _ _ _ (hrec T.Z))
--                   | succ r =>
--                       exact T.P_lt_P_of_compareVec_lt _ _ _ _
--                         (Vec.compare_rplc_rplc_lt _ _ _ _ _ (Nat.lt_succ_self r) (hrec T.Z))
--                 · simp only [hd1, ite_false]
--                   split <;> exact T.P_lt_P_of_compareVec_lt _ _ _ _ (Vec.compare_rplc_lt _ _ _ (hrec _))
--           · rw [T.fund, ite_eq_right hadd]
--             change (match compareVec ls ls with
--               | .eq => compareT (T.fund add t) add | ord => ord) = .lt
--             rw [Vec_refl]
--             exact ih _ (T.add_size_lt_P ls add) t hadd

theorem T.head_mono {lam : Nat}
    (a b : T lam) (h : a < b) :
    T.head a ≤ T.head b := by
  cases a with
  | Z => exact T.Z_le _
  | P als aadd =>
      cases b with
      | Z => cases h
      | P bls badd =>
          change (match compareVec als bls with
            | .eq => compareT aadd badd | ord => ord) = .lt at h
          cases hc : compareVec als bls with
          | lt => exact Or.inl (T.P_lt_P_of_compareVec_lt _ _ _ _ hc)
          | eq => rw [Vec_eq_sound _ _ hc]; exact Or.inr (T_refl _)
          | gt => simp [hc] at h

-- theorem T.head_fund_le {lam : Nat}
--     (s t : T lam) :
--     T.head (T.fund s t) ≤ T.head s := by
--   cases s with
--   | Z => rw [T.fund]; exact T.Z_le _
--   | P ls add => exact T.head_mono _ _ (T.fund_lt_self _ _ (by intro h; cases h))

def T.LF (lam : Nat) : Nat → T lam
| 0 => Z
| n + 1 =>
  match lam with
  | 0 => P Vec.nil (LF 0 n)
  | lam' + 1 =>
    P (Vec.ofFn (lam' + 1) (fun i => if i = lam' then LF (lam' + 1) n else Z)) Z

inductive T.isOT : (lam : Nat) → T lam → Prop where
| base_0 (n : Nat) : isOT 0 (LF 0 n)
| base_succ (lam : Nat) (n : Nat) : isOT (lam + 1) (P (Vec.ofFn (lam + 1) (fun i => if i.val = 0 then LF (lam + 1) n else Z)) Z)
| step (lam : Nat) (s : T lam) (hs : isOT lam s) (n : Nat) : isOT lam (fund s (ofNat n))

end new
