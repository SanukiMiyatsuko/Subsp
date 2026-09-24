import Subsp.new.Base

namespace new

inductive Dom where
| zero
| one
| omega
| Omega
deriving DecidableEq

mutual
  def T.dom {lam : Nat} : T lam → Dom
  | .Z => .zero
  | .P ls add =>
    if add = Z then
      match domVecMinIdx ls with
      | none => .one
      | some (m, domSm) =>
        if domSm = .one then
          if m.val = 0 then .omega
          else .Omega
        else
          .omega
    else dom add

  def T.domVecMinIdx {lam m : Nat} : Vec (T lam) m → Option (Fin m × Dom)
  | .nil => none
  | .snoc k xs x =>
    match domVecMinIdx xs with
    | some (i, d) => some (i.castSucc, d)
    | none =>
      let dx := dom x
      if dx = .zero then none
      else some (Fin.last k, dx)
end

mutual
  def T.size {lam : Nat} : T lam → Nat
    | .Z => 0
    | .P ls add => 1 + Vec.size ls + T.size add

  def Vec.size {lam m : Nat} : Vec (T lam) m → Nat
    | .nil => 0
    | .snoc _ xs x => 1 + Vec.size xs + T.size x
end

theorem Vec.idx_size_lt {lam m : Nat} :
    ∀ (v : Vec (T lam) m) (i : Fin m), T.size (v.idx i) < Vec.size v := by
  intro v
  induction v with
  | nil => intro i; exact i.elim0
  | snoc k xs x ih =>
    intro i
    show T.size (if h : i.val < k then Vec.idx xs ⟨i.val, h⟩ else x)
        < 1 + Vec.size xs + T.size x
    by_cases h : i.val < k
    · rw [dite_eq_left h]
      have h1 : T.size (Vec.idx xs ⟨i.val, h⟩) < Vec.size xs := ih ⟨i.val, h⟩
      have h2 : Vec.size xs < 1 + Vec.size xs + T.size x := by
        have h2a : Vec.size xs ≤ Vec.size xs + T.size x := Nat.le_add_right _ _
        have h2b : Vec.size xs + T.size x < 1 + (Vec.size xs + T.size x) :=
          Nat.lt_add_of_pos_left Nat.zero_lt_one
        have h2c : 1 + (Vec.size xs + T.size x) = 1 + Vec.size xs + T.size x :=
          (Nat.add_assoc 1 (Vec.size xs) (T.size x)).symm
        calc Vec.size xs ≤ Vec.size xs + T.size x := h2a
          _ < 1 + (Vec.size xs + T.size x) := h2b
          _ = 1 + Vec.size xs + T.size x := h2c
      exact Nat.lt_trans h1 h2
    · rw [dite_eq_right h]
      have h3 : T.size x ≤ Vec.size xs + T.size x := Nat.le_add_left _ _
      have h4 : Vec.size xs + T.size x < 1 + (Vec.size xs + T.size x) :=
        Nat.lt_add_of_pos_left Nat.zero_lt_one
      have h5 : 1 + (Vec.size xs + T.size x) = 1 + Vec.size xs + T.size x :=
        (Nat.add_assoc 1 (Vec.size xs) (T.size x)).symm
      calc T.size x ≤ Vec.size xs + T.size x := h3
        _ < 1 + (Vec.size xs + T.size x) := h4
        _ = 1 + Vec.size xs + T.size x := h5

theorem Vec.getElem_eq_idx {A : Type} {n : Nat} (v : Vec A n) (m : Fin n) :
    v[m] = v.idx m := by
  show v[m.val] = v.idx m
  rfl

theorem T.idx_size_lt_P {lam : Nat} (ls : Vec (T lam) lam) (add : T lam) (i : Fin lam) :
    T.size (ls[i]) < T.size (T.P ls add) := by
  rw [Vec.getElem_eq_idx]
  have h1 : T.size (ls.idx i) < Vec.size ls := Vec.idx_size_lt ls i
  have h2 : Vec.size ls ≤ 1 + Vec.size ls := Nat.le_add_left (Vec.size ls) 1
  have h3 : 1 + Vec.size ls ≤ 1 + Vec.size ls + T.size add := Nat.le_add_right _ _
  have h4 : Vec.size ls ≤ 1 + Vec.size ls + T.size add := Nat.le_trans h2 h3
  have h5 : T.size (ls.idx i) < 1 + Vec.size ls + T.size add := Nat.lt_of_lt_of_le h1 h4
  show T.size (ls.idx i) < 1 + Vec.size ls + T.size add
  exact h5

theorem T.add_size_lt_P {lam : Nat} (ls : Vec (T lam) lam) (add : T lam) :
    T.size add < T.size (T.P ls add) := by
  have h1 : Vec.size ls + T.size add < 1 + (Vec.size ls + T.size add) :=
    Nat.lt_add_of_pos_left Nat.zero_lt_one
  have h2 : T.size add ≤ Vec.size ls + T.size add := Nat.le_add_left (T.size add) (Vec.size ls)
  have h3 : T.size add < 1 + (Vec.size ls + T.size add) := Nat.lt_of_le_of_lt h2 h1
  have h4 : 1 + (Vec.size ls + T.size add) = 1 + Vec.size ls + T.size add :=
    (Nat.add_assoc 1 (Vec.size ls) (T.size add)).symm
  show T.size add < 1 + Vec.size ls + T.size add
  rw [← h4]
  exact h3

theorem T.domVecMinIdx_spec {lam m : Nat} (v : Vec (T lam) m) :
    match T.domVecMinIdx v with
    | none => ∀ i : Fin m, T.dom (v.idx i) = .zero
    | some (i, d) =>
        d ≠ .zero ∧ T.dom (v.idx i) = d ∧
          ∀ j : Fin m, j.val < i.val →
            T.dom (v.idx j) = .zero := by
  induction v with
  | nil =>
      intro i
      exact i.elim0
  | snoc k xs x ih =>
      rw [T.domVecMinIdx]
      cases hrec : T.domVecMinIdx xs with
      | some p =>
          obtain ⟨i, d⟩ := p
          rw [hrec] at ih
          refine ⟨ih.1, ?_, ?_⟩
          · show T.dom
              (if h : i.val < k then
                Vec.idx xs ⟨i.val, h⟩ else x) = d
            rw [dite_eq_left i.isLt]
            exact ih.2.1
          · intro j hj
            have hjk : j.val < k :=
              Nat.lt_trans hj i.isLt
            show T.dom
                (if h : j.val < k then
                  Vec.idx xs ⟨j.val, h⟩ else x) = .zero
            rw [dite_eq_left hjk]
            exact ih.2.2 ⟨j.val, hjk⟩ hj
      | none =>
          rw [hrec] at ih
          by_cases hx : T.dom x = .zero
          · rw [if_pos hx]
            intro i
            by_cases hik : i.val < k
            · show T.dom
                (if h : i.val < k then
                  Vec.idx xs ⟨i.val, h⟩ else x) = .zero
              rw [dite_eq_left hik]
              exact ih ⟨i.val, hik⟩
            · show T.dom
                (if h : i.val < k then
                  Vec.idx xs ⟨i.val, h⟩ else x) = .zero
              rw [dite_eq_right hik]
              exact hx
          · rw [if_neg hx]
            refine ⟨hx, ?_, ?_⟩
            · show T.dom
                (if h : k < k then Vec.idx xs ⟨k, h⟩ else x) =
                  T.dom x
              rw [dite_eq_right (Nat.lt_irrefl k)]
            · intro j hj
              change j.val < k at hj
              show T.dom
                  (if h : j.val < k then
                    Vec.idx xs ⟨j.val, h⟩ else x) = .zero
              rw [dite_eq_left hj]
              exact ih ⟨j.val, hj⟩

theorem T.domVecMinIdx_none_all_zero {lam m : Nat}
    (v : Vec (T lam) m) (h : T.domVecMinIdx v = none) :
    ∀ i : Fin m, T.dom (v.idx i) = .zero := by
  have hs := T.domVecMinIdx_spec v
  rw [h] at hs
  exact hs

theorem T.domVecMinIdx_some_spec {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) (d : Dom)
    (h : T.domVecMinIdx v = some (i, d)) :
    d ≠ .zero ∧ T.dom (v.idx i) = d ∧
      ∀ j : Fin m, j.val < i.val →
        T.dom (v.idx j) = .zero := by
  have hs := T.domVecMinIdx_spec v
  rw [h] at hs
  exact hs

theorem T.dom_zero_eq_Z {lam : Nat} (s : T lam)
    (hdom : T.dom s = .zero) : s = T.Z := by
  cases s with
  | Z =>
      rfl
  | P ls add =>
      by_cases hadd : add = T.Z
      · subst add
        rw [T.dom, if_pos rfl] at hdom
        cases hmin : T.domVecMinIdx ls with
        | none =>
            rw [hmin] at hdom
            change Dom.one = Dom.zero at hdom
            cases hdom
        | some p =>
            obtain ⟨i, d⟩ := p
            rw [hmin] at hdom
            change
              (if d = Dom.one then
                if i.val = 0 then Dom.omega else Dom.Omega
              else Dom.omega) = Dom.zero at hdom
            by_cases hd1 : d = .one
            · rw [if_pos hd1] at hdom
              by_cases hi : i.val = 0
              · rw [if_pos hi] at hdom
                cases hdom
              · rw [if_neg hi] at hdom
                cases hdom
            · rw [if_neg hd1] at hdom
              cases hdom
      · rw [T.dom, if_neg hadd] at hdom
        have heq : add = T.Z :=
          T.dom_zero_eq_Z add hdom
        exact False.elim (hadd heq)
theorem Vec.rplc_idx_same {A : Type} {n : Nat}
    (v : Vec A n) (i : Fin n) (a : A) :
    (v.rplc i a).idx i = a := by
  unfold Vec.rplc
  rw [Vec.ofFn_idx]
  rw [if_pos rfl]

theorem Vec.rplc_idx_of_ne {A : Type} {n : Nat}
    (v : Vec A n) (i j : Fin n) (a : A)
    (h : j.val ≠ i.val) :
    (v.rplc i a).idx j = v.idx j := by
  unfold Vec.rplc
  rw [Vec.ofFn_idx]
  rw [if_neg h]
  rfl

theorem Vec.idx_mem_toList {A : Type} {n : Nat}
    (v : Vec A n) (i : Fin n) :
    v.idx i ∈ Vec.toList v := by
  induction v with
  | nil =>
      exact i.elim0
  | snoc k xs last ih =>
      rw [Vec.toList]
      change
        (if h : i.val < k then
          Vec.idx xs ⟨i.val, h⟩ else last) ∈
          Vec.toList xs ++ [last]
      by_cases h : i.val < k
      · rw [dite_eq_left h]
        exact List.mem_append_left [last] (ih ⟨i.val, h⟩)
      · rw [dite_eq_right h]
        exact List.mem_append_right (Vec.toList xs)
          (List.mem_singleton_self last)

theorem Vec.mem_toList_exists_idx {A : Type} {n : Nat}
    (v : Vec A n) (x : A) (hx : x ∈ Vec.toList v) :
    ∃ i : Fin n, v.idx i = x := by
  induction v with
  | nil =>
      cases hx
  | snoc k xs last ih =>
      rw [Vec.toList] at hx
      cases List.mem_append.mp hx with
      | inl hxs =>
          obtain ⟨i, hi⟩ := ih hxs
          refine ⟨i.castSucc, ?_⟩
          show
            (if h : i.val < k then
              Vec.idx xs ⟨i.val, h⟩ else last) = x
          rw [dite_eq_left i.isLt]
          exact hi
      | inr hlast =>
          have heq : x = last := List.mem_singleton.mp hlast
          refine ⟨Fin.last k, ?_⟩
          show
            (if h : k < k then
              Vec.idx xs ⟨k, h⟩ else last) = x
          rw [dite_eq_right (Nat.lt_irrefl k)]
          exact heq.symm

theorem Vec.compare_lt_of_pivot {lam m : Nat}
    (v w : Vec (T lam) m) (i : Fin m)
    (heq : ∀ j : Fin m, i.val < j.val →
      v.idx j = w.idx j)
    (hlt : v.idx i < w.idx i) :
    compareVec v w = Ordering.lt := by
  induction m with
  | zero =>
      exact i.elim0
  | succ k ih =>
      cases v with
      | snoc _ xs x =>
        cases w with
        | snoc _ ys y =>
          by_cases hik : i.val = k
          · have hieq : i = Fin.last k :=
              Fin.eq_of_val_eq hik
            have hx :
                (Vec.snoc k xs x).idx (Fin.last k) = x := by
              show
                (if h : k < k then
                  Vec.idx xs ⟨k, h⟩ else x) = x
              rw [dite_eq_right (Nat.lt_irrefl k)]
            have hy :
                (Vec.snoc k ys y).idx (Fin.last k) = y := by
              show
                (if h : k < k then
                  Vec.idx ys ⟨k, h⟩ else y) = y
              rw [dite_eq_right (Nat.lt_irrefl k)]
            rw [hieq, hx, hy] at hlt
            show
              (match compareT x y with
              | Ordering.eq => compareVec xs ys
              | ord => ord) = Ordering.lt
            rw [hlt]
          · have hiklt : i.val < k := by
              have hle : i.val ≤ k :=
                Nat.lt_succ_iff.mp i.isLt
              exact Nat.lt_of_le_of_ne hle hik
            let i' : Fin k := ⟨i.val, hiklt⟩
            have hxy : x = y := by
              have hh := heq (Fin.last k) hiklt
              have hx :
                  (Vec.snoc k xs x).idx (Fin.last k) = x := by
                show
                  (if h : k < k then
                    Vec.idx xs ⟨k, h⟩ else x) = x
                rw [dite_eq_right (Nat.lt_irrefl k)]
              have hy :
                  (Vec.snoc k ys y).idx (Fin.last k) = y := by
                show
                  (if h : k < k then
                    Vec.idx ys ⟨k, h⟩ else y) = y
                rw [dite_eq_right (Nat.lt_irrefl k)]
              rw [hx, hy] at hh
              exact hh
            have hlt' : xs.idx i' < ys.idx i' := by
              have hv :
                  (Vec.snoc k xs x).idx i = xs.idx i' := by
                show
                  (if h : i.val < k then
                    Vec.idx xs ⟨i.val, h⟩ else x) =
                    Vec.idx xs i'
                rw [dite_eq_left hiklt]
              have hw :
                  (Vec.snoc k ys y).idx i = ys.idx i' := by
                show
                  (if h : i.val < k then
                    Vec.idx ys ⟨i.val, h⟩ else y) =
                    Vec.idx ys i'
                rw [dite_eq_left hiklt]
              rw [hv, hw] at hlt
              exact hlt
            have heq' :
                ∀ j : Fin k, i'.val < j.val →
                  xs.idx j = ys.idx j := by
              intro j hj
              have hv :
                  (Vec.snoc k xs x).idx j.castSucc =
                    xs.idx j := by
                show
                  (if h : j.val < k then
                    Vec.idx xs ⟨j.val, h⟩ else x) =
                    Vec.idx xs j
                rw [dite_eq_left j.isLt]
              have hw :
                  (Vec.snoc k ys y).idx j.castSucc =
                    ys.idx j := by
                show
                  (if h : j.val < k then
                    Vec.idx ys ⟨j.val, h⟩ else y) =
                    Vec.idx ys j
                rw [dite_eq_left j.isLt]
              have hh := heq j.castSucc hj
              rw [hv, hw] at hh
              exact hh
            have hrec :=
              ih xs ys i' heq' hlt'
            show
              (match compareT x y with
              | Ordering.eq => compareVec xs ys
              | ord => ord) = Ordering.lt
            have hceq : compareT x y = Ordering.eq := by
              rw [hxy]
              exact T_refl y
            rw [hceq]
            exact hrec

theorem Vec.compare_lt_has_pivot {lam m : Nat}
    (v w : Vec (T lam) m)
    (h : compareVec v w = Ordering.lt) :
    ∃ i : Fin m,
      (∀ j : Fin m, i.val < j.val →
        v.idx j = w.idx j) ∧
      v.idx i < w.idx i := by
  induction m with
  | zero =>
      cases v with
      | nil =>
        cases w with
        | nil =>
          cases h
  | succ k ih =>
      cases v with
      | snoc _ xs x =>
        cases w with
        | snoc _ ys y =>
          change
            (match compareT x y with
            | Ordering.eq => compareVec xs ys
            | ord => ord) = Ordering.lt at h
          cases hc : compareT x y with
          | lt =>
              refine ⟨Fin.last k, ?_, ?_⟩
              · intro j hj
                have hjle : j.val ≤ k :=
                  Nat.lt_succ_iff.mp j.isLt
                exact False.elim
                  ((Nat.not_lt_of_ge hjle) hj)
              · have hv :
                    (Vec.snoc k xs x).idx (Fin.last k) = x := by
                  show
                    (if hlt : k < k then
                      Vec.idx xs ⟨k, hlt⟩ else x) = x
                  rw [dite_eq_right (Nat.lt_irrefl k)]
                have hw :
                    (Vec.snoc k ys y).idx (Fin.last k) = y := by
                  show
                    (if hlt : k < k then
                      Vec.idx ys ⟨k, hlt⟩ else y) = y
                  rw [dite_eq_right (Nat.lt_irrefl k)]
                rw [hv, hw]
                exact hc
          | eq =>
              rw [hc] at h
              obtain ⟨i, hiAbove, hiLt⟩ :=
                ih xs ys h
              refine ⟨i.castSucc, ?_, ?_⟩
              · intro j hij
                by_cases hjk : j.val < k
                · have hv :
                      (Vec.snoc k xs x).idx j =
                        xs.idx ⟨j.val, hjk⟩ := by
                    show
                      (if hlt : j.val < k then
                        Vec.idx xs ⟨j.val, hlt⟩ else x) =
                        Vec.idx xs ⟨j.val, hjk⟩
                    rw [dite_eq_left hjk]
                  have hw :
                      (Vec.snoc k ys y).idx j =
                        ys.idx ⟨j.val, hjk⟩ := by
                    show
                      (if hlt : j.val < k then
                        Vec.idx ys ⟨j.val, hlt⟩ else y) =
                        Vec.idx ys ⟨j.val, hjk⟩
                    rw [dite_eq_left hjk]
                  rw [hv, hw]
                  exact hiAbove ⟨j.val, hjk⟩ hij
                · have hjle : j.val ≤ k :=
                    Nat.lt_succ_iff.mp j.isLt
                  have hkj : k ≤ j.val :=
                    Nat.not_lt.mp hjk
                  have hjval : j.val = k :=
                    Nat.le_antisymm hjle hkj
                  have hjeq : j = Fin.last k :=
                    Fin.eq_of_val_eq hjval
                  rw [hjeq]
                  have hv :
                      (Vec.snoc k xs x).idx (Fin.last k) = x := by
                    show
                      (if hlt : k < k then
                        Vec.idx xs ⟨k, hlt⟩ else x) = x
                    rw [dite_eq_right (Nat.lt_irrefl k)]
                  have hw :
                      (Vec.snoc k ys y).idx (Fin.last k) = y := by
                    show
                      (if hlt : k < k then
                        Vec.idx ys ⟨k, hlt⟩ else y) = y
                    rw [dite_eq_right (Nat.lt_irrefl k)]
                  rw [hv, hw]
                  exact T_eq_sound x y hc
              · have hv :
                    (Vec.snoc k xs x).idx i.castSucc =
                      xs.idx i := by
                  show
                    (if hlt : i.val < k then
                      Vec.idx xs ⟨i.val, hlt⟩ else x) =
                      Vec.idx xs i
                  rw [dite_eq_left i.isLt]
                have hw :
                    (Vec.snoc k ys y).idx i.castSucc =
                      ys.idx i := by
                  show
                    (if hlt : i.val < k then
                      Vec.idx ys ⟨i.val, hlt⟩ else y) =
                      Vec.idx ys i
                  rw [dite_eq_left i.isLt]
                rw [hv, hw]
                exact hiLt
          | gt =>
              rw [hc] at h
              cases h

theorem Vec.compare_rplc_lt {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) (a : T lam)
    (h : a < v.idx i) :
    compareVec (v.rplc i a) v = Ordering.lt := by
  apply Vec.compare_lt_of_pivot (v.rplc i a) v i
  · intro j hij
    exact Vec.rplc_idx_of_ne v i j a
      (Nat.ne_of_gt hij)
  · rw [Vec.rplc_idx_same]
    exact h

theorem Vec.compare_rplc_rplc_lt {lam m : Nat}
    (v : Vec (T lam) m) (i j : Fin m)
    (a b : T lam) (hji : j.val < i.val)
    (ha : a < v.idx i) :
    compareVec ((v.rplc i a).rplc j b) v =
      Ordering.lt := by
  apply Vec.compare_lt_of_pivot
    ((v.rplc i a).rplc j b) v i
  · intro q hiq
    have hqi : q.val ≠ i.val := Nat.ne_of_gt hiq
    have hqj : q.val ≠ j.val :=
      Nat.ne_of_gt (Nat.lt_trans hji hiq)
    rw [Vec.rplc_idx_of_ne (v.rplc i a) j q b hqj]
    rw [Vec.rplc_idx_of_ne v i q a hqi]
  · have hij : i.val ≠ j.val := Nat.ne_of_gt hji
    rw [Vec.rplc_idx_of_ne (v.rplc i a) j i b hij]
    rw [Vec.rplc_idx_same]
    exact ha

theorem Vec.compare_lt_preserve_from_index {lam m : Nat}
    (a v w : Vec (T lam) m) (q : Fin m)
    (hvw : ∀ j : Fin m, q.val ≤ j.val →
      v.idx j = w.idx j)
    (hne : a.idx q ≠ v.idx q)
    (hlt : compareVec a v = Ordering.lt) :
    compareVec a w = Ordering.lt := by
  induction m with
  | zero =>
    exact q.elim0
  | succ k ih =>
    cases a with
    | snoc _ as aLast =>
      cases v with
      | snoc _ vs vLast =>
        cases w with
        | snoc _ ws wLast =>
          have hlastV :
              (Vec.snoc k vs vLast).idx
                (Fin.last k) = vLast := by
            show
              (if h : k < k then
                Vec.idx vs ⟨k, h⟩ else vLast) = vLast
            rw [dite_eq_right (Nat.lt_irrefl k)]
          have hlastW :
              (Vec.snoc k ws wLast).idx
                (Fin.last k) = wLast := by
            show
              (if h : k < k then
                Vec.idx ws ⟨k, h⟩ else wLast) = wLast
            rw [dite_eq_right (Nat.lt_irrefl k)]
          have hvwLast : vLast = wLast := by
            have hqk : q.val ≤ k :=
              Nat.le_of_lt_succ q.isLt
            have hh := hvw (Fin.last k) hqk
            rw [hlastV, hlastW] at hh
            exact hh
          show
            (match compareT aLast wLast with
            | Ordering.eq => compareVec as ws
            | ord => ord) = Ordering.lt
          change
            (match compareT aLast vLast with
            | Ordering.eq => compareVec as vs
            | ord => ord) = Ordering.lt at hlt
          cases hc : compareT aLast vLast with
          | lt =>
            have hc' :
                compareT aLast wLast = Ordering.lt := by
              rw [← hvwLast]
              exact hc
            rw [hc']
          | gt =>
            rw [hc] at hlt
            cases hlt
          | eq =>
            have hc' :
                compareT aLast wLast = Ordering.eq := by
              rw [← hvwLast]
              exact hc
            rw [hc']
            rw [hc] at hlt
            by_cases hq : q.val = k
            · have hqe : q = Fin.last k :=
                Fin.eq_of_val_eq hq
              have haLast :
                  (Vec.snoc k as aLast).idx
                    (Fin.last k) = aLast := by
                show
                  (if h : k < k then
                    Vec.idx as ⟨k, h⟩ else aLast) = aLast
                rw [dite_eq_right (Nat.lt_irrefl k)]
              rw [hqe, haLast, hlastV] at hne
              have heq : aLast = vLast :=
                T_eq_sound aLast vLast hc
              exact False.elim (hne heq)
            · have hqk : q.val < k := by
                have hle : q.val ≤ k :=
                  Nat.le_of_lt_succ q.isLt
                exact Nat.lt_of_le_of_ne hle hq
              let q' : Fin k := ⟨q.val, hqk⟩
              have hne' :
                  as.idx q' ≠ vs.idx q' := by
                intro heq
                apply hne
                show
                  (if h : q.val < k then
                    Vec.idx as ⟨q.val, h⟩ else aLast) ≠
                  (if h : q.val < k then
                    Vec.idx vs ⟨q.val, h⟩ else vLast)
                rw [dite_eq_left hqk,
                  dite_eq_left hqk]
                exact heq
              have hvw' :
                  ∀ j : Fin k, q'.val ≤ j.val →
                    vs.idx j = ws.idx j := by
                intro j hj
                have hv :
                    (Vec.snoc k vs vLast).idx j.castSucc =
                      vs.idx j := by
                  show
                    (if h : j.val < k then
                      Vec.idx vs ⟨j.val, h⟩ else vLast) =
                      Vec.idx vs j
                  rw [dite_eq_left j.isLt]
                have hw :
                    (Vec.snoc k ws wLast).idx j.castSucc =
                      ws.idx j := by
                  show
                    (if h : j.val < k then
                      Vec.idx ws ⟨j.val, h⟩ else wLast) =
                      Vec.idx ws j
                  rw [dite_eq_left j.isLt]
                have hh := hvw j.castSucc hj
                rw [hv, hw] at hh
                exact hh
              exact ih as vs ws q'
                hvw' hne' hlt

theorem Vec.compare_lt_after_pivot_update {lam m : Nat}
    (a old newv : Vec (T lam) m) (i : Fin m)
    (heqAbove :
      ∀ j : Fin m, i.val < j.val →
        old.idx j = newv.idx j)
    (hold : compareVec a old = Ordering.lt)
    (hpivot : a.idx i < newv.idx i) :
    compareVec a newv = Ordering.lt := by
  induction m with
  | zero =>
    exact i.elim0
  | succ k ih =>
    cases a with
    | snoc _ as aLast =>
      cases old with
      | snoc _ os oLast =>
        cases newv with
        | snoc _ ns nLast =>
          show
            (match compareT aLast nLast with
            | Ordering.eq => compareVec as ns
            | ord => ord) = Ordering.lt
          change
            (match compareT aLast oLast with
            | Ordering.eq => compareVec as os
            | ord => ord) = Ordering.lt at hold
          by_cases hik : i.val = k
          · have hieq : i = Fin.last k :=
              Fin.eq_of_val_eq hik
            have haLast :
                (Vec.snoc k as aLast).idx
                  (Fin.last k) = aLast := by
              show
                (if h : k < k then
                  Vec.idx as ⟨k, h⟩ else aLast) = aLast
              rw [dite_eq_right (Nat.lt_irrefl k)]
            have hnLast :
                (Vec.snoc k ns nLast).idx
                  (Fin.last k) = nLast := by
              show
                (if h : k < k then
                  Vec.idx ns ⟨k, h⟩ else nLast) = nLast
              rw [dite_eq_right (Nat.lt_irrefl k)]
            rw [hieq, haLast, hnLast] at hpivot
            rw [hpivot]
          · have hiklt : i.val < k := by
              have hle : i.val ≤ k :=
                Nat.le_of_lt_succ i.isLt
              exact Nat.lt_of_le_of_ne hle hik
            have hoLast :
                (Vec.snoc k os oLast).idx
                  (Fin.last k) = oLast := by
              show
                (if h : k < k then
                  Vec.idx os ⟨k, h⟩ else oLast) = oLast
              rw [dite_eq_right (Nat.lt_irrefl k)]
            have hnLast :
                (Vec.snoc k ns nLast).idx
                  (Fin.last k) = nLast := by
              show
                (if h : k < k then
                  Vec.idx ns ⟨k, h⟩ else nLast) = nLast
              rw [dite_eq_right (Nat.lt_irrefl k)]
            have hon : oLast = nLast := by
              have hh :=
                heqAbove (Fin.last k) hiklt
              rw [hoLast, hnLast] at hh
              exact hh
            cases hc : compareT aLast oLast with
            | lt =>
              have hc' :
                  compareT aLast nLast = Ordering.lt := by
                rw [← hon]
                exact hc
              rw [hc']
            | gt =>
              rw [hc] at hold
              cases hold
            | eq =>
              have hc' :
                  compareT aLast nLast = Ordering.eq := by
                rw [← hon]
                exact hc
              rw [hc']
              rw [hc] at hold
              let i' : Fin k := ⟨i.val, hiklt⟩
              have hpivot' :
                  as.idx i' < ns.idx i' := by
                show
                  (if h : i.val < k then
                    Vec.idx as ⟨i.val, h⟩ else aLast) <
                  (if h : i.val < k then
                    Vec.idx ns ⟨i.val, h⟩ else nLast) at hpivot
                rw [dite_eq_left hiklt,
                  dite_eq_left hiklt] at hpivot
                exact hpivot
              have heqAbove' :
                  ∀ j : Fin k, i'.val < j.val →
                    os.idx j = ns.idx j := by
                intro j hj
                have ho :
                    (Vec.snoc k os oLast).idx j.castSucc =
                      os.idx j := by
                  show
                    (if h : j.val < k then
                      Vec.idx os ⟨j.val, h⟩ else oLast) =
                      Vec.idx os j
                  rw [dite_eq_left j.isLt]
                have hn :
                    (Vec.snoc k ns nLast).idx j.castSucc =
                      ns.idx j := by
                  show
                    (if h : j.val < k then
                      Vec.idx ns ⟨j.val, h⟩ else nLast) =
                      Vec.idx ns j
                  rw [dite_eq_left j.isLt]
                have hh := heqAbove j.castSucc hj
                rw [ho, hn] at hh
                exact hh
              exact ih as os ns i'
                heqAbove' hold hpivot'

theorem T.P_vector_field_ne_self {lam : Nat}
    (xs : Vec (T lam) lam) (add : T lam)
    (q : Fin lam) :
    xs.idx q ≠ T.P xs add := by
  intro heq
  have hlt :
      T.size (xs.idx q) < Vec.size xs :=
    Vec.idx_size_lt xs q
  rw [heq] at hlt
  have hge :
      Vec.size xs ≤ T.size (T.P xs add) := by
    show
      Vec.size xs ≤
        1 + Vec.size xs + T.size add
    have h1 :
        Vec.size xs ≤ 1 + Vec.size xs :=
      Nat.le_add_left (Vec.size xs) 1
    have h2 :
        1 + Vec.size xs ≤
          1 + Vec.size xs + T.size add :=
      Nat.le_add_right _ _
    exact Nat.le_trans h1 h2
  exact (Nat.not_lt_of_ge hge) hlt

theorem T.P_lt_P_of_compareVec_lt {lam : Nat}
    (v w : Vec (T lam) lam) (a b : T lam)
    (h : compareVec v w = Ordering.lt) :
    T.P v a < T.P w b := by
  show
    (match compareVec v w with
    | Ordering.eq => compareT a b
    | ord => ord) = Ordering.lt
  rw [h]

theorem T.Z_le {lam : Nat} (s : T lam) : T.Z ≤ s := by
  cases s with
  | Z =>
      exact Or.inr rfl
  | P ls add =>
      exact Or.inl rfl

def T.fund {lam : Nat} (s t : T lam) : T lam :=
  match s with
  | Z => Z
  | P ls add =>
    if add = Z then
      match domVecMinIdx ls with
      | none => Z
      | some (m, d) =>
        if d = .one then
          match m with
          | ⟨0, _⟩ =>
            let updatedLs := ls.rplc m (T.fund ls[m] Z)
            mul (P updatedLs Z) t
          | ⟨m' + 1, h⟩ =>
            P ((ls.rplc m (fund ls[m] Z)).rplc ⟨m', Nat.lt_of_succ_lt h⟩ t) Z
        else if d = .Omega then
          let F := fun x => fund ls[m] x
          P (ls.rplc m (fund ls[m] (iter F t))) Z
        else
          P (ls.rplc m (fund ls[m] t)) Z
    else P ls (fund add t)
termination_by (T.size s, T.size t)
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left _ _ (T.idx_size_lt_P ls _ m)
    | exact Prod.Lex.right _ (T.add_size_lt_P _ _)
    | exact Prod.Lex.left _ _ (T.add_size_lt_P ls add)

theorem T.fund_PZ_none {lam : Nat}
    (ls : Vec (T lam) lam) (t : T lam)
    (hmin : T.domVecMinIdx ls = none) :
    T.fund (T.P ls T.Z) t = T.Z := by
  rw [T.fund, if_pos rfl, hmin]

theorem T.mul_PZ_lt_of_compareVec_lt {lam : Nat}
    (u v : Vec (T lam) lam) (t : T lam)
    (h : compareVec u v = Ordering.lt) :
    T.mul (T.P u T.Z) t < T.P v T.Z := by
  cases t with
  | Z =>
      rfl
  | P tls add =>
      rw [T.mul]
      change
        T.P u (T.mul (T.P u T.Z) add) <
          T.P v T.Z
      exact T.P_lt_P_of_compareVec_lt
        u v (T.mul (T.P u T.Z) add) T.Z h

theorem T.fund_lt_self {lam : Nat}
    (s t : T lam) (hne : s ≠ T.Z) :
    T.fund s t < s := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ a b : T lam, T.size a = n →
        a ≠ T.Z → T.fund a b < a
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a b hsize hanz
      cases a with
      | Z =>
        exact False.elim (hanz rfl)
      | P ls add =>
        by_cases hadd : add = T.Z
        · subst add
          cases hmin : T.domVecMinIdx ls with
          | none =>
            rw [T.fund_PZ_none ls b hmin]
            rfl
          | some md =>
            obtain ⟨m, d⟩ := md
            have hspec :=
              T.domVecMinIdx_some_spec ls m d hmin
            have hmne : ls.idx m ≠ T.Z := by
              intro hmz
              have hdom : T.dom (ls.idx m) = d :=
                hspec.2.1
              rw [hmz] at hdom
              exact hspec.1 hdom.symm
            have hmsize : T.size (ls.idx m) < n := by
              have hlt : T.size (ls.idx m) <
                  T.size (T.P ls T.Z) := by
                rw [← Vec.getElem_eq_idx ls m]
                exact T.idx_size_lt_P ls T.Z m
              rw [hsize] at hlt
              exact hlt
            by_cases hd1 : d = .one
            · cases m with
              | mk mv mh =>
                cases mv with
                | zero =>
                  let mi : Fin lam := ⟨0, mh⟩
                  conv =>
                    lhs
                    rw [T.fund, if_pos rfl]
                    rw [hmin]
                    change (if d = .one then _ else _)
                    rw [if_pos hd1]
                  change
                    T.mul
                      (T.P
                        (ls.rplc mi
                          (T.fund (ls.idx mi) T.Z))
                        T.Z)
                      b < T.P ls T.Z
                  have hrec :
                      T.fund (ls.idx mi) T.Z <
                        ls.idx mi :=
                    ih (T.size (ls.idx mi)) hmsize
                      (ls.idx mi) T.Z rfl hmne
                  have hvec :
                      compareVec
                        (ls.rplc mi
                          (T.fund (ls.idx mi) T.Z))
                        ls = Ordering.lt :=
                    Vec.compare_rplc_lt ls mi
                      (T.fund (ls.idx mi) T.Z) hrec
                  exact T.mul_PZ_lt_of_compareVec_lt
                    (ls.rplc mi
                      (T.fund (ls.idx mi) T.Z))
                    ls b hvec
                | succ m' =>
                  let mi : Fin lam := ⟨m' + 1, mh⟩
                  let j : Fin lam :=
                    ⟨m', Nat.lt_of_succ_lt mh⟩
                  conv =>
                    lhs
                    rw [T.fund, if_pos rfl]
                    rw [hmin]
                    change (if d = .one then _ else _)
                    rw [if_pos hd1]
                  change
                    T.P
                      ((ls.rplc mi
                        (T.fund (ls.idx mi) T.Z)).rplc
                          j b)
                      T.Z < T.P ls T.Z
                  have hrec :
                      T.fund (ls.idx mi) T.Z <
                        ls.idx mi :=
                    ih (T.size (ls.idx mi)) hmsize
                      (ls.idx mi) T.Z rfl hmne
                  have hvec :
                      compareVec
                        ((ls.rplc mi
                          (T.fund (ls.idx mi) T.Z)).rplc
                            j b)
                        ls = Ordering.lt :=
                    Vec.compare_rplc_rplc_lt
                      ls mi j
                      (T.fund (ls.idx mi) T.Z)
                      b (Nat.lt_succ_self m') hrec
                  exact T.P_lt_P_of_compareVec_lt
                    ((ls.rplc mi
                      (T.fund (ls.idx mi) T.Z)).rplc
                        j b)
                    ls T.Z T.Z hvec
            · by_cases hdO : d = .Omega
              · conv =>
                  lhs
                  rw [T.fund, if_pos rfl]
                  rw [hmin]
                  change (if d = .one then _ else _)
                  rw [if_neg hd1]
                  change (if d = .Omega then _ else _)
                  rw [if_pos hdO]
                have hrec :
                    T.fund (ls.idx m)
                      (T.iter
                        (fun x => T.fund (ls.idx m) x) b) <
                      ls.idx m :=
                  ih (T.size (ls.idx m)) hmsize
                    (ls.idx m)
                    (T.iter
                      (fun x => T.fund (ls.idx m) x) b)
                    rfl hmne
                have hvec :
                    compareVec
                      (ls.rplc m
                        (T.fund (ls.idx m)
                          (T.iter
                            (fun x =>
                              T.fund (ls.idx m) x) b)))
                      ls = Ordering.lt :=
                  Vec.compare_rplc_lt ls m
                    (T.fund (ls.idx m)
                      (T.iter
                        (fun x =>
                          T.fund (ls.idx m) x) b))
                    hrec
                exact T.P_lt_P_of_compareVec_lt
                  (ls.rplc m
                    (T.fund (ls.idx m)
                      (T.iter
                        (fun x =>
                          T.fund (ls.idx m) x) b)))
                  ls T.Z T.Z hvec
              · conv =>
                  lhs
                  rw [T.fund, if_pos rfl]
                  rw [hmin]
                  change (if d = .one then _ else _)
                  rw [if_neg hd1]
                  change (if d = .Omega then _ else _)
                  rw [if_neg hdO]
                change
                  T.P
                    (ls.rplc m
                      (T.fund (ls.idx m) b))
                    T.Z < T.P ls T.Z
                have hrec :
                    T.fund (ls.idx m) b <
                      ls.idx m :=
                  ih (T.size (ls.idx m)) hmsize
                    (ls.idx m) b rfl hmne
                have hvec :
                    compareVec
                      (ls.rplc m
                        (T.fund (ls.idx m) b))
                      ls = Ordering.lt :=
                  Vec.compare_rplc_lt ls m
                    (T.fund (ls.idx m) b) hrec
                exact T.P_lt_P_of_compareVec_lt
                  (ls.rplc m
                    (T.fund (ls.idx m) b))
                  ls T.Z T.Z hvec
        · rw [T.fund]
          rw [if_neg hadd]
          have haddsize : T.size add < n := by
            have hlt := T.add_size_lt_P ls add
            rw [hsize] at hlt
            exact hlt
          have hrec : T.fund add b < add :=
            ih (T.size add) haddsize add b rfl hadd
          change
            (match compareVec ls ls with
            | Ordering.eq =>
                compareT (T.fund add b) add
            | ord => ord) = Ordering.lt
          rw [Vec_refl ls]
          exact hrec)
  exact main (T.size s) s t rfl hne

theorem T.head_mono {lam : Nat}
    (a b : T lam) (h : a < b) :
    T.head a ≤ T.head b := by
  cases a with
  | Z =>
      exact T.Z_le (T.head b)
  | P als aadd =>
    cases b with
    | Z =>
      change compareT (T.P als aadd) T.Z =
        Ordering.lt at h
      cases h
    | P bls badd =>
      change
        (match compareVec als bls with
        | Ordering.eq => compareT aadd badd
        | ord => ord) = Ordering.lt at h
      cases hc : compareVec als bls with
      | lt =>
          exact Or.inl
            (T.P_lt_P_of_compareVec_lt
              als bls T.Z T.Z hc)
      | eq =>
          have hls : als = bls :=
            Vec_eq_sound als bls hc
          rw [hls]
          exact Or.inr (T_refl (T.P bls T.Z))
      | gt =>
          rw [hc] at h
          cases h

theorem T.head_fund_le {lam : Nat}
    (s t : T lam) :
    T.head (T.fund s t) ≤ T.head s := by
  cases s with
  | Z =>
      rw [T.fund]
      exact T.Z_le T.Z
  | P ls add =>
      have hne : T.P ls add ≠ T.Z := by
        intro h
        cases h
      exact T.head_mono
        (T.fund (T.P ls add) t)
        (T.P ls add)
        (T.fund_lt_self (T.P ls add) t hne)

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

def T.G {lam : Nat} (s : T lam) : List (T lam) :=
  match s with
  | Z => []
  | P ls add =>
    let rec res {m : Nat} (vt : Vec (T lam) m) : List (T lam) :=
      match vt with
      | .nil => []
      | .snoc n v last => res v ++ [last] ++ G last
    res ls ++ G add

theorem T.G_P_eq {lam : Nat} (ls : Vec (T lam) lam) (add : T lam) :
    T.G (T.P ls add) = T.G.res ls ++ T.G add := by
  rfl

theorem Vec.Gres_mem_of_idx {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) :
    v.idx i ∈ T.G.res v := by
  induction v with
  | nil =>
      exact i.elim0
  | snoc k xs last ih =>
      change
        (if h : i.val < k then
          Vec.idx xs ⟨i.val, h⟩ else last) ∈
          T.G.res xs ++ [last] ++ T.G last
      by_cases h : i.val < k
      · rw [dite_eq_left h]
        exact List.mem_append_left (T.G last)
          (List.mem_append_left [last] (ih ⟨i.val, h⟩))
      · rw [dite_eq_right h]
        exact List.mem_append_left (T.G last)
          (List.mem_append_right (T.G.res xs)
            (List.mem_singleton_self last))

theorem Vec.Gres_mem_G_of_idx {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m)
    (y : T lam) (hy : y ∈ T.G (v.idx i)) :
    y ∈ T.G.res v := by
  induction v with
  | nil =>
      exact i.elim0
  | snoc k xs last ih =>
      change
        y ∈ T.G.res xs ++ [last] ++ T.G last
      by_cases h : i.val < k
      · have hy' : y ∈ T.G (Vec.idx xs ⟨i.val, h⟩) := by
          change
            y ∈ T.G
              (if h' : i.val < k then
                Vec.idx xs ⟨i.val, h'⟩ else last) at hy
          rw [dite_eq_left h] at hy
          exact hy
        exact List.mem_append_left (T.G last)
          (List.mem_append_left [last]
            (ih ⟨i.val, h⟩ hy'))
      · have hy' : y ∈ T.G last := by
          change
            y ∈ T.G
              (if h' : i.val < k then
                Vec.idx xs ⟨i.val, h'⟩ else last) at hy
          rw [dite_eq_right h] at hy
          exact hy
        exact List.mem_append_right (T.G.res xs ++ [last]) hy'

theorem Vec.Gres_cases {lam m : Nat}
    (v : Vec (T lam) m) (y : T lam)
    (hy : y ∈ T.G.res v) :
    ∃ i : Fin m, y = v.idx i ∨ y ∈ T.G (v.idx i) := by
  induction v with
  | nil =>
      cases hy
  | snoc k xs last ih =>
      change y ∈ T.G.res xs ++ [last] ++ T.G last at hy
      cases List.mem_append.mp hy with
      | inl hleft =>
        cases List.mem_append.mp hleft with
        | inl hxs =>
          obtain ⟨i, hcase⟩ := ih hxs
          refine ⟨i.castSucc, ?_⟩
          have hidx :
              (Vec.snoc k xs last).idx i.castSucc =
                xs.idx i := by
            show
              (if h : i.val < k then
                Vec.idx xs ⟨i.val, h⟩ else last) =
                xs.idx i
            rw [dite_eq_left i.isLt]
          rw [hidx]
          exact hcase
        | inr hlast =>
          have hylast : y = last := List.mem_singleton.mp hlast
          refine ⟨Fin.last k, Or.inl ?_⟩
          have hidx :
              (Vec.snoc k xs last).idx (Fin.last k) = last := by
            show
              (if h : k < k then
                Vec.idx xs ⟨k, h⟩ else last) = last
            rw [dite_eq_right (Nat.lt_irrefl k)]
          rw [hidx]
          exact hylast
      | inr hG =>
        refine ⟨Fin.last k, Or.inr ?_⟩
        have hidx :
            (Vec.snoc k xs last).idx (Fin.last k) = last := by
          show
            (if h : k < k then
              Vec.idx xs ⟨k, h⟩ else last) = last
          rw [dite_eq_right (Nat.lt_irrefl k)]
        rw [hidx]
        exact hG

theorem T.mem_G_P {lam : Nat}
    (ls : Vec (T lam) lam) (add y : T lam) :
    y ∈ T.G (T.P ls add) ↔
      (∃ i : Fin lam,
        y = ls.idx i ∨ y ∈ T.G (ls.idx i)) ∨
      y ∈ T.G add := by
  constructor
  · intro hy
    rw [T.G_P_eq] at hy
    cases List.mem_append.mp hy with
    | inl hres =>
      exact Or.inl (Vec.Gres_cases ls y hres)
    | inr hadd =>
      exact Or.inr hadd
  · intro hy
    rw [T.G_P_eq]
    cases hy with
    | inl hcoord =>
      obtain ⟨i, hcase⟩ := hcoord
      apply List.mem_append_left (T.G add)
      cases hcase with
      | inl heq =>
        rw [heq]
        exact Vec.Gres_mem_of_idx ls i
      | inr hG =>
        exact Vec.Gres_mem_G_of_idx ls i y hG
    | inr hadd =>
      exact List.mem_append_right (T.G.res ls) hadd

inductive T.isNF {lam : Nat} : T lam → Prop where
| z : isNF Z
| p (ls : Vec (T lam) lam) (add : T lam)
  (h0 : ∀ x ∈ Vec.toList ls, isNF x) (h1 : isNF add)
  (h2 : ∀ x ∈ Vec.toList ls, ∀ y ∈ G x, y < x)
  (h3 : head add ≤ P ls Z) : isNF (P ls add)

def T.decForallMem {lam : Nat} (l : List (T lam))
    (P : T lam → Prop) (dP : ∀ x, Decidable (P x)) :
    Decidable (∀ x ∈ l, P x) :=
  match l with
  | [] =>
      isTrue (fun x hx => by cases hx)
  | a :: as =>
      match dP a with
      | isFalse hna =>
          isFalse (fun h => hna (h a List.mem_cons_self))
      | isTrue ha =>
          match T.decForallMem as P dP with
          | isFalse hnas =>
              isFalse (fun h =>
                hnas (fun x hx => h x (List.mem_cons_of_mem a hx)))
          | isTrue has =>
              isTrue (fun x hx =>
                match List.mem_cons.mp hx with
                | Or.inl hxa => hxa ▸ ha
                | Or.inr hxs => has x hxs)

def T.decGCondition {lam : Nat} (x : T lam) :
    Decidable (∀ y ∈ T.G x, y < x) :=
  T.decForallMem (T.G x) (fun y => y < x)
    (fun y => inferInstanceAs (Decidable (T.lt y x)))

mutual
  def T.decIsNF {lam : Nat} : (s : T lam) → Decidable (T.isNF s)
    | .Z => isTrue T.isNF.z
    | .P ls add =>
      match Vec.decAllNF ls with
      | isFalse hn0 =>
          isFalse (fun h =>
            match h with
            | .p _ _ h0 _ _ _ => hn0 h0)
      | isTrue h0 =>
        match T.decIsNF add with
        | isFalse hn1 =>
            isFalse (fun h =>
              match h with
              | .p _ _ _ h1 _ _ => hn1 h1)
        | isTrue h1 =>
          match Vec.decAllG ls with
          | isFalse hn2 =>
              isFalse (fun h =>
                match h with
                | .p _ _ _ _ h2 _ => hn2 h2)
          | isTrue h2 =>
            match (inferInstanceAs
              (Decidable (T.le (T.head add) (T.P ls T.Z))) :
              Decidable (T.head add ≤ T.P ls T.Z)) with
            | isFalse hn3 =>
                isFalse (fun h =>
                  match h with
                  | .p _ _ _ _ _ h3 => hn3 h3)
            | isTrue h3 =>
                isTrue (T.isNF.p ls add h0 h1 h2 h3)

  def Vec.decAllNF {lam m : Nat} :
      (v : Vec (T lam) m) →
        Decidable (∀ x ∈ Vec.toList v, T.isNF x)
    | .nil =>
        isTrue (fun x hx => by cases hx)
    | .snoc _ xs x =>
      match Vec.decAllNF xs with
      | isFalse hnxs =>
          isFalse (fun h =>
            hnxs (fun y hy =>
              h y (List.mem_append_left [x] hy)))
      | isTrue hxs =>
        match T.decIsNF x with
        | isFalse hnx =>
            isFalse (fun h =>
              hnx (h x
                (List.mem_append_right (Vec.toList xs)
                  (List.mem_singleton_self x))))
        | isTrue hx =>
            isTrue (fun y hy =>
              match List.mem_append.mp hy with
              | Or.inl hmem => hxs y hmem
              | Or.inr hmem =>
                  have heq : y = x := List.mem_singleton.mp hmem
                  heq ▸ hx)

  def Vec.decAllG {lam m : Nat} :
      (v : Vec (T lam) m) →
        Decidable
          (∀ x ∈ Vec.toList v, ∀ y ∈ T.G x, y < x)
    | .nil =>
        isTrue (fun x hx => by cases hx)
    | .snoc _ xs x =>
      match Vec.decAllG xs with
      | isFalse hnxs =>
          isFalse (fun h =>
            hnxs (fun z hz =>
              h z (List.mem_append_left [x] hz)))
      | isTrue hxs =>
        match T.decGCondition x with
        | isFalse hnx =>
            isFalse (fun h =>
              hnx (h x
                (List.mem_append_right (Vec.toList xs)
                  (List.mem_singleton_self x))))
        | isTrue hx =>
            isTrue (fun z hz =>
              match List.mem_append.mp hz with
              | Or.inl hmem => hxs z hmem
              | Or.inr hmem =>
                  have heq : z = x := List.mem_singleton.mp hmem
                  heq ▸ hx)
end

instance {lam : Nat} (s : T lam) : Decidable (T.isNF s) :=
  T.decIsNF s


def T.isNFComp {lam : Nat} (s : T lam) : Prop :=
  T.isNF s ∧ ∀ y ∈ T.G s, y < s

theorem T.isNFComp_Z {lam : Nat} :
    T.isNFComp (T.Z : T lam) := by
  constructor
  · exact T.isNF.z
  · intro y hy
    change y ∈ ([] : List (T lam)) at hy
    cases hy

theorem T.isNF_P_coord_NFComp {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNF (T.P ls add)) :
    ∀ i : Fin lam, T.isNFComp (ls.idx i) := by
  intro i
  cases hs with
  | p _ _ h0 h1 h2 h3 =>
    have hmem : ls.idx i ∈ Vec.toList ls :=
      Vec.idx_mem_toList ls i
    exact ⟨h0 (ls.idx i) hmem,
      h2 (ls.idx i) hmem⟩

theorem T.isNF_PZ_of_coords {lam : Nat}
    (ls : Vec (T lam) lam)
    (h : ∀ i : Fin lam, T.isNFComp (ls.idx i)) :
    T.isNF (T.P ls T.Z) := by
  apply T.isNF.p ls T.Z
  · intro x hx
    obtain ⟨i, hi⟩ := Vec.mem_toList_exists_idx ls x hx
    rw [← hi]
    exact (h i).1
  · exact T.isNF.z
  · intro x hx y hy
    obtain ⟨i, hi⟩ := Vec.mem_toList_exists_idx ls x hx
    rw [← hi] at hy
    have hlt := (h i).2 y hy
    rw [hi] at hlt
    exact hlt
  · exact Or.inl rfl

theorem T.coord_lt_of_NFComp_P {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNFComp (T.P ls add)) :
    ∀ i : Fin lam, ls.idx i < T.P ls add := by
  intro i
  apply hs.2 (ls.idx i)
  apply (T.mem_G_P ls add (ls.idx i)).mpr
  exact Or.inl ⟨i, Or.inl rfl⟩

theorem T.fund_omega_NFComp_closed {lam : Nat} (s t : T lam)
    (hs : T.isNFComp s)
    (hd : T.dom s = .omega) :
    T.isNFComp (T.fund s t) := by
  sorry

theorem T.fund_iter_NFComp {lam : Nat} (s t : T lam)
    (hs : T.isNFComp s)
    (hd : T.dom s = .Omega) :
    T.isNFComp
      (T.fund s (T.iter (fun x => T.fund s x) t)) := by
  sorry

theorem T.fund_NF_closed {lam : Nat} (s t : T lam)
    (hs : T.isNF s)
    (ht : T.dom s = .Omega → T.isNFComp t) :
    T.isNF (T.fund s t) := by
  sorry

end new
