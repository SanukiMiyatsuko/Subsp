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
                    Vec.idx as ⟨q.val, h⟩ else aLast) =
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
              have haI :
                  (Vec.snoc k as aLast).idx i = as.idx i' := by
                show
                  (if h : i.val < k then
                    Vec.idx as ⟨i.val, h⟩ else aLast) =
                    Vec.idx as i'
                rw [dite_eq_left hiklt]
              have hnI :
                  (Vec.snoc k ns nLast).idx i = ns.idx i' := by
                show
                  (if h : i.val < k then
                    Vec.idx ns ⟨i.val, h⟩ else nLast) =
                    Vec.idx ns i'
                rw [dite_eq_left hiklt]
              have hpivot' :
                  as.idx i' < ns.idx i' := by
                rw [haI, hnI] at hpivot
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

theorem T.term_lt_P_of_self_at {lam : Nat}
    (x : T lam) (v w : Vec (T lam) lam)
    (q : Fin lam)
    (hx : T.isNFComp x)
    (hold : x < T.P v T.Z)
    (hwq : w.idx q = x)
    (hhigh : ∀ j : Fin lam, q.val < j.val →
      w.idx j = v.idx j) :
    x < T.P w T.Z := by
  cases x with
  | Z =>
      rfl
  | P xs xadd =>
    have hvlt : compareVec xs v = Ordering.lt := by
      change
        (match compareVec xs v with
        | Ordering.eq => compareT xadd T.Z
        | ord => ord) = Ordering.lt at hold
      cases hc : compareVec xs v with
      | lt =>
          rfl
      | eq =>
          rw [hc] at hold
          cases xadd with
          | Z =>
              rw [T_refl T.Z] at hold
              cases hold
          | P als aadd =>
              cases hold
      | gt =>
          rw [hc] at hold
          cases hold
    obtain ⟨p, hpAbove, hpLt⟩ :=
      Vec.compare_lt_has_pivot xs v hvlt
    by_cases hqp : q.val < p.val
    · have hcmp : compareVec xs w = Ordering.lt := by
        apply Vec.compare_lt_of_pivot xs w p
        · intro j hpj
          have hqj : q.val < j.val :=
            Nat.lt_trans hqp hpj
          rw [hhigh j hqj]
          exact hpAbove j hpj
        · have hpw : w.idx p = v.idx p :=
            hhigh p hqp
          rw [hpw]
          exact hpLt
      exact T.P_lt_P_of_compareVec_lt
        xs w xadd T.Z hcmp
    · have hpq : p.val ≤ q.val :=
        Nat.not_lt.mp hqp
      have hself :
          xs.idx q < T.P xs xadd := by
        apply hx.2 (xs.idx q)
        apply (T.mem_G_P xs xadd (xs.idx q)).mpr
        exact Or.inl ⟨q, Or.inl rfl⟩
      have hcmp : compareVec xs w = Ordering.lt := by
        apply Vec.compare_lt_of_pivot xs w q
        · intro j hqj
          have hpj : p.val < j.val :=
            Nat.lt_of_le_of_lt hpq hqj
          rw [hhigh j hqj]
          exact hpAbove j hpj
        · rw [hwq]
          exact hself
      exact T.P_lt_P_of_compareVec_lt
        xs w xadd T.Z hcmp

theorem T.rplc_min_NFComp_closed {lam : Nat}
    (ls : Vec (T lam) lam) (m : Fin lam)
    (d : Dom) (a : T lam)
    (hs : T.isNFComp (T.P ls T.Z))
    (hmin : T.domVecMinIdx ls = some (m, d))
    (ha : T.isNFComp a)
    (halt : a < ls.idx m) :
    T.isNFComp (T.P (ls.rplc m a) T.Z) := by
  have hspec :=
    T.domVecMinIdx_some_spec ls m d hmin
  have holdCoord :=
    T.isNF_P_coord_NFComp ls T.Z hs.1
  have hcoord :
      ∀ i : Fin lam,
        T.isNFComp ((ls.rplc m a).idx i) := by
    intro i
    by_cases him : i.val = m.val
    · have hieq : i = m :=
        Fin.eq_of_val_eq him
      rw [hieq, Vec.rplc_idx_same]
      exact ha
    · rw [Vec.rplc_idx_of_ne ls m i a him]
      exact holdCoord i
  have hnf :
      T.isNF (T.P (ls.rplc m a) T.Z) :=
    T.isNF_PZ_of_coords (ls.rplc m a) hcoord
  constructor
  · exact hnf
  · intro y hy
    cases
      (T.mem_G_P (ls.rplc m a) T.Z y).mp hy with
    | inl hv =>
      obtain ⟨i, hcase⟩ := hv
      have hilt :
          (ls.rplc m a).idx i <
            T.P (ls.rplc m a) T.Z := by
        by_cases him : i.val < m.val
        · have hdom0 :
              T.dom (ls.idx i) = .zero :=
            hspec.2.2 i him
          have hzi : ls.idx i = T.Z :=
            T.dom_zero_eq_Z (ls.idx i) hdom0
          have hine : i.val ≠ m.val :=
            Nat.ne_of_lt him
          have hr :
              (ls.rplc m a).idx i = ls.idx i :=
            Vec.rplc_idx_of_ne ls m i a hine
          rw [hr, hzi]
          rfl
        · by_cases hmi : m.val < i.val
          · have hine : i.val ≠ m.val :=
              Nat.ne_of_gt hmi
            have hr :
                (ls.rplc m a).idx i = ls.idx i :=
              Vec.rplc_idx_of_ne ls m i a hine
            have holdLt :
                ls.idx i < T.P ls T.Z := by
              apply hs.2 (ls.idx i)
              apply
                (T.mem_G_P ls T.Z
                  (ls.idx i)).mpr
              exact Or.inl ⟨i, Or.inl rfl⟩
            have hhigh :
                ∀ j : Fin lam, i.val < j.val →
                  (ls.rplc m a).idx j =
                    ls.idx j := by
              intro j hij
              have hmj : m.val < j.val :=
                Nat.lt_trans hmi hij
              exact Vec.rplc_idx_of_ne
                ls m j a (Nat.ne_of_gt hmj)
            have hb :=
              T.term_lt_P_of_self_at
                (ls.idx i) ls (ls.rplc m a) i
                (holdCoord i) holdLt hr hhigh
            rw [hr]
            exact hb
          · have himle : i.val ≤ m.val :=
              Nat.not_lt.mp hmi
            have hmile : m.val ≤ i.val :=
              Nat.not_lt.mp him
            have hval : i.val = m.val :=
              Nat.le_antisymm himle hmile
            have hieq : i = m :=
              Fin.eq_of_val_eq hval
            rw [hieq]
            have hr :
                (ls.rplc m a).idx m = a :=
              Vec.rplc_idx_same ls m a
            have holdLt :
                ls.idx m < T.P ls T.Z := by
              apply hs.2 (ls.idx m)
              apply
                (T.mem_G_P ls T.Z
                  (ls.idx m)).mpr
              exact Or.inl ⟨m, Or.inl rfl⟩
            have haold :
                a < T.P ls T.Z :=
              strict_partial_order.trans
                a (ls.idx m) (T.P ls T.Z)
                halt holdLt
            have hhigh :
                ∀ j : Fin lam, m.val < j.val →
                  (ls.rplc m a).idx j =
                    ls.idx j := by
              intro j hmj
              exact Vec.rplc_idx_of_ne
                ls m j a (Nat.ne_of_gt hmj)
            rw [hr]
            exact
              T.term_lt_P_of_self_at
                a ls (ls.rplc m a) m
                ha haold hr hhigh
      cases hcase with
      | inl heq =>
          rw [heq]
          exact hilt
      | inr hyg =>
          have hyi :
              y < (ls.rplc m a).idx i :=
            (hcoord i).2 y hyg
          exact strict_partial_order.trans
            y ((ls.rplc m a).idx i)
            (T.P (ls.rplc m a) T.Z)
            hyi hilt
    | inr hz =>
      change y ∈ ([] : List (T lam)) at hz
      cases hz

theorem Vec.mem_toList_iff_idx {A : Type} {n : Nat}
    (v : Vec A n) (x : A) :
    x ∈ Vec.toList v ↔ ∃ i : Fin n, v.idx i = x := by
  constructor
  · intro hx
    exact Vec.mem_toList_exists_idx v x hx
  · intro h
    obtain ⟨i, hi⟩ := h
    rw [← hi]
    exact Vec.idx_mem_toList v i

theorem T.P_tail_lt {lam : Nat} (ls : Vec (T lam) lam)
    (a b : T lam) (h : a < b) :
    T.P ls a < T.P ls b := by
  show
    (match compareVec ls ls with
    | Ordering.eq => compareT a b
    | ord => ord) = Ordering.lt
  rw [Vec_refl ls]
  exact h

theorem T.le_refl {lam : Nat} (a : T lam) : a ≤ a := by
  exact Or.inr (T_refl a)

theorem T.le_trans {lam : Nat} (a b c : T lam)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases hab with
  | inl hablt =>
    cases hbc with
    | inl hbclt =>
      exact Or.inl (T_trans a b c hablt hbclt)
    | inr hbceq =>
      have hbcEq : b = c := T_eq_sound b c hbceq
      rw [← hbcEq]
      exact Or.inl hablt
  | inr habeq =>
    have habEq : a = b := T_eq_sound a b habeq
    rw [habEq]
    exact hbc

theorem T.le_antisymm {lam : Nat} (a b : T lam)
    (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases hab with
  | inr habeq =>
    exact T_eq_sound a b habeq
  | inl hablt =>
    cases hba with
    | inr hbaeq =>
      exact (T_eq_sound b a hbaeq).symm
    | inl hbalt =>
      have haa : a < a :=
        T_trans a b a hablt hbalt
      exact False.elim
        (strict_partial_order.irrefl a haa)

theorem T.P_le_P_same {lam : Nat} (ls : Vec (T lam) lam)
    (a b : T lam) (h : a ≤ b) :
    T.P ls a ≤ T.P ls b := by
  cases h with
  | inl hlt =>
    exact Or.inl (T.P_tail_lt ls a b hlt)
  | inr heq =>
    have hab : a = b := T_eq_sound a b heq
    rw [hab]
    exact T.le_refl (T.P ls b)

theorem T.isNF_G_isNFComp {lam : Nat} (s : T lam)
    (hs : T.isNF s) :
    ∀ x ∈ T.G s, T.isNFComp x := by
  induction hs with
  | z =>
    intro x hx
    change x ∈ ([] : List (T lam)) at hx
    cases hx
  | p ls add h0 h1 h2 h3 ih0 ih1 =>
    intro x hx
    cases (T.mem_G_P ls add x).mp hx with
    | inl hv =>
      obtain ⟨i, hcase⟩ := hv
      cases hcase with
      | inl hxq =>
        rw [hxq]
        have hmem := Vec.idx_mem_toList ls i
        exact ⟨h0 (ls.idx i) hmem, h2 (ls.idx i) hmem⟩
      | inr hxG =>
        have hmem := Vec.idx_mem_toList ls i
        exact ih0 (ls.idx i) hmem x hxG
    | inr hxG =>
      exact ih1 x hxG

theorem T.head_mono_le {lam : Nat} (a b : T lam)
    (h : a ≤ b) : T.head a ≤ T.head b := by
  cases h with
  | inl hlt =>
    exact T.head_mono a b hlt
  | inr heq =>
    have hab : a = b := T_eq_sound a b heq
    rw [hab]
    exact T.le_refl (T.head b)

theorem T.P_same_le_iff {lam : Nat} (ls : Vec (T lam) lam)
    (a b : T lam) :
    T.P ls a ≤ T.P ls b ↔ a ≤ b := by
  constructor
  · intro h
    cases h with
    | inl hlt =>
      apply Or.inl
      change
        (match compareVec ls ls with
        | Ordering.eq => compareT a b
        | ord => ord) = Ordering.lt at hlt
      rw [Vec_refl ls] at hlt
      exact hlt
    | inr heq =>
      apply Or.inr
      have hpEq : T.P ls a = T.P ls b :=
        T_eq_sound (T.P ls a) (T.P ls b) heq
      injection hpEq with _ hadd
      rw [hadd]
      exact T_refl b
  · intro h
    exact T.P_le_P_same ls a b h

theorem T.sandwich_same_vector {lam : Nat}
    (ls : Vec (T lam) lam) (a b c : T lam)
    (hab : a ≤ b)
    (hl : T.P ls a ≤ c)
    (hu : c ≤ T.P ls b) :
    ∃ d, c = T.P ls d ∧ a ≤ d ∧ d ≤ b := by
  have hheadL :
      T.P ls T.Z ≤ T.head c :=
    T.head_mono_le (T.P ls a) c hl
  have hheadU :
      T.head c ≤ T.P ls T.Z :=
    T.head_mono_le c (T.P ls b) hu
  have hheadEq :
      T.head c = T.P ls T.Z :=
    T.le_antisymm (T.head c) (T.P ls T.Z)
      hheadU hheadL
  cases c with
  | Z =>
    change T.Z = T.P ls T.Z at hheadEq
    cases hheadEq
  | P cs d =>
    change T.P cs T.Z = T.P ls T.Z at hheadEq
    injection hheadEq with hcs
    subst cs
    refine ⟨d, rfl, ?_, ?_⟩
    · exact (T.P_same_le_iff ls a d).mp hl
    · exact (T.P_same_le_iff ls d b).mp hu

theorem T.vector_rel_of_P_le_P {lam : Nat}
    (v w : Vec (T lam) lam) (a b : T lam)
    (h : T.P v a ≤ T.P w b) :
    compareVec v w = Ordering.lt ∨ v = w := by
  cases h with
  | inl hlt =>
    change
      (match compareVec v w with
      | Ordering.eq => compareT a b
      | ord => ord) = Ordering.lt at hlt
    cases hc : compareVec v w with
    | lt =>
      exact Or.inl rfl
    | eq =>
      exact Or.inr (Vec_eq_sound v w hc)
    | gt =>
      rw [hc] at hlt
      cases hlt
  | inr heq =>
    have hpEq : T.P v a = T.P w b :=
      T_eq_sound (T.P v a) (T.P w b) heq
    injection hpEq with hv
    exact Or.inr hv

theorem T.lt_of_le_of_lt {lam : Nat} (a b c : T lam)
    (hab : a ≤ b) (hbc : b < c) : a < c := by
  cases hab with
  | inl hablt =>
    exact T_trans a b c hablt hbc
  | inr habeq =>
    have habEq : a = b := T_eq_sound a b habeq
    rw [habEq]
    exact hbc

theorem T.lt_of_lt_of_le {lam : Nat} (a b c : T lam)
    (hab : a < b) (hbc : b ≤ c) : a < c := by
  cases hbc with
  | inl hbclt =>
    exact T_trans a b c hab hbclt
  | inr hbceq =>
    have hbcEq : b = c := T_eq_sound b c hbceq
    rw [← hbcEq]
    exact hab

def T.ZeroDom {lam : Nat} (b a : T lam) : Prop :=
  b < a ∧
    ∀ c : T lam, b ≤ c → c ≤ a →
      ∀ x ∈ T.G b,
        ∃ y : T lam, y ∈ T.G c ++ [T.Z] ∧ x ≤ y

theorem T.ZeroDom_tail {lam : Nat}
    (ls : Vec (T lam) lam) (a b : T lam)
    (hdom : T.ZeroDom b a) :
    T.ZeroDom (T.P ls b) (T.P ls a) := by
  constructor
  · exact T.P_tail_lt ls b a hdom.1
  · intro c hbc hca x hx
    obtain ⟨d, hceq, hbd, hda⟩ :=
      T.sandwich_same_vector ls b a c
        (Or.inl hdom.1) hbc hca
    rw [hceq]
    cases (T.mem_G_P ls b x).mp hx with
    | inl hvec =>
      refine ⟨x, ?_, T.le_refl x⟩
      apply List.mem_append_left [T.Z]
      apply (T.mem_G_P ls d x).mpr
      exact Or.inl hvec
    | inr htail =>
      obtain ⟨y, hy, hxy⟩ :=
        hdom.2 d hbd hda x htail
      refine ⟨y, ?_, hxy⟩
      cases List.mem_append.mp hy with
      | inl hGd =>
        apply List.mem_append_left [T.Z]
        apply (T.mem_G_P ls d y).mpr
        exact Or.inr hGd
      | inr hZ =>
        exact List.mem_append_right
          (T.G (T.P ls d)) hZ

theorem T.NFComp_of_ZeroDom {lam : Nat}
    (a b : T lam) (hb : T.isNF b)
    (ha : T.isNFComp a) (hdom : T.ZeroDom b a) :
    T.isNFComp b := by
  by_cases hbz : b = T.Z
  · rw [hbz]
    exact T.isNFComp_Z
  · have hzb : T.Z < b := by
      cases T.Z_le b with
      | inl hlt =>
        exact hlt
      | inr heq =>
        have hzEq : T.Z = b :=
          T_eq_sound T.Z b heq
        exact False.elim (hbz hzEq.symm)
    constructor
    · exact hb
    · intro x hx
      have hba : b ≤ a := Or.inl hdom.1
      have haa : a ≤ a := T.le_refl a
      obtain ⟨w, hw, hxw⟩ :=
        hdom.2 a hba haa x hx
      have hwa : w < a := by
        cases List.mem_append.mp hw with
        | inl hGa =>
          exact ha.2 w hGa
        | inr hZ =>
          have hwz : w = T.Z :=
            List.mem_singleton.mp hZ
          rw [hwz]
          exact T_trans T.Z b a hzb hdom.1
      have hxa : x < a :=
        T.lt_of_le_of_lt x w a hxw hwa
      by_cases hxb : x < b
      · exact hxb
      · have hbx : b ≤ x := by
          cases T_total b x with
          | inl hlt =>
            exact Or.inl hlt
          | inr hr =>
            cases hr with
            | inl hlt =>
              exact False.elim (hxb hlt)
            | inr heq =>
              rw [heq]
              exact T.le_refl x
        obtain ⟨v, hv, hxv⟩ :=
          hdom.2 x hbx (Or.inl hxa) x hx
        have hvx : v < x := by
          cases List.mem_append.mp hv with
          | inl hGx =>
            have hxc : T.isNFComp x :=
              T.isNF_G_isNFComp b hb x hx
            exact hxc.2 v hGx
          | inr hZ =>
            have hvz : v = T.Z :=
              List.mem_singleton.mp hZ
            rw [hvz]
            exact T.lt_of_lt_of_le T.Z b x hzb hbx
        have hxx : x < x :=
          T.lt_of_le_of_lt x v x hxv hvx
        exact False.elim
          (strict_partial_order.irrefl x hxx)

theorem T.fund_one_master {lam : Nat} (s : T lam) :
    ∀ (hs : T.isNF s), T.dom s = .one →
      T.isNF (T.fund s T.Z) ∧
        T.ZeroDom (T.fund s T.Z) s := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ a : T lam, T.size a = n →
        T.isNF a → T.dom a = .one →
          T.isNF (T.fund a T.Z) ∧
            T.ZeroDom (T.fund a T.Z) a
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a hn hs hd
      cases a with
      | Z =>
        cases hd
      | P ls add =>
        cases hs with
        | p _ _ h0 h1 h2 h3 =>
          by_cases hadd : add = T.Z
          · subst add
            have hnone : T.domVecMinIdx ls = none := by
              cases hmin : T.domVecMinIdx ls with
              | none =>
                rfl
              | some md =>
                obtain ⟨m, d⟩ := md
                have hd' := hd
                conv at hd' =>
                  lhs
                  rw [T.dom, if_pos rfl]
                  rw [hmin]
                change
                  (if d = Dom.one then
                    if m.val = 0 then Dom.omega else Dom.Omega
                  else Dom.omega) = Dom.one at hd'
                by_cases hd1 : d = .one
                · rw [if_pos hd1] at hd'
                  by_cases hm0 : m.val = 0
                  · rw [if_pos hm0] at hd'
                    cases hd'
                  · rw [if_neg hm0] at hd'
                    cases hd'
                · rw [if_neg hd1] at hd'
                  cases hd'
            rw [T.fund_PZ_none ls T.Z hnone]
            constructor
            · exact T.isNF.z
            · constructor
              · rfl
              · intro c hzc hcs x hx
                change x ∈ ([] : List (T lam)) at hx
                cases hx
          · have hdadd : T.dom add = .one := by
              rw [T.dom, if_neg hadd] at hd
              exact hd
            have hsz : T.size add < n := by
              rw [← hn]
              exact T.add_size_lt_P ls add
            obtain ⟨hnf, hrel⟩ :=
              ih (T.size add) hsz add rfl h1 hdadd
            rw [T.fund, if_neg hadd]
            constructor
            · apply T.isNF.p ls (T.fund add T.Z)
              · exact h0
              · exact hnf
              · exact h2
              · exact T.le_trans
                  (T.head (T.fund add T.Z))
                  (T.head add) (T.P ls T.Z)
                  (T.head_fund_le add T.Z) h3
            · exact T.ZeroDom_tail ls add
                (T.fund add T.Z) hrel)
  intro hs hd
  exact main (T.size s) s rfl hs hd

theorem T.fund_one_NFComp_closed {lam : Nat} (s : T lam)
    (hs : T.isNFComp s) (hd : T.dom s = .one) :
    T.isNFComp (T.fund s T.Z) := by
  obtain ⟨hnf, hdom⟩ :=
    T.fund_one_master s hs.1 hd
  exact T.NFComp_of_ZeroDom
    s (T.fund s T.Z) hnf hs hdom

def T.GZ {lam : Nat} (z : T lam) : List (T lam) :=
  [z] ++ T.G z ++ [T.Z]

def T.listLe {lam : Nat} (xs ys : List (T lam)) : Prop :=
  ∀ x, x ∈ xs → ∃ y, y ∈ ys ∧ x ≤ y

def T.SDom {lam : Nat} (z b a : T lam) : Prop :=
  b < a ∧
    ∀ c, b ≤ c → c ≤ a →
      T.listLe (T.G b) (T.G c ++ T.GZ z)

theorem T.G_size_lt {lam : Nat} :
    ∀ s y : T lam, y ∈ T.G s → T.size y < T.size s := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ s y : T lam, T.size s = n →
        y ∈ T.G s → T.size y < T.size s
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro s y hsize hy
      cases s with
      | Z =>
        change y ∈ ([] : List (T lam)) at hy
        cases hy
      | P ls add =>
        cases (T.mem_G_P ls add y).mp hy with
        | inl hv =>
          obtain ⟨i, hcase⟩ := hv
          have hidx :
              T.size (ls.idx i) <
                T.size (T.P ls add) := by
            rw [← Vec.getElem_eq_idx ls i]
            exact T.idx_size_lt_P ls add i
          cases hcase with
          | inl heq =>
            rw [heq]
            exact hidx
          | inr hG =>
            have hidxn : T.size (ls.idx i) < n := by
              rw [hsize] at hidx
              exact hidx
            have hrec :
                T.size y < T.size (ls.idx i) :=
              ih (T.size (ls.idx i)) hidxn
                (ls.idx i) y rfl hG
            exact Nat.lt_trans hrec hidx
        | inr hGadd =>
          have hadd :
              T.size add < T.size (T.P ls add) :=
            T.add_size_lt_P ls add
          have haddn : T.size add < n := by
            rw [hsize] at hadd
            exact hadd
          have hrec :
              T.size y < T.size add :=
            ih (T.size add) haddn add y rfl hGadd
          exact Nat.lt_trans hrec
            (T.add_size_lt_P ls add))
  intro s y hy
  exact main (T.size s) s y rfl hy

theorem T.G_trans {lam : Nat} :
    ∀ a x y : T lam,
      x ∈ T.G a → y ∈ T.G x → y ∈ T.G a := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ a x y : T lam, T.size a = n →
        x ∈ T.G a → y ∈ T.G x → y ∈ T.G a
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a x y hsize hx hy
      cases a with
      | Z =>
        change x ∈ ([] : List (T lam)) at hx
        cases hx
      | P ls add =>
        cases (T.mem_G_P ls add x).mp hx with
        | inl hv =>
          obtain ⟨i, hcase⟩ := hv
          cases hcase with
          | inl heq =>
            rw [heq] at hy
            apply (T.mem_G_P ls add y).mpr
            exact Or.inl ⟨i, Or.inr hy⟩
          | inr hG =>
            have hidx :
                T.size (ls.idx i) <
                  T.size (T.P ls add) := by
              rw [← Vec.getElem_eq_idx ls i]
              exact T.idx_size_lt_P ls add i
            have hidxn : T.size (ls.idx i) < n := by
              rw [hsize] at hidx
              exact hidx
            have hyr : y ∈ T.G (ls.idx i) :=
              ih (T.size (ls.idx i)) hidxn
                (ls.idx i) x y rfl hG hy
            apply (T.mem_G_P ls add y).mpr
            exact Or.inl ⟨i, Or.inr hyr⟩
        | inr hGadd =>
          have hadd :
              T.size add < T.size (T.P ls add) :=
            T.add_size_lt_P ls add
          have haddn : T.size add < n := by
            rw [hsize] at hadd
            exact hadd
          have hyr : y ∈ T.G add :=
            ih (T.size add) haddn add x y
              rfl hGadd hy
          apply (T.mem_G_P ls add y).mpr
          exact Or.inr hyr)
  intro a x y hx hy
  exact main (T.size a) a x y rfl hx hy

theorem T.exists_G_not_lt {lam : Nat} (s b : T lam)
    (h : ¬ (∀ x ∈ T.G s, x < b)) :
    ∃ x, x ∈ T.G s ∧ ¬ x < b := by
  have main :
      ∀ l : List (T lam),
        ¬ (∀ x ∈ l, x < b) →
        ∃ x, x ∈ l ∧ ¬ x < b := by
    intro l
    induction l with
    | nil =>
      intro hn
      exact False.elim
        (hn (fun x hx => by cases hx))
    | cons a as ih =>
      intro hn
      by_cases ha : a < b
      · have htail : ¬ (∀ x ∈ as, x < b) := by
          intro hall
          apply hn
          intro x hx
          cases List.mem_cons.mp hx with
          | inl heq =>
            rw [heq]
            exact ha
          | inr hmem =>
            exact hall x hmem
        obtain ⟨x, hx, hnx⟩ := ih htail
        exact ⟨x, List.mem_cons_of_mem a hx, hnx⟩
      · exact ⟨a, List.mem_cons_self, ha⟩
  exact main (T.G s) h

theorem T.find_violating_source {lam : Nat}
    (b c₀ w : T lam)
    (hw : w ∈ T.G c₀) (hbw : b ≤ w) :
    ∃ c, c ∈ T.G c₀ ∧ b ≤ c ∧
      ∀ x ∈ T.G c, x < b := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ w : T lam, T.size w = n →
        w ∈ T.G c₀ → b ≤ w →
        ∃ c, c ∈ T.G c₀ ∧ b ≤ c ∧
          ∀ x ∈ T.G c, x < b
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro w hn hw hbw
      by_cases hbound : ∀ x ∈ T.G w, x < b
      · exact ⟨w, hw, hbw, hbound⟩
      · obtain ⟨x, hx, hnx⟩ :=
          T.exists_G_not_lt w b hbound
        have hbx : b ≤ x := by
          cases strict_linear_order.total x b with
          | inl hxb =>
            exact False.elim (hnx hxb)
          | inr hr =>
            cases hr with
            | inl hbx =>
              exact Or.inl hbx
            | inr heq =>
              apply Or.inr
              rw [heq]
              exact T_refl b
        have hxsize : T.size x < n := by
          have hs := T.G_size_lt w x hx
          rw [hn] at hs
          exact hs
        have hxc₀ : x ∈ T.G c₀ :=
          T.G_trans c₀ w x hw hx
        exact ih (T.size x) hxsize x rfl hxc₀ hbx)
  exact main (T.size w) w rfl hw hbw

theorem T.GZ_lt_of_NFComp_lt {lam : Nat}
    (z b : T lam)
    (hz : T.isNFComp z) (hzb : z < b) :
    ∀ x ∈ T.GZ z, x < b := by
  intro x hx
  rw [T.GZ] at hx
  cases List.mem_append.mp hx with
  | inl hleft =>
    cases List.mem_append.mp hleft with
    | inl hzmem =>
      have heq : x = z := List.mem_singleton.mp hzmem
      rw [heq]
      exact hzb
    | inr hG =>
      have hxz : x < z := hz.2 x hG
      exact T_trans x z b hxz hzb
  | inr hzero =>
    have heq : x = T.Z := List.mem_singleton.mp hzero
    rw [heq]
    exact T.lt_of_le_of_lt T.Z z b (T.Z_le z) hzb

theorem T.SDom_G_lt_upper {lam : Nat}
    (z b a : T lam)
    (hs : T.SDom z b a)
    (hGa : ∀ x ∈ T.G a, x < a)
    (hGz : ∀ x ∈ T.GZ z, x < b) :
    ∀ y ∈ T.G b, y < a := by
  intro y hy
  have hba : b ≤ a := Or.inl hs.1
  obtain ⟨w, hw, hyw⟩ :=
    hs.2 a hba (T.le_refl a) y hy
  cases List.mem_append.mp hw with
  | inl hwa =>
    exact T.lt_of_le_of_lt y w a hyw
      (hGa w hwa)
  | inr hwz =>
    have hyltb : y < b :=
      T.lt_of_le_of_lt y w b hyw
        (hGz w hwz)
    exact T_trans y b a hyltb hs.1

theorem T.SDom_G_closed {lam : Nat}
    (z b a : T lam)
    (hs : T.SDom z b a)
    (hGa : ∀ x ∈ T.G a, x < a)
    (hGz : ∀ x ∈ T.GZ z, x < b) :
    ∀ y ∈ T.G b, y < b := by
  intro y hy
  by_cases hyb : y < b
  · exact hyb
  · have hby : b ≤ y := by
      cases strict_linear_order.total y b with
      | inl hylt =>
        exact False.elim (hyb hylt)
      | inr hr =>
        cases hr with
        | inl hblt =>
          exact Or.inl hblt
        | inr heq =>
          apply Or.inr
          rw [← heq]
          exact T_refl y
    obtain ⟨c, hcG, hbc, hcBound⟩ :=
      T.find_violating_source b b y hy hby
    have hca : c < a :=
      T.SDom_G_lt_upper z b a hs hGa hGz c hcG
    obtain ⟨w, hw, hcw⟩ :=
      hs.2 c hbc (Or.inl hca) c hcG
    have hwb : w < b := by
      cases List.mem_append.mp hw with
      | inl hwc =>
        exact hcBound w hwc
      | inr hwz =>
        exact hGz w hwz
    have hcb : c < b :=
      T.lt_of_le_of_lt c w b hcw hwb
    have hbb : b < b :=
      T.lt_of_le_of_lt b c b hbc hcb
    exact False.elim
      (strict_partial_order.irrefl b hbb)

theorem T.NFComp_of_SDom {lam : Nat}
    (z b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp a)
    (hz : T.isNFComp z)
    (hdom : T.SDom z b a)
    (hzb : z < b) :
    T.isNFComp b := by
  constructor
  · exact hb
  · exact T.SDom_G_closed z b a hdom ha.2
      (T.GZ_lt_of_NFComp_lt z b hz hzb)

theorem T.NFComp_of_SDom_Z_or_eq {lam : Nat}
    (b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp a)
    (hdom : T.SDom T.Z b a) :
    T.isNFComp b := by
  by_cases hbz : b = T.Z
  · rw [hbz]
    exact T.isNFComp_Z
  · have hzb : T.Z < b := by
      cases T.Z_le b with
      | inl hlt =>
        exact hlt
      | inr heq =>
        have heq' : T.Z = b :=
          T_eq_sound T.Z b heq
        exact False.elim (hbz heq'.symm)
    exact T.NFComp_of_SDom
      T.Z b a hb ha T.isNFComp_Z hdom hzb

theorem T.rplc_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam) (i : Fin lam) (a : T lam)
    (hs : T.isNF (T.P ls T.Z))
    (ha : T.isNFComp a) :
    T.isNF (T.P (ls.rplc i a) T.Z) := by
  have holdCoord :=
    T.isNF_P_coord_NFComp ls T.Z hs
  apply T.isNF_PZ_of_coords (ls.rplc i a)
  intro q
  by_cases hqi : q.val = i.val
  · have hq : q = i := Fin.eq_of_val_eq hqi
    rw [hq, Vec.rplc_idx_same]
    exact ha
  · rw [Vec.rplc_idx_of_ne ls i q a hqi]
    exact holdCoord q

theorem T.rplc_two_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam) (i j : Fin lam)
    (a b : T lam) (hij : i.val ≠ j.val)
    (hs : T.isNF (T.P ls T.Z))
    (ha : T.isNFComp a) (hb : T.isNFComp b) :
    T.isNF
      (T.P ((ls.rplc i a).rplc j b) T.Z) := by
  have holdCoord :=
    T.isNF_P_coord_NFComp ls T.Z hs
  apply T.isNF_PZ_of_coords
    ((ls.rplc i a).rplc j b)
  intro q
  by_cases hqj : q.val = j.val
  · have hq : q = j := Fin.eq_of_val_eq hqj
    rw [hq, Vec.rplc_idx_same]
    exact hb
  · rw [Vec.rplc_idx_of_ne (ls.rplc i a) j q b hqj]
    by_cases hqi : q.val = i.val
    · have hq : q = i := Fin.eq_of_val_eq hqi
      rw [hq, Vec.rplc_idx_same]
      exact ha
    · rw [Vec.rplc_idx_of_ne ls i q a hqi]
      exact holdCoord q

theorem T.mul_PZ_lt_next {lam : Nat}
    (ls : Vec (T lam) lam) :
    ∀ t : T lam,
      T.mul (T.P ls T.Z) t <
        T.P ls (T.mul (T.P ls T.Z) t) := by
  intro t
  let motive : Nat → Prop :=
    fun n =>
      ∀ u : T lam, T.size u = n →
        T.mul (T.P ls T.Z) u <
          T.P ls (T.mul (T.P ls T.Z) u)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro u hn
      cases u with
      | Z =>
        rw [T.mul]
        rfl
      | P us add =>
        have hsz : T.size add < n := by
          rw [← hn]
          exact T.add_size_lt_P us add
        have hrec :=
          ih (T.size add) hsz add rfl
        rw [T.mul]
        change
          T.P ls (T.mul (T.P ls T.Z) add) <
            T.P ls
              (T.P ls (T.mul (T.P ls T.Z) add))
        exact T.P_tail_lt ls
          (T.mul (T.P ls T.Z) add)
          (T.P ls (T.mul (T.P ls T.Z) add))
          hrec)
  exact main (T.size t) t rfl

theorem T.head_mul_PZ_le {lam : Nat}
    (ls : Vec (T lam) lam) :
    ∀ t : T lam,
      T.head (T.mul (T.P ls T.Z) t) ≤
        T.P ls T.Z := by
  intro t
  cases t with
  | Z =>
    rw [T.mul]
    exact T.Z_le (T.P ls T.Z)
  | P tls add =>
    rw [T.mul]
    change T.P ls T.Z ≤ T.P ls T.Z
    exact T.le_refl (T.P ls T.Z)

theorem T.mul_PZ_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam)
    (hbase : T.isNF (T.P ls T.Z)) :
    ∀ t : T lam,
      T.isNF (T.mul (T.P ls T.Z) t) := by
  intro t
  let motive : Nat → Prop :=
    fun n =>
      ∀ u : T lam, T.size u = n →
        T.isNF (T.mul (T.P ls T.Z) u)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro u hn
      cases u with
      | Z =>
        rw [T.mul]
        exact T.isNF.z
      | P us add =>
        have hsz : T.size add < n := by
          rw [← hn]
          exact T.add_size_lt_P us add
        have hrec :=
          ih (T.size add) hsz add rfl
        rw [T.mul]
        change
          T.isNF
            (T.P ls (T.mul (T.P ls T.Z) add))
        cases hbase with
        | p _ _ h0 hz h2 h3 =>
          exact T.isNF.p ls
            (T.mul (T.P ls T.Z) add)
            h0 hrec h2 (T.head_mul_PZ_le ls add))
  exact main (T.size t) t rfl

theorem T.mul_PZ_NFComp_closed {lam : Nat}
    (ls : Vec (T lam) lam)
    (hbase : T.isNFComp (T.P ls T.Z)) :
    ∀ t : T lam,
      T.isNFComp (T.mul (T.P ls T.Z) t) := by
  intro t
  let motive : Nat → Prop :=
    fun n =>
      ∀ u : T lam, T.size u = n →
        T.isNFComp (T.mul (T.P ls T.Z) u)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro u hn
      cases u with
      | Z =>
        rw [T.mul]
        exact T.isNFComp_Z
      | P us add =>
        have hsz : T.size add < n := by
          rw [← hn]
          exact T.add_size_lt_P us add
        have hrec :=
          ih (T.size add) hsz add rfl
        rw [T.mul]
        change
          T.isNFComp
            (T.P ls (T.mul (T.P ls T.Z) add))
        have hnf :
            T.isNF
              (T.P ls (T.mul (T.P ls T.Z) add)) := by
          cases hbase.1 with
          | p _ _ h0 hz h2 h3 =>
            exact T.isNF.p ls
              (T.mul (T.P ls T.Z) add)
              h0 hrec.1 h2
              (T.head_mul_PZ_le ls add)
        constructor
        · exact hnf
        · intro y hy
          cases
              (T.mem_G_P ls
                (T.mul (T.P ls T.Z) add) y).mp hy with
          | inl hvec =>
            have hybase :
                y ∈ T.G (T.P ls T.Z) := by
              apply (T.mem_G_P ls T.Z y).mpr
              exact Or.inl hvec
            have hya : y < T.P ls T.Z :=
              hbase.2 y hybase
            have hle :
                T.P ls T.Z ≤
                  T.P ls
                    (T.mul (T.P ls T.Z) add) :=
              T.P_le_P_same ls T.Z
                (T.mul (T.P ls T.Z) add)
                (T.Z_le (T.mul (T.P ls T.Z) add))
            exact T.lt_of_lt_of_le y
              (T.P ls T.Z)
              (T.P ls (T.mul (T.P ls T.Z) add))
              hya hle
          | inr htail =>
            have hyu :
                y < T.mul (T.P ls T.Z) add :=
              hrec.2 y htail
            exact T_trans y
              (T.mul (T.P ls T.Z) add)
              (T.P ls (T.mul (T.P ls T.Z) add))
              hyu (T.mul_PZ_lt_next ls add))
  exact main (T.size t) t rfl

theorem T.SDom_tail {lam : Nat}
    (z b a : T lam) (ls : Vec (T lam) lam)
    (hs : T.SDom z b a) :
    T.SDom z (T.P ls b) (T.P ls a) := by
  constructor
  · exact T.P_tail_lt ls b a hs.1
  · intro c hbc hca
    have hba : b ≤ a := Or.inl hs.1
    obtain ⟨d, hcd, hbd, hda⟩ :=
      T.sandwich_same_vector ls b a c hba hbc hca
    rw [hcd]
    intro x hx
    cases (T.mem_G_P ls b x).mp hx with
    | inl hvec =>
      refine ⟨x, ?_, T.le_refl x⟩
      apply List.mem_append_left (T.GZ z)
      apply (T.mem_G_P ls d x).mpr
      exact Or.inl hvec
    | inr htail =>
      obtain ⟨y, hy, hxy⟩ :=
        hs.2 d hbd hda x htail
      cases List.mem_append.mp hy with
      | inl hyd =>
        refine ⟨y, ?_, hxy⟩
        apply List.mem_append_left (T.GZ z)
        apply (T.mem_G_P ls d y).mpr
        exact Or.inr hyd
      | inr hyz =>
        exact
          ⟨y,
            List.mem_append_right (T.G (T.P ls d)) hyz,
            hxy⟩

theorem Vec.interval_pivot_properties {lam m : Nat}
    (low mid high : Vec (T lam) m) (i : Fin m)
    (heqAbove :
      ∀ j : Fin m, i.val < j.val →
        low.idx j = high.idx j)
    (hpivot : low.idx i < high.idx i)
    (hlm : compareVec low mid = Ordering.lt ∨ low = mid)
    (hmh : compareVec mid high = Ordering.lt ∨ mid = high) :
    (∀ j : Fin m, i.val < j.val →
        mid.idx j = high.idx j) ∧
      low.idx i ≤ mid.idx i ∧
      mid.idx i ≤ high.idx i := by
  cases hlm with
  | inr heq =>
    subst mid
    constructor
    · intro j hij
      exact heqAbove j hij
    · constructor
      · exact T.le_refl (low.idx i)
      · exact Or.inl hpivot
  | inl hlt =>
    obtain ⟨p, hpEq, hpLt⟩ :=
      Vec.compare_lt_has_pivot low mid hlt
    have hpi : p.val ≤ i.val := by
      by_cases hip : i.val < p.val
      · cases hmh with
        | inr hmeq =>
          have hmp : mid.idx p = high.idx p := by
            rw [hmeq]
          have hlp : low.idx p = high.idx p :=
            heqAbove p hip
          have hbad : low.idx p < low.idx p := by
            rw [hmp, ← hlp] at hpLt
            exact hpLt
          exact False.elim
            (strict_partial_order.irrefl (low.idx p) hbad)
        | inl hmhlt =>
          obtain ⟨q, hqEq, hqLt⟩ :=
            Vec.compare_lt_has_pivot mid high hmhlt
          cases Nat.lt_trichotomy q.val p.val with
          | inl hqp =>
            have hmp : mid.idx p = high.idx p :=
              hqEq p hqp
            have hlp : low.idx p = high.idx p :=
              heqAbove p hip
            have hbad : low.idx p < low.idx p := by
              rw [hmp, ← hlp] at hpLt
              exact hpLt
            exact False.elim
              (strict_partial_order.irrefl (low.idx p) hbad)
          | inr hrest =>
            cases hrest with
            | inl heqVal =>
              have hpq : p = q :=
                Fin.eq_of_val_eq heqVal.symm
              subst q
              have hlp : low.idx p = high.idx p :=
                heqAbove p hip
              have hcycle : low.idx p < low.idx p := by
                have htrans :=
                  strict_partial_order.trans
                    (low.idx p) (mid.idx p)
                    (high.idx p) hpLt hqLt
                rw [← hlp] at htrans
                exact htrans
              exact False.elim
                (strict_partial_order.irrefl
                  (low.idx p) hcycle)
            | inr hpq =>
              have hiq : i.val < q.val :=
                Nat.lt_trans hip hpq
              have hlq : low.idx q = high.idx q :=
                heqAbove q hiq
              have hlmq : low.idx q = mid.idx q :=
                hpEq q hpq
              have hbad : high.idx q < high.idx q := by
                rw [← hlmq, hlq] at hqLt
                exact hqLt
              exact False.elim
                (strict_partial_order.irrefl
                  (high.idx q) hbad)
      · exact Nat.not_lt.mp hip
    have hhigh :
        ∀ j : Fin m, i.val < j.val →
          mid.idx j = high.idx j := by
      intro j hij
      have hpj : p.val < j.val :=
        Nat.lt_of_le_of_lt hpi hij
      have hlmEq : low.idx j = mid.idx j :=
        hpEq j hpj
      have hlhEq : low.idx j = high.idx j :=
        heqAbove j hij
      exact hlmEq.symm.trans hlhEq
    have hlower : low.idx i ≤ mid.idx i := by
      cases Nat.lt_or_eq_of_le hpi with
      | inl hpiLt =>
        have heq : low.idx i = mid.idx i :=
          hpEq i hpiLt
        rw [heq]
        exact T.le_refl (mid.idx i)
      | inr hpiEq =>
        have hpeqi : p = i :=
          Fin.eq_of_val_eq hpiEq
        rw [hpeqi] at hpLt
        exact Or.inl hpLt
    have hupper : mid.idx i ≤ high.idx i := by
      cases hmh with
      | inr heq =>
        rw [heq]
        exact T.le_refl (high.idx i)
      | inl hltmh =>
        obtain ⟨q, hqEq, hqLt⟩ :=
          Vec.compare_lt_has_pivot mid high hltmh
        have hqi : q.val ≤ i.val := by
          by_cases hiq : i.val < q.val
          · have heqQ : mid.idx q = high.idx q :=
              hhigh q hiq
            have hbad : high.idx q < high.idx q := by
              rw [heqQ] at hqLt
              exact hqLt
            exact False.elim
              (strict_partial_order.irrefl
                (high.idx q) hbad)
          · exact Nat.not_lt.mp hiq
        cases Nat.lt_or_eq_of_le hqi with
        | inl hqiLt =>
          have heq : mid.idx i = high.idx i :=
            hqEq i hqiLt
          rw [heq]
          exact T.le_refl (high.idx i)
        | inr hqiEq =>
          have hqei : q = i :=
            Fin.eq_of_val_eq hqiEq
          rw [hqei] at hqLt
          exact Or.inl hqLt
    exact ⟨hhigh, hlower, hupper⟩

theorem T.SDom_PZ_pivot_comp {lam : Nat}
    (z : T lam)
    (low high : Vec (T lam) lam)
    (i : Fin lam)
    (hAbove :
      ∀ j : Fin lam, i.val < j.val →
        low.idx j = high.idx j)
    (hPivotLt : low.idx i < high.idx i)
    (hPivotComp : T.isNFComp (low.idx i))
    (hBelow :
      ∀ q : Fin lam, q.val < i.val →
        low.idx q = T.Z ∨ low.idx q = z) :
    T.SDom z (T.P low T.Z) (T.P high T.Z) := by
  constructor
  · exact T.P_lt_P_of_compareVec_lt
      low high T.Z T.Z
      (Vec.compare_lt_of_pivot
        low high i hAbove hPivotLt)
  · intro c hlc hch
    cases c with
    | Z =>
      cases hlc with
      | inl hlt =>
        change
          compareT (T.P low T.Z) T.Z =
            Ordering.lt at hlt
        cases hlt
      | inr heq =>
        have hpEq : T.P low T.Z = T.Z :=
          T_eq_sound (T.P low T.Z) T.Z heq
        cases hpEq
    | P mid add =>
      have hLowVec :
          compareVec low mid = Ordering.lt ∨
            low = mid :=
        T.vector_rel_of_P_le_P
          low mid T.Z add hlc
      have hHighVec :
          compareVec mid high = Ordering.lt ∨
            mid = high :=
        T.vector_rel_of_P_le_P
          mid high add T.Z hch
      have hBetween :=
        Vec.interval_pivot_properties
          low mid high i hAbove hPivotLt
          hLowVec hHighVec
      intro x hx
      cases (T.mem_G_P low T.Z x).mp hx with
      | inl hcoord =>
        obtain ⟨q, hqx⟩ := hcoord
        cases Nat.lt_trichotomy q.val i.val with
        | inl hqi =>
          have hlower := hBelow q hqi
          cases hqx with
          | inl hxq =>
            rw [hxq]
            cases hlower with
            | inl hz =>
              rw [hz]
              refine ⟨T.Z, ?_, T.le_refl T.Z⟩
              apply
                List.mem_append_right
                  (T.G (T.P mid add))
              rw [T.GZ]
              exact
                List.mem_append_right
                  ([z] ++ T.G z)
                  (List.mem_singleton_self T.Z)
            | inr hz =>
              rw [hz]
              refine ⟨z, ?_, T.le_refl z⟩
              apply
                List.mem_append_right
                  (T.G (T.P mid add))
              rw [T.GZ]
              exact
                List.mem_append_left
                  (T.G z ++ [T.Z])
                  (List.mem_singleton_self z)
          | inr hG =>
            cases hlower with
            | inl hz =>
              rw [hz] at hG
              change x ∈ ([] : List (T lam)) at hG
              cases hG
            | inr hz =>
              rw [hz] at hG
              refine ⟨x, ?_, T.le_refl x⟩
              apply
                List.mem_append_right
                  (T.G (T.P mid add))
              rw [T.GZ]
              apply List.mem_append_left [T.Z]
              exact List.mem_append_right [z] hG
        | inr hrest =>
          cases hrest with
          | inl hiq =>
            have hqi : q = i :=
              Fin.eq_of_val_eq hiq
            subst q
            have hLowMid :
                low.idx i ≤ mid.idx i :=
              hBetween.2.1
            have hmidMem :
                mid.idx i ∈
                  T.G (T.P mid add) := by
              apply
                (T.mem_G_P mid add
                  (mid.idx i)).mpr
              exact Or.inl ⟨i, Or.inl rfl⟩
            cases hqx with
            | inl hxi =>
              rw [hxi]
              exact
                ⟨mid.idx i,
                  List.mem_append_left
                    (T.GZ z) hmidMem,
                  hLowMid⟩
            | inr hG =>
              have hxLow :
                  x < low.idx i :=
                hPivotComp.2 x hG
              have hxMid :
                  x < mid.idx i :=
                T.lt_of_lt_of_le x
                  (low.idx i) (mid.idx i)
                  hxLow hLowMid
              exact
                ⟨mid.idx i,
                  List.mem_append_left
                    (T.GZ z) hmidMem,
                  Or.inl hxMid⟩
          | inr hiq =>
            have hmidHigh :
                mid.idx q = high.idx q :=
              hBetween.1 q hiq
            have hlowHigh :
                low.idx q = high.idx q :=
              hAbove q hiq
            have hlowMid :
                low.idx q = mid.idx q :=
              hlowHigh.trans hmidHigh.symm
            refine ⟨x, ?_, T.le_refl x⟩
            apply List.mem_append_left (T.GZ z)
            apply (T.mem_G_P mid add x).mpr
            cases hqx with
            | inl hxq =>
              exact
                Or.inl
                  ⟨q,
                    Or.inl
                      (hxq.trans hlowMid)⟩
            | inr hG =>
              rw [hlowMid] at hG
              exact Or.inl ⟨q, Or.inr hG⟩
      | inr htail =>
        change x ∈ ([] : List (T lam)) at htail
        cases htail

theorem Vec.compare_rplc_same_index_lt {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m)
    (a b : T lam) (hab : a < b) :
    compareVec (v.rplc i a) (v.rplc i b) =
      Ordering.lt := by
  apply Vec.compare_lt_of_pivot
    (v.rplc i a) (v.rplc i b) i
  · intro j hij
    have hji : j.val ≠ i.val :=
      Nat.ne_of_gt hij
    rw [Vec.rplc_idx_of_ne v i j a hji]
    rw [Vec.rplc_idx_of_ne v i j b hji]
  · rw [Vec.rplc_idx_same]
    rw [Vec.rplc_idx_same]
    exact hab

theorem T.fund_P_tail_eq {lam : Nat}
    (ls : Vec (T lam) lam) (add t : T lam)
    (hadd : add ≠ T.Z) :
    T.fund (T.P ls add) t =
      T.P ls (T.fund add t) := by
  conv =>
    lhs
    rw [T.fund, if_neg hadd]

theorem T.fund_Omega_ne_Z {lam : Nat}
    (s t : T lam) (hd : T.dom s = .Omega) :
    T.fund s t ≠ T.Z := by
  cases s with
  | Z =>
    change Dom.zero = Dom.Omega at hd
    cases hd
  | P ls add =>
    by_cases hadd : add = T.Z
    · subst add
      cases hmin : T.domVecMinIdx ls with
      | none =>
        have hd' := hd
        conv at hd' =>
          lhs
          rw [T.dom, if_pos rfl]
          rw [hmin]
        change Dom.one = Dom.Omega at hd'
        cases hd'
      | some md =>
        obtain ⟨m, d⟩ := md
        have hd' := hd
        conv at hd' =>
          lhs
          rw [T.dom, if_pos rfl]
          rw [hmin]
        cases d with
        | zero =>
          change Dom.omega = Dom.Omega at hd'
          cases hd'
        | omega =>
          change Dom.omega = Dom.Omega at hd'
          cases hd'
        | Omega =>
          change Dom.omega = Dom.Omega at hd'
          cases hd'
        | one =>
          change
            (if m.val = 0 then
              Dom.omega else Dom.Omega) =
                Dom.Omega at hd'
          by_cases hm0 : m.val = 0
          · rw [if_pos hm0] at hd'
            cases hd'
          · cases m with
            | mk mv mh =>
              cases mv with
              | zero =>
                exact False.elim (hm0 rfl)
              | succ k =>
                intro heq
                conv at heq =>
                  lhs
                  rw [T.fund, if_pos rfl]
                  rw [hmin]
                  change
                    (if Dom.one = Dom.one then _ else _)
                  rw [if_pos rfl]
                cases heq
    · intro heq
      conv at heq =>
        lhs
        rw [T.fund, if_neg hadd]
      cases heq

theorem T.fund_Omega_strict_mono {lam : Nat}
    (s x y : T lam)
    (hd : T.dom s = .Omega)
    (hxy : x < y) :
    T.fund s x < T.fund s y := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ a u v : T lam, T.size a = n →
        T.dom a = .Omega → u < v →
          T.fund a u < T.fund a v
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a u v hn hdom huv
      cases a with
      | Z =>
        change Dom.zero = Dom.Omega at hdom
        cases hdom
      | P ls add =>
        by_cases hadd : add = T.Z
        · subst add
          cases hmin : T.domVecMinIdx ls with
          | none =>
            have hd' := hdom
            conv at hd' =>
              lhs
              rw [T.dom, if_pos rfl]
              rw [hmin]
            change Dom.one = Dom.Omega at hd'
            cases hd'
          | some md =>
            obtain ⟨m, d⟩ := md
            have hd' := hdom
            conv at hd' =>
              lhs
              rw [T.dom, if_pos rfl]
              rw [hmin]
            cases d with
            | zero =>
              change Dom.omega = Dom.Omega at hd'
              cases hd'
            | omega =>
              change Dom.omega = Dom.Omega at hd'
              cases hd'
            | Omega =>
              change Dom.omega = Dom.Omega at hd'
              cases hd'
            | one =>
              change
                (if m.val = 0 then
                  Dom.omega else Dom.Omega) =
                    Dom.Omega at hd'
              by_cases hm0 : m.val = 0
              · rw [if_pos hm0] at hd'
                cases hd'
              · cases m with
                | mk mv mh =>
                  cases mv with
                  | zero =>
                    exact False.elim (hm0 rfl)
                  | succ k =>
                    let mi : Fin lam :=
                      ⟨Nat.succ k, mh⟩
                    let mj : Fin lam :=
                      ⟨k, Nat.lt_of_succ_lt mh⟩
                    let base :=
                      ls.rplc mi
                        (T.fund (ls.idx mi) T.Z)
                    have hvec :
                        compareVec
                          (base.rplc mj u)
                          (base.rplc mj v) =
                            Ordering.lt :=
                      Vec.compare_rplc_same_index_lt
                        base mj u v huv
                    have hfu :
                        T.fund (T.P ls T.Z) u =
                          T.P (base.rplc mj u) T.Z := by
                      conv =>
                        lhs
                        rw [T.fund, if_pos rfl]
                        rw [hmin]
                        change
                          (if Dom.one = Dom.one then _ else _)
                        rw [if_pos rfl]
                      change
                        T.P
                          ((ls.rplc mi
                            (T.fund (ls.idx mi) T.Z)).rplc
                              mj u)
                          T.Z =
                            T.P (base.rplc mj u) T.Z
                      rfl
                    have hfv :
                        T.fund (T.P ls T.Z) v =
                          T.P (base.rplc mj v) T.Z := by
                      conv =>
                        lhs
                        rw [T.fund, if_pos rfl]
                        rw [hmin]
                        change
                          (if Dom.one = Dom.one then _ else _)
                        rw [if_pos rfl]
                      change
                        T.P
                          ((ls.rplc mi
                            (T.fund (ls.idx mi) T.Z)).rplc
                              mj v)
                          T.Z =
                            T.P (base.rplc mj v) T.Z
                      rfl
                    rw [hfu, hfv]
                    exact T.P_lt_P_of_compareVec_lt
                      (base.rplc mj u)
                      (base.rplc mj v)
                      T.Z T.Z hvec
        · have hdadd : T.dom add = .Omega := by
            conv at hdom =>
              lhs
              rw [T.dom, if_neg hadd]
            exact hdom
          have hsz : T.size add < n := by
            rw [← hn]
            exact T.add_size_lt_P ls add
          have hrec :
              T.fund add u < T.fund add v :=
            ih (T.size add) hsz add u v
              rfl hdadd huv
          rw [
            T.fund_P_tail_eq ls add u hadd,
            T.fund_P_tail_eq ls add v hadd]
          exact T.P_tail_lt ls
            (T.fund add u) (T.fund add v) hrec)
  exact main (T.size s) s x y rfl hd hxy

theorem T.iter_fund_lt_next {lam : Nat}
    (s t : T lam) (hd : T.dom s = .Omega) :
    T.iter (fun x => T.fund s x) t <
      T.fund s
        (T.iter (fun x => T.fund s x) t) := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ u : T lam, T.size u = n →
        T.iter (fun x => T.fund s x) u <
          T.fund s
            (T.iter (fun x => T.fund s x) u)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro u hn
      cases u with
      | Z =>
        rw [T.iter]
        have hne :
            T.fund s T.Z ≠ T.Z :=
          T.fund_Omega_ne_Z s T.Z hd
        cases T.Z_le (T.fund s T.Z) with
        | inl hlt =>
          exact hlt
        | inr heq =>
          have hz :
              T.Z = T.fund s T.Z :=
            T_eq_sound T.Z
              (T.fund s T.Z) heq
          exact False.elim (hne hz.symm)
      | P us add =>
        have hsz : T.size add < n := by
          rw [← hn]
          exact T.add_size_lt_P us add
        have hrec :=
          ih (T.size add) hsz add rfl
        rw [T.iter]
        exact T.fund_Omega_strict_mono s
          (T.iter (fun x => T.fund s x) add)
          (T.fund s
            (T.iter (fun x => T.fund s x) add))
          hd hrec)
  exact main (T.size t) t rfl

theorem T.fund_Omega_master {lam : Nat}
    (s z : T lam)
    (hs : T.isNF s)
    (hd : T.dom s = .Omega)
    (hz : T.isNFComp z) :
    T.isNF (T.fund s z) ∧
      T.SDom z (T.fund s z) s := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ a w : T lam, T.size a = n →
        T.isNF a → T.dom a = .Omega →
        T.isNFComp w →
          T.isNF (T.fund a w) ∧
            T.SDom w (T.fund a w) a
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a w hn ha hdom hw
      cases a with
      | Z =>
        change Dom.zero = Dom.Omega at hdom
        cases hdom
      | P ls add =>
        have ha0 := ha
        have hcoords :=
          T.isNF_P_coord_NFComp ls add ha
        cases ha with
        | p _ _ h0 h1 h2 h3 =>
          by_cases hadd : add = T.Z
          · subst add
            cases hmin : T.domVecMinIdx ls with
            | none =>
              have hd' := hdom
              conv at hd' =>
                lhs
                rw [T.dom, if_pos rfl]
                rw [hmin]
              change Dom.one = Dom.Omega at hd'
              cases hd'
            | some md =>
              obtain ⟨m, d⟩ := md
              have hspec :=
                T.domVecMinIdx_some_spec ls m d hmin
              have hd' := hdom
              conv at hd' =>
                lhs
                rw [T.dom, if_pos rfl]
                rw [hmin]
              cases d with
              | zero =>
                change Dom.omega = Dom.Omega at hd'
                cases hd'
              | omega =>
                change Dom.omega = Dom.Omega at hd'
                cases hd'
              | Omega =>
                change Dom.omega = Dom.Omega at hd'
                cases hd'
              | one =>
                change
                  (if m.val = 0 then
                    Dom.omega else Dom.Omega) =
                      Dom.Omega at hd'
                by_cases hm0 : m.val = 0
                · rw [if_pos hm0] at hd'
                  cases hd'
                · cases m with
                  | mk mv mh =>
                    cases mv with
                    | zero =>
                      exact False.elim (hm0 rfl)
                    | succ k =>
                      let i : Fin lam :=
                        ⟨Nat.succ k, mh⟩
                      let j : Fin lam :=
                        ⟨k, Nat.lt_of_succ_lt mh⟩
                      let child := ls.idx i
                      let childFund :=
                        T.fund child T.Z
                      let low :=
                        (ls.rplc i childFund).rplc j w
                      have hchildComp :
                          T.isNFComp child :=
                        hcoords i
                      have hchildDom :
                          T.dom child = Dom.one := by
                        change
                          T.dom
                            (ls.idx
                              ⟨Nat.succ k, mh⟩) =
                            Dom.one
                        exact hspec.2.1
                      have hchildFundComp :
                          T.isNFComp childFund := by
                        exact T.fund_one_NFComp_closed
                          child hchildComp hchildDom
                      have hchildNe :
                          child ≠ T.Z := by
                        intro heq
                        have hc := hchildDom
                        rw [heq] at hc
                        cases hc
                      have hchildLt :
                          childFund < child := by
                        exact T.fund_lt_self
                          child T.Z hchildNe
                      have hij : i.val ≠ j.val := by
                        change Nat.succ k ≠ k
                        exact
                          (Nat.ne_of_lt
                            (Nat.lt_succ_self k)).symm
                      have hnf :
                          T.isNF (T.P low T.Z) := by
                        exact T.rplc_two_NF_closed
                          ls i j childFund w hij
                          ha0 hchildFundComp hw
                      have hAbove :
                          ∀ q : Fin lam,
                            i.val < q.val →
                              low.idx q = ls.idx q := by
                        intro q hiq
                        have hqj : q.val ≠ j.val := by
                          have hjq : j.val < q.val := by
                            exact Nat.lt_trans
                              (Nat.lt_succ_self k) hiq
                          exact Nat.ne_of_gt hjq
                        have hqi : q.val ≠ i.val :=
                          Nat.ne_of_gt hiq
                        change
                          ((ls.rplc i childFund).rplc
                            j w).idx q = ls.idx q
                        rw [
                          Vec.rplc_idx_of_ne
                            (ls.rplc i childFund)
                            j q w hqj,
                          Vec.rplc_idx_of_ne
                            ls i q childFund hqi]
                      have hlowi :
                          low.idx i = childFund := by
                        change
                          ((ls.rplc i childFund).rplc
                            j w).idx i = childFund
                        rw [
                          Vec.rplc_idx_of_ne
                            (ls.rplc i childFund)
                            j i w hij,
                          Vec.rplc_idx_same]
                      have hPivotLt :
                          low.idx i < ls.idx i := by
                        rw [hlowi]
                        exact hchildLt
                      have hPivotComp :
                          T.isNFComp (low.idx i) := by
                        rw [hlowi]
                        exact hchildFundComp
                      have hBelow :
                          ∀ q : Fin lam,
                            q.val < i.val →
                              low.idx q = T.Z ∨
                                low.idx q = w := by
                        intro q hqi
                        by_cases hqj :
                            q.val = j.val
                        · have hq : q = j :=
                            Fin.eq_of_val_eq hqj
                          rw [hq]
                          apply Or.inr
                          change
                            ((ls.rplc i childFund).rplc
                              j w).idx j = w
                          rw [Vec.rplc_idx_same]
                        · have hqine :
                              q.val ≠ i.val :=
                            Nat.ne_of_lt hqi
                          have hold :
                              ls.idx q = T.Z := by
                            have hdomq :
                                T.dom (ls.idx q) =
                                  Dom.zero :=
                              hspec.2.2 q hqi
                            exact T.dom_zero_eq_Z
                              (ls.idx q) hdomq
                          apply Or.inl
                          change
                            ((ls.rplc i childFund).rplc
                              j w).idx q = T.Z
                          rw [
                            Vec.rplc_idx_of_ne
                              (ls.rplc i childFund)
                              j q w hqj,
                            Vec.rplc_idx_of_ne
                              ls i q childFund hqine,
                            hold]
                      have hsd :
                          T.SDom w
                            (T.P low T.Z)
                            (T.P ls T.Z) :=
                        T.SDom_PZ_pivot_comp
                          w low ls i
                          hAbove hPivotLt
                          hPivotComp hBelow
                      have hfundEq :
                          T.fund (T.P ls T.Z) w =
                            T.P low T.Z := by
                        conv =>
                          lhs
                          rw [T.fund, if_pos rfl]
                          rw [hmin]
                          change
                            (if Dom.one = Dom.one then
                              _ else _)
                          rw [if_pos rfl]
                        change
                          T.P
                            ((ls.rplc i
                              (T.fund
                                (ls.idx i) T.Z)).rplc
                              j w)
                            T.Z =
                              T.P low T.Z
                        rfl
                      rw [hfundEq]
                      exact ⟨hnf, hsd⟩
          · have hdadd :
                T.dom add = .Omega := by
              conv at hdom =>
                lhs
                rw [T.dom, if_neg hadd]
              exact hdom
            have hsz : T.size add < n := by
              rw [← hn]
              exact T.add_size_lt_P ls add
            obtain ⟨hnewNF, hnewSD⟩ :=
              ih (T.size add) hsz add w
                rfl h1 hdadd hw
            have hparentNF :
                T.isNF
                  (T.P ls (T.fund add w)) :=
              T.isNF.p ls (T.fund add w)
                h0 hnewNF h2
                (T.le_trans
                  (T.head (T.fund add w))
                  (T.head add)
                  (T.P ls T.Z)
                  (T.head_fund_le add w) h3)
            have hparentSD :
                T.SDom w
                  (T.P ls (T.fund add w))
                  (T.P ls add) :=
              T.SDom_tail w
                (T.fund add w) add ls hnewSD
            rw [T.fund_P_tail_eq ls add w hadd]
            exact ⟨hparentNF, hparentSD⟩)
  exact main (T.size s) s z rfl hs hd hz

theorem T.fund_iter_NFComp_core {lam : Nat} (s t : T lam)
    (hs : T.isNFComp s)
    (hd : T.dom s = .Omega) :
    T.isNFComp
      (T.fund s (T.iter (fun x => T.fund s x) t)) := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ u : T lam, T.size u = n →
        T.isNFComp
          (T.fund s
            (T.iter (fun x => T.fund s x) u))
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro u hn
      have harg :
          T.isNFComp
            (T.iter (fun x => T.fund s x) u) := by
        cases u with
        | Z =>
          rw [T.iter]
          exact T.isNFComp_Z
        | P us add =>
          have hsz : T.size add < n := by
            rw [← hn]
            exact T.add_size_lt_P us add
          have hrec :=
            ih (T.size add) hsz add rfl
          rw [T.iter]
          exact hrec
      obtain ⟨hnf, hsd⟩ :=
        T.fund_Omega_master s
          (T.iter (fun x => T.fund s x) u)
          hs.1 hd harg
      have hlt :
          T.iter (fun x => T.fund s x) u <
            T.fund s
              (T.iter (fun x => T.fund s x) u) :=
        T.iter_fund_lt_next s u hd
      exact T.NFComp_of_SDom
        (T.iter (fun x => T.fund s x) u)
        (T.fund s
          (T.iter (fun x => T.fund s x) u))
        s hnf hs harg hsd hlt)
  exact main (T.size t) t rfl

theorem T.G_mul_PZ_subset {lam : Nat}
    (ls : Vec (T lam) lam) :
    ∀ t x : T lam,
      x ∈ T.G (T.mul (T.P ls T.Z) t) →
        x ∈ T.G (T.P ls T.Z) := by
  intro t
  let motive : Nat → Prop :=
    fun n =>
      ∀ u : T lam, T.size u = n →
        ∀ x : T lam,
          x ∈ T.G (T.mul (T.P ls T.Z) u) →
            x ∈ T.G (T.P ls T.Z)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro u hn x hx
      cases u with
      | Z =>
        rw [T.mul] at hx
        change x ∈ ([] : List (T lam)) at hx
        cases hx
      | P us add =>
        have hsz : T.size add < n := by
          rw [← hn]
          exact T.add_size_lt_P us add
        have hrec :=
          ih (T.size add) hsz add rfl
        rw [T.mul] at hx
        change
          x ∈
            T.G
              (T.P ls
                (T.mul (T.P ls T.Z) add)) at hx
        cases
            (T.mem_G_P ls
              (T.mul (T.P ls T.Z) add) x).mp hx with
        | inl hvec =>
          apply (T.mem_G_P ls T.Z x).mpr
          exact Or.inl hvec
        | inr htail =>
          exact hrec x htail)
  exact main (T.size t) t rfl

theorem T.SDom_mul_PZ {lam : Nat}
    (u v : Vec (T lam) lam) (t : T lam)
    (hvec : compareVec u v = Ordering.lt)
    (hbase :
      T.SDom T.Z (T.P u T.Z) (T.P v T.Z)) :
    T.SDom T.Z
      (T.mul (T.P u T.Z) t) (T.P v T.Z) := by
  constructor
  · exact T.mul_PZ_lt_of_compareVec_lt u v t hvec
  · intro c hmc hcv x hx
    cases t with
    | Z =>
      rw [T.mul] at hx
      change x ∈ ([] : List (T lam)) at hx
      cases hx
    | P ts add =>
      have hbaseMul :
          T.P u T.Z ≤
            T.mul (T.P u T.Z) (T.P ts add) := by
        rw [T.mul]
        change
          T.P u T.Z ≤
            T.P u (T.mul (T.P u T.Z) add)
        exact T.P_le_P_same u T.Z
          (T.mul (T.P u T.Z) add)
          (T.Z_le (T.mul (T.P u T.Z) add))
      have hbaseC :
          T.P u T.Z ≤ c :=
        T.le_trans
          (T.P u T.Z)
          (T.mul (T.P u T.Z) (T.P ts add))
          c hbaseMul hmc
      have hxbase :
          x ∈ T.G (T.P u T.Z) :=
        T.G_mul_PZ_subset u (T.P ts add) x hx
      exact hbase.2 c hbaseC hcv x hxbase

theorem T.SDom_rplc_min_Z {lam : Nat}
    (ls : Vec (T lam) lam) (m : Fin lam) (d : Dom)
    (b : T lam)
    (hmin : T.domVecMinIdx ls = some (m, d))
    (hb : T.isNFComp b)
    (hblt : b < ls.idx m) :
    T.SDom T.Z
      (T.P (ls.rplc m b) T.Z)
      (T.P ls T.Z) := by
  have hspec :=
    T.domVecMinIdx_some_spec ls m d hmin
  apply T.SDom_PZ_pivot_comp
    T.Z (ls.rplc m b) ls m
  · intro j hmj
    exact Vec.rplc_idx_of_ne
      ls m j b (Nat.ne_of_gt hmj)
  · rw [Vec.rplc_idx_same]
    exact hblt
  · rw [Vec.rplc_idx_same]
    exact hb
  · intro q hqm
    apply Or.inl
    have hne : q.val ≠ m.val :=
      Nat.ne_of_lt hqm
    rw [Vec.rplc_idx_of_ne ls m q b hne]
    exact T.dom_zero_eq_Z
      (ls.idx q) (hspec.2.2 q hqm)

theorem T.SDom_rplc_lower {lam : Nat}
    (z : T lam)
    (ls : Vec (T lam) lam)
    (m j : Fin lam) (d : Dom) (b : T lam)
    (hjm : j.val < m.val)
    (hmin : T.domVecMinIdx ls = some (m, d))
    (hb : T.isNFComp b)
    (hblt : b < ls.idx m) :
    T.SDom z
      (T.P ((ls.rplc m b).rplc j z) T.Z)
      (T.P ls T.Z) := by
  have hspec :=
    T.domVecMinIdx_some_spec ls m d hmin
  apply T.SDom_PZ_pivot_comp
    z ((ls.rplc m b).rplc j z) ls m
  · intro q hmq
    have hqj : q.val ≠ j.val :=
      Nat.ne_of_gt (Nat.lt_trans hjm hmq)
    have hqm : q.val ≠ m.val :=
      Nat.ne_of_gt hmq
    rw [Vec.rplc_idx_of_ne
      (ls.rplc m b) j q z hqj]
    rw [Vec.rplc_idx_of_ne ls m q b hqm]
  · have hmj : m.val ≠ j.val :=
      Nat.ne_of_gt hjm
    rw [Vec.rplc_idx_of_ne
      (ls.rplc m b) j m z hmj]
    rw [Vec.rplc_idx_same]
    exact hblt
  · have hmj : m.val ≠ j.val :=
      Nat.ne_of_gt hjm
    rw [Vec.rplc_idx_of_ne
      (ls.rplc m b) j m z hmj]
    rw [Vec.rplc_idx_same]
    exact hb
  · intro q hqm
    by_cases hqj : q.val = j.val
    · have hq : q = j :=
        Fin.eq_of_val_eq hqj
      rw [hq, Vec.rplc_idx_same]
      exact Or.inr rfl
    · apply Or.inl
      rw [Vec.rplc_idx_of_ne
        (ls.rplc m b) j q z hqj]
      have hqmne : q.val ≠ m.val :=
        Nat.ne_of_lt hqm
      rw [Vec.rplc_idx_of_ne
        ls m q b hqmne]
      exact T.dom_zero_eq_Z
        (ls.idx q) (hspec.2.2 q hqm)

theorem T.fund_dom_master {lam : Nat} (s : T lam)
    (hs : T.isNF s) :
    (T.dom s = .omega →
      ∀ t : T lam,
        T.isNF (T.fund s t) ∧
          T.SDom T.Z (T.fund s t) s) ∧
    (T.dom s = .Omega →
      ∀ z : T lam, T.isNFComp z →
        T.isNF (T.fund s z) ∧
          T.SDom z (T.fund s z) s) := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ a : T lam, T.size a = n →
        T.isNF a →
        (T.dom a = .omega →
          ∀ t : T lam,
            T.isNF (T.fund a t) ∧
              T.SDom T.Z (T.fund a t) a) ∧
        (T.dom a = .Omega →
          ∀ z : T lam, T.isNFComp z →
            T.isNF (T.fund a z) ∧
              T.SDom z (T.fund a z) a)
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a hn ha
      cases a with
      | Z =>
        constructor
        · intro hd
          change Dom.zero = Dom.omega at hd
          cases hd
        · intro hd
          change Dom.zero = Dom.Omega at hd
          cases hd
      | P ls add =>
        cases ha with
        | p _ _ h0 h1 h2 h3 =>
          by_cases hadd : add = T.Z
          · subst add
            have hparentNF :
                T.isNF (T.P ls T.Z) :=
              T.isNF.p ls T.Z h0 h1 h2 h3
            cases hmin : T.domVecMinIdx ls with
            | none =>
              constructor
              · intro hd
                have hd' := hd
                conv at hd' =>
                  lhs
                  rw [T.dom, if_pos rfl]
                  rw [hmin]
                change Dom.one = Dom.omega at hd'
                cases hd'
              · intro hd
                have hd' := hd
                conv at hd' =>
                  lhs
                  rw [T.dom, if_pos rfl]
                  rw [hmin]
                change Dom.one = Dom.Omega at hd'
                cases hd'
            | some md =>
              obtain ⟨m, d⟩ := md
              have hspec :=
                T.domVecMinIdx_some_spec ls m d hmin
              have hchildComp :
                  T.isNFComp (ls.idx m) :=
                T.isNF_P_coord_NFComp
                  ls T.Z hparentNF m
              have hmsz :
                  T.size (ls.idx m) < n := by
                rw [← hn]
                rw [← Vec.getElem_eq_idx ls m]
                exact T.idx_size_lt_P ls T.Z m
              have hchildRec :=
                ih (T.size (ls.idx m)) hmsz
                  (ls.idx m) rfl hchildComp.1
              have hchildNe :
                  ls.idx m ≠ T.Z := by
                intro heq
                have hdchild := hspec.2.1
                rw [heq] at hdchild
                change Dom.zero = d at hdchild
                exact hspec.1 hdchild.symm
              cases d with
              | zero =>
                exact False.elim (hspec.1 rfl)
              | omega =>
                constructor
                · intro hd t
                  have hchildDom :
                      T.dom (ls.idx m) = .omega :=
                    hspec.2.1
                  obtain ⟨hfnf, hfrel⟩ :=
                    hchildRec.1 hchildDom t
                  have hfcomp :
                      T.isNFComp
                        (T.fund (ls.idx m) t) :=
                    T.NFComp_of_SDom_Z_or_eq
                      (T.fund (ls.idx m) t)
                      (ls.idx m) hfnf
                      hchildComp hfrel
                  have hflt :
                      T.fund (ls.idx m) t <
                        ls.idx m :=
                    T.fund_lt_self
                      (ls.idx m) t hchildNe
                  let low :=
                    ls.rplc m
                      (T.fund (ls.idx m) t)
                  have hnf :
                      T.isNF (T.P low T.Z) := by
                    exact T.rplc_NF_closed
                      ls m
                      (T.fund (ls.idx m) t)
                      hparentNF hfcomp
                  have hrel :
                      T.SDom T.Z
                        (T.P low T.Z)
                        (T.P ls T.Z) := by
                    exact T.SDom_rplc_min_Z
                      ls m Dom.omega
                      (T.fund (ls.idx m) t)
                      hmin hfcomp hflt
                  have hfund :
                      T.fund (T.P ls T.Z) t =
                        T.P low T.Z := by
                    conv =>
                      lhs
                      rw [T.fund, if_pos rfl]
                      rw [hmin]
                      change
                        (if Dom.omega = Dom.one then _
                        else _) =
                          T.P low T.Z
                      rw [if_neg (by intro h; cases h)]
                      change
                        (if Dom.omega = Dom.Omega then _
                        else _) =
                          T.P low T.Z
                      rw [if_neg (by intro h; cases h)]
                    rfl
                  rw [hfund]
                  exact ⟨hnf, hrel⟩
                · intro hd
                  have hd' := hd
                  conv at hd' =>
                    lhs
                    rw [T.dom, if_pos rfl]
                    rw [hmin]
                  change Dom.omega = Dom.Omega at hd'
                  cases hd'
              | Omega =>
                constructor
                · intro hd t
                  have hchildDom :
                      T.dom (ls.idx m) = .Omega :=
                    hspec.2.1
                  have hOmegaRec :
                      ∀ z : T lam, T.isNFComp z →
                        T.isNF
                            (T.fund (ls.idx m) z) ∧
                          T.SDom z
                            (T.fund (ls.idx m) z)
                            (ls.idx m) :=
                    hchildRec.2 hchildDom
                  let imotive : Nat → Prop :=
                    fun k =>
                      ∀ u : T lam, T.size u = k →
                        T.isNFComp
                          (T.iter
                            (fun x =>
                              T.fund (ls.idx m) x) u) ∧
                        T.isNFComp
                          (T.fund (ls.idx m)
                            (T.iter
                              (fun x =>
                                T.fund (ls.idx m) x) u))
                  have imain :
                      ∀ k : Nat, imotive k := by
                    intro k
                    exact Nat.strongRecOn k
                      (motive := imotive) (fun k iih => by
                        intro u hu
                        cases u with
                        | Z =>
                          rw [T.iter]
                          obtain ⟨hznf, hzrel⟩ :=
                            hOmegaRec T.Z
                              T.isNFComp_Z
                          exact
                            ⟨T.isNFComp_Z,
                              T.NFComp_of_SDom_Z_or_eq
                                (T.fund (ls.idx m) T.Z)
                                (ls.idx m)
                                hznf hchildComp hzrel⟩
                        | P us uadd =>
                          have husz :
                              T.size uadd < k := by
                            rw [← hu]
                            exact
                              T.add_size_lt_P us uadd
                          obtain ⟨hprev, hcur⟩ :=
                            iih (T.size uadd) husz
                              uadd rfl
                          rw [T.iter]
                          obtain ⟨hnxtNF, hnxtRel⟩ :=
                            hOmegaRec
                              (T.fund (ls.idx m)
                                (T.iter
                                  (fun x =>
                                    T.fund (ls.idx m) x)
                                  uadd))
                              hcur
                          have hstep :
                              T.fund (ls.idx m)
                                  (T.iter
                                    (fun x =>
                                      T.fund (ls.idx m) x)
                                    uadd) <
                                T.fund (ls.idx m)
                                  (T.fund (ls.idx m)
                                    (T.iter
                                      (fun x =>
                                        T.fund (ls.idx m) x)
                                      uadd)) := by
                            have hh :=
                              T.iter_fund_lt_next
                                (ls.idx m)
                                (T.P us uadd)
                                hchildDom
                            rw [T.iter] at hh
                            exact hh
                          exact
                            ⟨hcur,
                              T.NFComp_of_SDom
                                (T.fund (ls.idx m)
                                  (T.iter
                                    (fun x =>
                                      T.fund (ls.idx m) x)
                                    uadd))
                                (T.fund (ls.idx m)
                                  (T.fund (ls.idx m)
                                    (T.iter
                                      (fun x =>
                                        T.fund (ls.idx m) x)
                                      uadd)))
                                (ls.idx m)
                                hnxtNF hchildComp hcur
                                hnxtRel hstep⟩)
                  obtain ⟨hwcomp, hfwcomp⟩ :=
                    imain (T.size t) t rfl
                  let w :=
                    T.iter
                      (fun x =>
                        T.fund (ls.idx m) x) t
                  have hflt :
                      T.fund (ls.idx m) w <
                        ls.idx m :=
                    T.fund_lt_self
                      (ls.idx m) w hchildNe
                  let low :=
                    ls.rplc m
                      (T.fund (ls.idx m) w)
                  have hnf :
                      T.isNF (T.P low T.Z) := by
                    exact T.rplc_NF_closed
                      ls m
                      (T.fund (ls.idx m) w)
                      hparentNF hfwcomp
                  have hrel :
                      T.SDom T.Z
                        (T.P low T.Z)
                        (T.P ls T.Z) := by
                    exact T.SDom_rplc_min_Z
                      ls m Dom.Omega
                      (T.fund (ls.idx m) w)
                      hmin hfwcomp hflt
                  have hfund :
                      T.fund (T.P ls T.Z) t =
                        T.P low T.Z := by
                    conv =>
                      lhs
                      rw [T.fund, if_pos rfl]
                      rw [hmin]
                      change
                        (if Dom.Omega = Dom.one then _
                        else _) =
                          T.P low T.Z
                      rw [if_neg (by intro h; cases h)]
                      change
                        (if Dom.Omega = Dom.Omega then _
                        else _) =
                          T.P low T.Z
                      rw [if_pos rfl]
                    rfl
                  rw [hfund]
                  exact ⟨hnf, hrel⟩
                · intro hd
                  have hd' := hd
                  conv at hd' =>
                    lhs
                    rw [T.dom, if_pos rfl]
                    rw [hmin]
                  change Dom.omega = Dom.Omega at hd'
                  cases hd'
              | one =>
                have hchildDom :
                    T.dom (ls.idx m) = .one :=
                  hspec.2.1
                have hfcomp :
                    T.isNFComp
                      (T.fund (ls.idx m) T.Z) :=
                  T.fund_one_NFComp_closed
                    (ls.idx m) hchildComp hchildDom
                have hflt :
                    T.fund (ls.idx m) T.Z <
                      ls.idx m :=
                  T.fund_lt_self
                    (ls.idx m) T.Z hchildNe
                cases m with
                | mk mv mh =>
                  cases mv with
                  | zero =>
                    let mi : Fin lam := ⟨0, mh⟩
                    let low :=
                      ls.rplc mi
                        (T.fund (ls.idx mi) T.Z)
                    constructor
                    · intro hd t
                      have hbaseNF :
                          T.isNF (T.P low T.Z) := by
                        exact T.rplc_NF_closed
                          ls mi
                          (T.fund (ls.idx mi) T.Z)
                          hparentNF hfcomp
                      have hbaseRel :
                          T.SDom T.Z
                            (T.P low T.Z)
                            (T.P ls T.Z) := by
                        exact T.SDom_rplc_min_Z
                          ls mi Dom.one
                          (T.fund (ls.idx mi) T.Z)
                          hmin hfcomp hflt
                      have hvec :
                          compareVec low ls =
                            Ordering.lt := by
                        exact Vec.compare_rplc_lt
                          ls mi
                          (T.fund (ls.idx mi) T.Z)
                          hflt
                      have hnf :
                          T.isNF
                            (T.mul (T.P low T.Z) t) :=
                        T.mul_PZ_NF_closed
                          low hbaseNF t
                      have hrel :
                          T.SDom T.Z
                            (T.mul (T.P low T.Z) t)
                            (T.P ls T.Z) :=
                        T.SDom_mul_PZ
                          low ls t hvec hbaseRel
                      have hfund :
                          T.fund (T.P ls T.Z) t =
                            T.mul (T.P low T.Z) t := by
                        conv =>
                          lhs
                          rw [T.fund, if_pos rfl]
                          rw [hmin]
                          change
                            (if Dom.one = Dom.one then _
                            else _) =
                              T.mul (T.P low T.Z) t
                          rw [if_pos rfl]
                        rfl
                      rw [hfund]
                      exact ⟨hnf, hrel⟩
                    · intro hd
                      have hd' := hd
                      conv at hd' =>
                        lhs
                        rw [T.dom, if_pos rfl]
                        rw [hmin]
                      change Dom.omega = Dom.Omega at hd'
                      cases hd'
                  | succ k =>
                    let mi : Fin lam :=
                      ⟨Nat.succ k, mh⟩
                    let mj : Fin lam :=
                      ⟨k, Nat.lt_of_succ_lt mh⟩
                    constructor
                    · intro hd
                      have hd' := hd
                      conv at hd' =>
                        lhs
                        rw [T.dom, if_pos rfl]
                        rw [hmin]
                      change Dom.Omega = Dom.omega at hd'
                      cases hd'
                    · intro hd z hz
                      let low :=
                        (ls.rplc mi
                          (T.fund (ls.idx mi) T.Z)).rplc
                            mj z
                      have hnf :
                          T.isNF (T.P low T.Z) := by
                        exact T.rplc_two_NF_closed
                          ls mi mj
                          (T.fund (ls.idx mi) T.Z)
                          z
                          (Nat.ne_of_gt
                            (Nat.lt_succ_self k))
                          hparentNF hfcomp hz
                      have hrel :
                          T.SDom z
                            (T.P low T.Z)
                            (T.P ls T.Z) := by
                        exact T.SDom_rplc_lower
                          z ls mi mj Dom.one
                          (T.fund (ls.idx mi) T.Z)
                          (Nat.lt_succ_self k)
                          hmin hfcomp hflt
                      have hfund :
                          T.fund (T.P ls T.Z) z =
                            T.P low T.Z := by
                        conv =>
                          lhs
                          rw [T.fund, if_pos rfl]
                          rw [hmin]
                          change
                            (if Dom.one = Dom.one then _
                            else _) =
                              T.P low T.Z
                          rw [if_pos rfl]
                        change
                          T.P
                            ((ls.rplc mi
                              (T.fund (ls.idx mi) T.Z)).rplc
                                mj z)
                            T.Z =
                              T.P low T.Z
                        rfl
                      rw [hfund]
                      exact ⟨hnf, hrel⟩
          · have hsz :
                T.size add < n := by
              rw [← hn]
              exact T.add_size_lt_P ls add
            have hrec :=
              ih (T.size add) hsz
                add rfl h1
            constructor
            · intro hd t
              have hdadd :
                  T.dom add = .omega := by
                conv at hd =>
                  lhs
                  rw [T.dom, if_neg hadd]
                exact hd
              obtain ⟨hfnf, hfrel⟩ :=
                hrec.1 hdadd t
              have hnf :
                  T.isNF
                    (T.P ls (T.fund add t)) :=
                T.isNF.p ls (T.fund add t)
                  h0 hfnf h2
                  (T.le_trans
                    (T.head (T.fund add t))
                    (T.head add)
                    (T.P ls T.Z)
                    (T.head_fund_le add t) h3)
              have hrel :
                  T.SDom T.Z
                    (T.P ls (T.fund add t))
                    (T.P ls add) :=
                T.SDom_tail
                  T.Z (T.fund add t)
                  add ls hfrel
              rw [T.fund_P_tail_eq ls add t hadd]
              exact ⟨hnf, hrel⟩
            · intro hd z hz
              have hdadd :
                  T.dom add = .Omega := by
                conv at hd =>
                  lhs
                  rw [T.dom, if_neg hadd]
                exact hd
              obtain ⟨hfnf, hfrel⟩ :=
                hrec.2 hdadd z hz
              have hnf :
                  T.isNF
                    (T.P ls (T.fund add z)) :=
                T.isNF.p ls (T.fund add z)
                  h0 hfnf h2
                  (T.le_trans
                    (T.head (T.fund add z))
                    (T.head add)
                    (T.P ls T.Z)
                    (T.head_fund_le add z) h3)
              have hrel :
                  T.SDom z
                    (T.P ls (T.fund add z))
                    (T.P ls add) :=
                T.SDom_tail
                  z (T.fund add z)
                  add ls hfrel
              rw [T.fund_P_tail_eq ls add z hadd]
              exact ⟨hnf, hrel⟩)
  exact main (T.size s) s rfl hs

theorem T.fund_omega_master {lam : Nat}
    (s t : T lam)
    (hs : T.isNF s)
    (hd : T.dom s = .omega) :
    T.isNF (T.fund s t) ∧
      T.SDom T.Z (T.fund s t) s := by
  let motive : Nat → Prop :=
    fun n =>
      ∀ a u : T lam, T.size a = n →
        T.isNF a → T.dom a = .omega →
          T.isNF (T.fund a u) ∧
            T.SDom T.Z (T.fund a u) a
  have main : ∀ n : Nat, motive n := by
    intro n
    exact Nat.strongRecOn n (motive := motive) (fun n ih => by
      intro a u hn ha hdom
      cases a with
      | Z =>
        change Dom.zero = Dom.omega at hdom
        cases hdom
      | P ls add =>
        have ha0 := ha
        have hcoords :=
          T.isNF_P_coord_NFComp ls add ha
        cases ha with
        | p _ _ h0 h1 h2 h3 =>
          by_cases hadd : add = T.Z
          · subst add
            cases hmin : T.domVecMinIdx ls with
            | none =>
              have hd' := hdom
              conv at hd' =>
                lhs
                rw [T.dom, if_pos rfl]
                rw [hmin]
              change Dom.one = Dom.omega at hd'
              cases hd'
            | some md =>
              obtain ⟨m, d⟩ := md
              have hspec :=
                T.domVecMinIdx_some_spec ls m d hmin
              have hd' := hdom
              conv at hd' =>
                lhs
                rw [T.dom, if_pos rfl]
                rw [hmin]
              cases d with
              | zero =>
                exact False.elim (hspec.1 rfl)
              | one =>
                change
                  (if m.val = 0 then
                    Dom.omega else Dom.Omega) =
                      Dom.omega at hd'
                have hm0 : m.val = 0 := by
                  by_cases hm : m.val = 0
                  · exact hm
                  · rw [if_neg hm] at hd'
                    cases hd'
                cases m with
                | mk mv mh =>
                  change mv = 0 at hm0
                  subst mv
                  let i : Fin lam := ⟨0, mh⟩
                  let child := ls.idx i
                  let childFund :=
                    T.fund child T.Z
                  let base := ls.rplc i childFund
                  have hchildComp :
                      T.isNFComp child :=
                    hcoords i
                  have hchildDom :
                      T.dom child = Dom.one := by
                    change
                      T.dom (ls.idx ⟨0, mh⟩) =
                        Dom.one
                    exact hspec.2.1
                  have hchildFundComp :
                      T.isNFComp childFund :=
                    T.fund_one_NFComp_closed
                      child hchildComp hchildDom
                  have hchildNe : child ≠ T.Z := by
                    intro heq
                    have hc := hchildDom
                    rw [heq] at hc
                    cases hc
                  have hchildLt :
                      childFund < child :=
                    T.fund_lt_self child T.Z hchildNe
                  have hbaseNF :
                      T.isNF (T.P base T.Z) := by
                    exact T.rplc_NF_closed
                      ls i childFund ha0
                      hchildFundComp
                  have hbaseSD :
                      T.SDom T.Z
                        (T.P base T.Z)
                        (T.P ls T.Z) := by
                    exact T.SDom_rplc_min_Z
                      ls i Dom.one childFund
                      hmin hchildFundComp hchildLt
                  have hvec :
                      compareVec base ls =
                        Ordering.lt := by
                    exact Vec.compare_rplc_lt
                      ls i childFund hchildLt
                  have hnf :
                      T.isNF
                        (T.mul (T.P base T.Z) u) :=
                    T.mul_PZ_NF_closed
                      base hbaseNF u
                  have hsd :
                      T.SDom T.Z
                        (T.mul (T.P base T.Z) u)
                        (T.P ls T.Z) :=
                    T.SDom_mul_PZ
                      base ls u hvec hbaseSD
                  have hfundEq :
                      T.fund (T.P ls T.Z) u =
                        T.mul (T.P base T.Z) u := by
                    conv =>
                      lhs
                      rw [T.fund, if_pos rfl]
                      rw [hmin]
                      change
                        (if Dom.one = Dom.one then
                          _ else _)
                      rw [if_pos rfl]
                    change
                      T.mul
                        (T.P
                          (ls.rplc i
                            (T.fund
                              (ls.idx i) T.Z))
                          T.Z)
                        u =
                        T.mul (T.P base T.Z) u
                    rfl
                  rw [hfundEq]
                  exact ⟨hnf, hsd⟩
              | omega =>
                let child := ls.idx m
                let childFund :=
                  T.fund child u
                let base := ls.rplc m childFund
                have hchildComp :
                    T.isNFComp child :=
                  hcoords m
                have hchildDom :
                    T.dom child = Dom.omega := by
                  change
                    T.dom (ls.idx m) = Dom.omega
                  exact hspec.2.1
                have hsz :
                    T.size child < n := by
                  change T.size (ls.idx m) < n
                  have hlt :
                      T.size (ls.idx m) <
                        T.size (T.P ls T.Z) := by
                    rw [← Vec.getElem_eq_idx ls m]
                    exact T.idx_size_lt_P ls T.Z m
                  rw [hn] at hlt
                  exact hlt
                obtain ⟨hchildNF, hchildSD⟩ :=
                  ih (T.size child) hsz child u
                    rfl hchildComp.1 hchildDom
                have hchildFundComp :
                    T.isNFComp childFund := by
                  exact T.NFComp_of_SDom_Z_or_eq
                    childFund child hchildNF
                    hchildComp hchildSD
                have hchildNe : child ≠ T.Z := by
                  intro heq
                  have hc := hchildDom
                  rw [heq] at hc
                  cases hc
                have hchildLt :
                    childFund < child :=
                  T.fund_lt_self child u hchildNe
                have hnf :
                    T.isNF (T.P base T.Z) :=
                  T.rplc_NF_closed
                    ls m childFund ha0
                    hchildFundComp
                have hsd :
                    T.SDom T.Z
                      (T.P base T.Z)
                      (T.P ls T.Z) :=
                  T.SDom_rplc_min_Z
                    ls m Dom.omega childFund
                    hmin hchildFundComp hchildLt
                have hfundEq :
                    T.fund (T.P ls T.Z) u =
                      T.P base T.Z := by
                  conv =>
                    lhs
                    rw [T.fund, if_pos rfl]
                    rw [hmin]
                    change
                      (if Dom.omega = Dom.one then
                        _ else _)
                    rw [if_neg (by
                      intro heq
                      cases heq)]
                    change
                      (if Dom.omega = Dom.Omega then
                        _ else _)
                    rw [if_neg (by
                      intro heq
                      cases heq)]
                  change
                    T.P
                      (ls.rplc m
                        (T.fund (ls.idx m) u))
                      T.Z =
                        T.P base T.Z
                  rfl
                rw [hfundEq]
                exact ⟨hnf, hsd⟩
              | Omega =>
                let child := ls.idx m
                let arg :=
                  T.iter
                    (fun x => T.fund child x) u
                let childFund :=
                  T.fund child arg
                let base := ls.rplc m childFund
                have hchildComp :
                    T.isNFComp child :=
                  hcoords m
                have hchildDom :
                    T.dom child = Dom.Omega := by
                  change
                    T.dom (ls.idx m) = Dom.Omega
                  exact hspec.2.1
                have hchildFundComp :
                    T.isNFComp childFund := by
                  change
                    T.isNFComp
                      (T.fund child
                        (T.iter
                          (fun x => T.fund child x) u))
                  exact T.fund_iter_NFComp_core
                    child u hchildComp hchildDom
                have hchildNe : child ≠ T.Z := by
                  intro heq
                  have hc := hchildDom
                  rw [heq] at hc
                  cases hc
                have hchildLt :
                    childFund < child := by
                  exact T.fund_lt_self
                    child arg hchildNe
                have hnf :
                    T.isNF (T.P base T.Z) :=
                  T.rplc_NF_closed
                    ls m childFund ha0
                    hchildFundComp
                have hsd :
                    T.SDom T.Z
                      (T.P base T.Z)
                      (T.P ls T.Z) :=
                  T.SDom_rplc_min_Z
                    ls m Dom.Omega childFund
                    hmin hchildFundComp hchildLt
                have hfundEq :
                    T.fund (T.P ls T.Z) u =
                      T.P base T.Z := by
                  conv =>
                    lhs
                    rw [T.fund, if_pos rfl]
                    rw [hmin]
                    change
                      (if Dom.Omega = Dom.one then
                        _ else _)
                    rw [if_neg (by
                      intro heq
                      cases heq)]
                    change
                      (if Dom.Omega = Dom.Omega then
                        _ else _)
                    rw [if_pos rfl]
                  change
                    T.P
                      (ls.rplc m
                        (T.fund (ls.idx m)
                          (T.iter
                            (fun x =>
                              T.fund (ls.idx m) x) u)))
                      T.Z =
                        T.P base T.Z
                  rfl
                rw [hfundEq]
                exact ⟨hnf, hsd⟩
          · have hdadd :
                T.dom add = Dom.omega := by
              conv at hdom =>
                lhs
                rw [T.dom, if_neg hadd]
              exact hdom
            have hsz :
                T.size add < n := by
              rw [← hn]
              exact T.add_size_lt_P ls add
            obtain ⟨hnewNF, hnewSD⟩ :=
              ih (T.size add) hsz add u
                rfl h1 hdadd
            have hparentNF :
                T.isNF
                  (T.P ls (T.fund add u)) :=
              T.isNF.p ls (T.fund add u)
                h0 hnewNF h2
                (T.le_trans
                  (T.head (T.fund add u))
                  (T.head add)
                  (T.P ls T.Z)
                  (T.head_fund_le add u) h3)
            have hparentSD :
                T.SDom T.Z
                  (T.P ls (T.fund add u))
                  (T.P ls add) :=
              T.SDom_tail T.Z
                (T.fund add u) add ls hnewSD
            rw [T.fund_P_tail_eq ls add u hadd]
            exact ⟨hparentNF, hparentSD⟩)
  exact main (T.size s) s t rfl hs hd

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
  exact T.fund_iter_NFComp_core s t hs hd

theorem T.fund_NF_closed {lam : Nat} (s t : T lam)
    (hs : T.isNF s)
    (ht : T.dom s = .Omega → T.isNFComp t) :
    T.isNF (T.fund s t) := by
  sorry

end new
