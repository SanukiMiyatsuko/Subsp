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


theorem T.dom_ne_zero_of_P {lam : Nat} (ls : Vec (T lam) lam) (add : T lam) :
    T.dom (T.P ls add) ≠ .zero := by
  induction add with
  | Z =>
    rw [T.dom]
    cases hmin : T.domVecMinIdx ls with
    | none =>
      intro h
      cases h
    | some md =>
      cases md with
      | mk m d =>
        by_cases hd : d = .one
        · rw [if_pos hd]
          by_cases hm : m.val = 0
          · rw [if_pos hm]
            intro h
            cases h
          · rw [if_neg hm]
            intro h
            cases h
        · rw [if_neg hd]
          intro h
          cases h
  | P ls' add' ih =>
    rw [T.dom]
    have hne : T.P ls' add' ≠ T.Z := by
      intro h
      cases h
    rw [if_neg hne]
    exact ih

theorem T.dom_zero_eq_Z {lam : Nat} (s : T lam) (h : T.dom s = .zero) : s = T.Z := by
  cases s with
  | Z => rfl
  | P ls add =>
    exact False.elim ((T.dom_ne_zero_of_P ls add) h)


theorem T.domVecMinIdx_none_all_zero {lam m : Nat} (v : Vec (T lam) m)
    (h : T.domVecMinIdx v = none) :
    ∀ i : Fin m, T.dom (v.idx i) = .zero := by
  induction v with
  | nil =>
    intro i
    exact i.elim0
  | snoc k xs x ih =>
    intro i
    rw [T.domVecMinIdx] at h
    cases hrec : T.domVecMinIdx xs with
    | some md =>
      rw [hrec] at h
      cases h
    | none =>
      rw [hrec] at h
      by_cases hdx : T.dom x = .zero
      · rw [if_pos hdx] at h
        by_cases hi : i.val < k
        · show T.dom (if hlt : i.val < k then Vec.idx xs ⟨i.val, hlt⟩ else x) = .zero
          rw [dite_eq_left hi]
          exact ih hrec ⟨i.val, hi⟩
        · show T.dom (if hlt : i.val < k then Vec.idx xs ⟨i.val, hlt⟩ else x) = .zero
          rw [dite_eq_right hi]
          exact hdx
      · rw [if_neg hdx] at h
        cases h

theorem T.domVecMinIdx_some_spec {lam m : Nat} (v : Vec (T lam) m)
    (i : Fin m) (d : Dom) (h : T.domVecMinIdx v = some (i, d)) :
    T.dom (v.idx i) = d ∧
      ∀ j : Fin m, j.val < i.val → T.dom (v.idx j) = .zero := by
  induction v with
  | nil =>
    exact i.elim0
  | snoc k xs x ih =>
    rw [T.domVecMinIdx] at h
    cases hrec : T.domVecMinIdx xs with
    | some md =>
      cases md with
      | mk i' d' =>
        rw [hrec] at h
        cases h
        have hspec := ih i' d' hrec
        constructor
        · show T.dom
            (if hlt : i'.val < k then Vec.idx xs ⟨i'.val, hlt⟩ else x) = d'
          have hlt : i'.val < k := i'.isLt
          rw [dite_eq_left hlt]
          have heq : (⟨i'.val, hlt⟩ : Fin k) = i' := Fin.eq_of_val_eq rfl
          rw [heq]
          exact hspec.1
        · intro j hj
          have hjk : j.val < k := Nat.lt_of_lt_of_le hj (Nat.le_of_lt_succ i'.isLt)
          show T.dom
              (if hlt : j.val < k then Vec.idx xs ⟨j.val, hlt⟩ else x) = .zero
          rw [dite_eq_left hjk]
          exact hspec.2 ⟨j.val, hjk⟩ hj
    | none =>
      rw [hrec] at h
      by_cases hdx : T.dom x = .zero
      · rw [if_pos hdx] at h
        cases h
      · rw [if_neg hdx] at h
        cases h
        constructor
        · show T.dom
            (if hlt : k < k then Vec.idx xs ⟨k, hlt⟩ else x) = T.dom x
          rw [dite_eq_right (Nat.lt_irrefl k)]
        · intro j hj
          have hjk : j.val < k := hj
          show T.dom
              (if hlt : j.val < k then Vec.idx xs ⟨j.val, hlt⟩ else x) = .zero
          rw [dite_eq_left hjk]
          exact T.domVecMinIdx_none_all_zero xs hrec ⟨j.val, hjk⟩

theorem T.domVecMinIdx_some_ne_zero {lam m : Nat} (v : Vec (T lam) m)
    (i : Fin m) (d : Dom) (h : T.domVecMinIdx v = some (i, d)) :
    d ≠ .zero := by
  induction v with
  | nil =>
    exact i.elim0
  | snoc k xs x ih =>
    rw [T.domVecMinIdx] at h
    cases hrec : T.domVecMinIdx xs with
    | some md =>
      cases md with
      | mk i' d' =>
        rw [hrec] at h
        cases h
        exact ih i' d' hrec
    | none =>
      rw [hrec] at h
      by_cases hdx : T.dom x = .zero
      · rw [if_pos hdx] at h
        cases h
      · rw [if_neg hdx] at h
        cases h
        exact hdx

theorem Vec.rplc_idx_same {A : Type} {n : Nat} (v : Vec A n) (i : Fin n) (a : A) :
    (v.rplc i a).idx i = a := by
  unfold Vec.rplc
  rw [Vec.ofFn_idx]
  rw [if_pos rfl]

theorem Vec.rplc_idx_of_ne {A : Type} {n : Nat} (v : Vec A n)
    (i j : Fin n) (a : A) (h : j.val ≠ i.val) :
    (v.rplc i a).idx j = v.idx j := by
  unfold Vec.rplc
  rw [Vec.ofFn_idx]
  rw [if_neg h]
  rfl

theorem Vec.mem_toList_iff_idx {A : Type} {n : Nat} (v : Vec A n) (x : A) :
    x ∈ Vec.toList v ↔ ∃ i : Fin n, v.idx i = x := by
  induction v with
  | nil =>
    constructor
    · intro h
      exact False.elim (List.not_mem_nil x h)
    · intro h
      cases h with
      | intro i _ => exact i.elim0
  | snoc k xs last ih =>
    constructor
    · intro h
      rw [Vec.toList] at h
      cases List.mem_append.mp h with
      | inl hxs =>
        obtain ⟨i, hi⟩ := ih.mp hxs
        refine ⟨i.castSucc, ?_⟩
        show (if hlt : i.val < k then Vec.idx xs ⟨i.val, hlt⟩ else last) = x
        have hlt : i.val < k := i.isLt
        rw [dite_eq_left hlt]
        have heq : (⟨i.val, hlt⟩ : Fin k) = i := Fin.eq_of_val_eq rfl
        rw [heq]
        exact hi
      | inr hlast =>
        have heq : x = last := List.mem_singleton.mp hlast
        refine ⟨Fin.last k, ?_⟩
        show (if hlt : k < k then Vec.idx xs ⟨k, hlt⟩ else last) = x
        have hnlt : ¬ k < k := Nat.lt_irrefl k
        rw [dite_eq_right hnlt]
        exact heq.symm
    · intro h
      obtain ⟨i, hi⟩ := h
      rw [Vec.toList]
      by_cases hlt : i.val < k
      · apply List.mem_append_left [last]
        apply ih.mpr
        refine ⟨⟨i.val, hlt⟩, ?_⟩
        show Vec.idx xs ⟨i.val, hlt⟩ = x
        show (if h' : i.val < k then Vec.idx xs ⟨i.val, h'⟩ else last) = x at hi
        rw [dite_eq_left hlt] at hi
        exact hi
      · apply List.mem_append_right (Vec.toList xs)
        apply List.mem_singleton.mpr
        have hik : i.val ≤ k := Nat.lt_succ_iff.mp i.isLt
        have hki : k ≤ i.val := Nat.not_lt.mp hlt
        have hval : i.val = k := Nat.le_antisymm hik hki
        show (if h' : i.val < k then Vec.idx xs ⟨i.val, h'⟩ else last) = x at hi
        rw [dite_eq_right hlt] at hi
        exact hi.symm


theorem Vec.compare_lt_of_pivot {lam m : Nat} (v w : Vec (T lam) m) (i : Fin m)
    (heq : ∀ j : Fin m, i.val < j.val → v.idx j = w.idx j)
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
        · have hieq : i = Fin.last k := Fin.eq_of_val_eq hik
          rw [hieq] at hlt
          have hix :
              (Vec.snoc k xs x).idx (Fin.last k) = x := by
            show (if h : k < k then Vec.idx xs ⟨k, h⟩ else x) = x
            rw [dite_eq_right (Nat.lt_irrefl k)]
          have hiy :
              (Vec.snoc k ys y).idx (Fin.last k) = y := by
            show (if h : k < k then Vec.idx ys ⟨k, h⟩ else y) = y
            rw [dite_eq_right (Nat.lt_irrefl k)]
          rw [hix, hiy] at hlt
          show
            (match compareT x y with
            | Ordering.eq => compareVec xs ys
            | ord => ord) = Ordering.lt
          rw [hlt]
        · have hiklt : i.val < k := by
            have hikle : i.val ≤ k := Nat.lt_succ_iff.mp i.isLt
            exact Nat.lt_of_le_of_ne hikle hik
          let i' : Fin k := ⟨i.val, hiklt⟩
          have hlastEq :
              (Vec.snoc k xs x).idx (Fin.last k) =
                (Vec.snoc k ys y).idx (Fin.last k) :=
            heq (Fin.last k) (by exact hiklt)
          have hx : (Vec.snoc k xs x).idx (Fin.last k) = x := by
            show (if h : k < k then Vec.idx xs ⟨k, h⟩ else x) = x
            rw [dite_eq_right (Nat.lt_irrefl k)]
          have hy : (Vec.snoc k ys y).idx (Fin.last k) = y := by
            show (if h : k < k then Vec.idx ys ⟨k, h⟩ else y) = y
            rw [dite_eq_right (Nat.lt_irrefl k)]
          rw [hx, hy] at hlastEq
          have hxy : compareT x y = Ordering.eq := by
            rw [hlastEq]
            exact T_refl y
          have hlt' : xs.idx i' < ys.idx i' := by
            have hv :
                (Vec.snoc k xs x).idx i = xs.idx i' := by
              show
                (if h : i.val < k then Vec.idx xs ⟨i.val, h⟩ else x) =
                  Vec.idx xs i'
              rw [dite_eq_left hiklt]
              rfl
            have hw :
                (Vec.snoc k ys y).idx i = ys.idx i' := by
              show
                (if h : i.val < k then Vec.idx ys ⟨i.val, h⟩ else y) =
                  Vec.idx ys i'
              rw [dite_eq_left hiklt]
              rfl
            rw [hv, hw] at hlt
            exact hlt
          have heq' : ∀ j : Fin k, i'.val < j.val → xs.idx j = ys.idx j := by
            intro j hj
            have hv :
                (Vec.snoc k xs x).idx j.castSucc = xs.idx j := by
              show
                (if h : j.val < k then Vec.idx xs ⟨j.val, h⟩ else x) =
                  Vec.idx xs j
              rw [dite_eq_left j.isLt]
              rfl
            have hw :
                (Vec.snoc k ys y).idx j.castSucc = ys.idx j := by
              show
                (if h : j.val < k then Vec.idx ys ⟨j.val, h⟩ else y) =
                  Vec.idx ys j
              rw [dite_eq_left j.isLt]
              rfl
            have hall := heq j.castSucc hj
            rw [hv, hw] at hall
            exact hall
          have hrec : compareVec xs ys = Ordering.lt :=
            ih xs ys i' heq' hlt'
          show
            (match compareT x y with
            | Ordering.eq => compareVec xs ys
            | ord => ord) = Ordering.lt
          rw [hxy]
          exact hrec


theorem Vec.compare_lt_preserve_from_index {lam m : Nat}
    (a v w : Vec (T lam) m) (q : Fin m)
    (hvw : ∀ j : Fin m, q.val ≤ j.val → v.idx j = w.idx j)
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
              (Vec.snoc k vs vLast).idx (Fin.last k) = vLast := by
            show
              (if h : k < k then Vec.idx vs ⟨k, h⟩ else vLast) = vLast
            rw [dite_eq_right (Nat.lt_irrefl k)]
          have hlastW :
              (Vec.snoc k ws wLast).idx (Fin.last k) = wLast := by
            show
              (if h : k < k then Vec.idx ws ⟨k, h⟩ else wLast) = wLast
            rw [dite_eq_right (Nat.lt_irrefl k)]
          have hvwLast :
              vLast = wLast := by
            have hqk : q.val ≤ k := Nat.le_of_lt_succ q.isLt
            have h := hvw (Fin.last k) hqk
            rw [hlastV, hlastW] at h
            exact h
          show
            (match compareT aLast wLast with
            | Ordering.eq => compareVec as ws
            | ord => ord) = Ordering.lt
          show
            (match compareT aLast vLast with
            | Ordering.eq => compareVec as vs
            | ord => ord) = Ordering.lt at hlt
          cases hc : compareT aLast vLast with
          | lt =>
            have hc' : compareT aLast wLast = Ordering.lt := by
              rw [← hvwLast]
              exact hc
            rw [hc']
          | gt =>
            rw [hc] at hlt
            cases hlt
          | eq =>
            have hc' : compareT aLast wLast = Ordering.eq := by
              rw [← hvwLast]
              exact hc
            rw [hc']
            rw [hc] at hlt
            by_cases hq : q.val = k
            · have hqe : q = Fin.last k := Fin.eq_of_val_eq hq
              have haLast :
                  (Vec.snoc k as aLast).idx (Fin.last k) = aLast := by
                show
                  (if h : k < k then Vec.idx as ⟨k, h⟩ else aLast) = aLast
                rw [dite_eq_right (Nat.lt_irrefl k)]
              rw [hqe, haLast, hlastV] at hne
              have heq : aLast = vLast := T_eq_sound aLast vLast hc
              exact False.elim (hne heq)
            · have hqk : q.val < k := by
                have hle : q.val ≤ k := Nat.le_of_lt_succ q.isLt
                exact Nat.lt_of_le_of_ne hle hq
              let q' : Fin k := ⟨q.val, hqk⟩
              have hne' : as.idx q' ≠ vs.idx q' := by
                intro heq
                apply hne
                show
                  (if h : q.val < k then Vec.idx as ⟨q.val, h⟩ else aLast) ≠
                    (if h : q.val < k then Vec.idx vs ⟨q.val, h⟩ else vLast)
                rw [dite_eq_left hqk, dite_eq_left hqk]
                exact heq
              have hvw' :
                  ∀ j : Fin k, q'.val ≤ j.val →
                    vs.idx j = ws.idx j := by
                intro j hj
                have hv :
                    (Vec.snoc k vs vLast).idx j.castSucc = vs.idx j := by
                  show
                    (if h : j.val < k then Vec.idx vs ⟨j.val, h⟩ else vLast) =
                      Vec.idx vs j
                  rw [dite_eq_left j.isLt]
                  rfl
                have hw :
                    (Vec.snoc k ws wLast).idx j.castSucc = ws.idx j := by
                  show
                    (if h : j.val < k then Vec.idx ws ⟨j.val, h⟩ else wLast) =
                      Vec.idx ws j
                  rw [dite_eq_left j.isLt]
                  rfl
                have hh := hvw j.castSucc hj
                rw [hv, hw] at hh
                exact hh
              exact ih as vs ws q' hvw' hne' hlt

theorem Vec.compare_lt_after_pivot_update {lam m : Nat}
    (a old newv : Vec (T lam) m) (i : Fin m)
    (heqAbove :
      ∀ j : Fin m, i.val < j.val → old.idx j = newv.idx j)
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
          show
            (match compareT aLast oLast with
            | Ordering.eq => compareVec as os
            | ord => ord) = Ordering.lt at hold
          by_cases hik : i.val = k
          · have hieq : i = Fin.last k := Fin.eq_of_val_eq hik
            have haLast :
                (Vec.snoc k as aLast).idx (Fin.last k) = aLast := by
              show
                (if h : k < k then Vec.idx as ⟨k, h⟩ else aLast) = aLast
              rw [dite_eq_right (Nat.lt_irrefl k)]
            have hnLast :
                (Vec.snoc k ns nLast).idx (Fin.last k) = nLast := by
              show
                (if h : k < k then Vec.idx ns ⟨k, h⟩ else nLast) = nLast
              rw [dite_eq_right (Nat.lt_irrefl k)]
            rw [hieq, haLast, hnLast] at hpivot
            rw [hpivot]
          · have hiklt : i.val < k := by
              have hle : i.val ≤ k := Nat.le_of_lt_succ i.isLt
              exact Nat.lt_of_le_of_ne hle hik
            have hoLast :
                (Vec.snoc k os oLast).idx (Fin.last k) = oLast := by
              show
                (if h : k < k then Vec.idx os ⟨k, h⟩ else oLast) = oLast
              rw [dite_eq_right (Nat.lt_irrefl k)]
            have hnLast :
                (Vec.snoc k ns nLast).idx (Fin.last k) = nLast := by
              show
                (if h : k < k then Vec.idx ns ⟨k, h⟩ else nLast) = nLast
              rw [dite_eq_right (Nat.lt_irrefl k)]
            have hon : oLast = nLast := by
              have hh := heqAbove (Fin.last k) hiklt
              rw [hoLast, hnLast] at hh
              exact hh
            cases hc : compareT aLast oLast with
            | lt =>
              have hc' : compareT aLast nLast = Ordering.lt := by
                rw [← hon]
                exact hc
              rw [hc']
            | gt =>
              rw [hc] at hold
              cases hold
            | eq =>
              have hc' : compareT aLast nLast = Ordering.eq := by
                rw [← hon]
                exact hc
              rw [hc']
              rw [hc] at hold
              let i' : Fin k := ⟨i.val, hiklt⟩
              have hpivot' : as.idx i' < ns.idx i' := by
                show
                  (if h : i.val < k then Vec.idx as ⟨i.val, h⟩ else aLast) <
                    (if h : i.val < k then Vec.idx ns ⟨i.val, h⟩ else nLast) at hpivot
                rw [dite_eq_left hiklt, dite_eq_left hiklt] at hpivot
                exact hpivot
              have heqAbove' :
                  ∀ j : Fin k, i'.val < j.val →
                    os.idx j = ns.idx j := by
                intro j hj
                have ho :
                    (Vec.snoc k os oLast).idx j.castSucc = os.idx j := by
                  show
                    (if h : j.val < k then Vec.idx os ⟨j.val, h⟩ else oLast) =
                      Vec.idx os j
                  rw [dite_eq_left j.isLt]
                  rfl
                have hn :
                    (Vec.snoc k ns nLast).idx j.castSucc = ns.idx j := by
                  show
                    (if h : j.val < k then Vec.idx ns ⟨j.val, h⟩ else nLast) =
                      Vec.idx ns j
                  rw [dite_eq_left j.isLt]
                  rfl
                have hh := heqAbove j.castSucc hj
                rw [ho, hn] at hh
                exact hh
              exact ih as os ns i' heqAbove' hold hpivot'

theorem T.P_vector_field_ne_self {lam : Nat}
    (xs : Vec (T lam) lam) (add : T lam) (q : Fin lam) :
    xs.idx q ≠ T.P xs add := by
  intro heq
  have hlt : T.size (xs.idx q) < Vec.size xs :=
    Vec.idx_size_lt xs q
  rw [heq] at hlt
  have hge : Vec.size xs ≤ T.size (T.P xs add) := by
    show Vec.size xs ≤ 1 + Vec.size xs + T.size add
    have h1 : Vec.size xs ≤ 1 + Vec.size xs :=
      Nat.le_add_left (Vec.size xs) 1
    have h2 :
        1 + Vec.size xs ≤ 1 + Vec.size xs + T.size add :=
      Nat.le_add_right _ _
    exact Nat.le_trans h1 h2
  exact (Nat.not_lt_of_ge hge) hlt

theorem T.coord_lt_preserved_below_update {lam : Nat}
    (old newv : Vec (T lam) lam) (q : Fin lam)
    (heq :
      ∀ j : Fin lam, q.val ≤ j.val → old.idx j = newv.idx j)
    (hold : old.idx q < T.P old T.Z) :
    old.idx q < T.P newv T.Z := by
  cases hx : old.idx q with
  | Z =>
    show compareT T.Z (T.P newv T.Z) = Ordering.lt
    rfl
  | P xs add =>
    show
      (match compareVec xs newv with
      | Ordering.eq => compareT add T.Z
      | ord => ord) = Ordering.lt
    have hold' :
      (match compareVec xs old with
      | Ordering.eq => compareT add T.Z
      | ord => ord) = Ordering.lt := by
      rw [← hx]
      exact hold
    cases hc : compareVec xs old with
    | lt =>
      have hne : xs.idx q ≠ old.idx q := by
        rw [hx]
        exact T.P_vector_field_ne_self xs add q
      have hpres :
          compareVec xs newv = Ordering.lt :=
        Vec.compare_lt_preserve_from_index xs old newv q
          heq hne hc
      rw [hpres]
    | gt =>
      rw [hc] at hold'
      cases hold'
    | eq =>
      rw [hc] at hold'
      cases add with
      | Z =>
        show compareT T.Z T.Z = Ordering.lt at hold'
        rw [T_refl T.Z] at hold'
        cases hold'
      | P als aadd =>
        show compareT (T.P als aadd) T.Z = Ordering.lt at hold'
        cases hold'

theorem T.pivot_term_lt_updated_parent {lam : Nat}
    (old newv : Vec (T lam) lam) (i : Fin lam)
    (z : T lam)
    (heqAbove :
      ∀ j : Fin lam, i.val < j.val → old.idx j = newv.idx j)
    (hnewi : newv.idx i = z)
    (hzold : z < T.P old T.Z)
    (hzcomp : T.isNFComp z) :
    z < T.P newv T.Z := by
  cases hz : z with
  | Z =>
    show compareT T.Z (T.P newv T.Z) = Ordering.lt
    rfl
  | P zs zadd =>
    have hzold' :
        (match compareVec zs old with
        | Ordering.eq => compareT zadd T.Z
        | ord => ord) = Ordering.lt := by
      rw [← hz]
      exact hzold
    have hcmpOld : compareVec zs old = Ordering.lt := by
      cases hc : compareVec zs old with
      | lt => exact hc
      | gt =>
        rw [hc] at hzold'
        cases hzold'
      | eq =>
        rw [hc] at hzold'
        cases zadd with
        | Z =>
          show compareT T.Z T.Z = Ordering.lt at hzold'
          rw [T_refl T.Z] at hzold'
          cases hzold'
        | P als aadd =>
          show compareT (T.P als aadd) T.Z = Ordering.lt at hzold'
          cases hzold'
    have hziMem : zs.idx i ∈ Vec.toList zs := by
      apply (Vec.mem_toList_iff_idx zs (zs.idx i)).mpr
      exact ⟨i, rfl⟩
    have hziG : zs.idx i ∈ T.G z := by
      rw [hz]
      apply (T.mem_G_P zs zadd (zs.idx i)).mpr
      exact Or.inl ⟨zs.idx i, hziMem, Or.inl rfl⟩
    have hpivot0 : zs.idx i < z :=
      hzcomp.2 (zs.idx i) hziG
    have hpivot : zs.idx i < newv.idx i := by
      rw [hnewi]
      exact hpivot0
    have hcmpNew :
        compareVec zs newv = Ordering.lt :=
      Vec.compare_lt_after_pivot_update
        zs old newv i heqAbove hcmpOld hpivot
    show
      (match compareVec zs newv with
      | Ordering.eq => compareT zadd T.Z
      | ord => ord) = Ordering.lt
    rw [hcmpNew]

theorem Vec.compare_rplc_lt {lam m : Nat} (v : Vec (T lam) m)
    (i : Fin m) (a : T lam) (h : a < v.idx i) :
    compareVec (v.rplc i a) v = Ordering.lt := by
  apply Vec.compare_lt_of_pivot (v.rplc i a) v i
  · intro j hj
    exact Vec.rplc_idx_of_ne v i j a (Nat.ne_of_gt hj)
  · rw [Vec.rplc_idx_same]
    exact h

theorem Vec.compare_rplc_rplc_lt {lam m : Nat} (v : Vec (T lam) m)
    (i j : Fin m) (a b : T lam) (hji : j.val < i.val)
    (ha : a < v.idx i) :
    compareVec ((v.rplc i a).rplc j b) v = Ordering.lt := by
  apply Vec.compare_lt_of_pivot ((v.rplc i a).rplc j b) v i
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

theorem T.P_lt_P_of_compareVec_lt {lam : Nat}
    (v w : Vec (T lam) lam) (a b : T lam)
    (h : compareVec v w = Ordering.lt) :
    T.P v a < T.P w b := by
  show compareT (T.P v a) (T.P w b) = Ordering.lt
  show
    (match compareVec v w with
    | Ordering.eq => compareT a b
    | ord => ord) = Ordering.lt
  rw [h]

theorem Vec.compare_lt_has_pivot {lam m : Nat}
    (v w : Vec (T lam) m) (h : compareVec v w = Ordering.lt) :
    ∃ i : Fin m,
      (∀ j : Fin m, i.val < j.val → v.idx j = w.idx j) ∧
      v.idx i < w.idx i := by
  induction v generalizing w with
  | nil =>
    cases w with
    | nil =>
      cases h
  | snoc k xs x ih =>
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
          have hjle : j.val ≤ k := Nat.lt_succ_iff.mp j.isLt
          exact False.elim ((Nat.not_lt_of_ge hjle) hj)
        · have hv :
              (Vec.snoc k xs x).idx (Fin.last k) = x := by
            show
              (if hlt : k < k then Vec.idx xs ⟨k, hlt⟩ else x) = x
            rw [dite_eq_right (Nat.lt_irrefl k)]
          have hw :
              (Vec.snoc k ys y).idx (Fin.last k) = y := by
            show
              (if hlt : k < k then Vec.idx ys ⟨k, hlt⟩ else y) = y
            rw [dite_eq_right (Nat.lt_irrefl k)]
          rw [hv, hw]
          exact hc
      | eq =>
        rw [hc] at h
        obtain ⟨i, hiEq, hiLt⟩ := ih ys h
        refine ⟨i.castSucc, ?_, ?_⟩
        · intro j hj
          by_cases hjk : j.val < k
          · have hv :
                (Vec.snoc k xs x).idx j =
                  xs.idx ⟨j.val, hjk⟩ := by
              show
                (if hlt : j.val < k then
                    Vec.idx xs ⟨j.val, hlt⟩ else x) =
                  Vec.idx xs ⟨j.val, hjk⟩
              rw [dite_eq_left hjk]
              rfl
            have hw :
                (Vec.snoc k ys y).idx j =
                  ys.idx ⟨j.val, hjk⟩ := by
              show
                (if hlt : j.val < k then
                    Vec.idx ys ⟨j.val, hlt⟩ else y) =
                  Vec.idx ys ⟨j.val, hjk⟩
              rw [dite_eq_left hjk]
              rfl
            rw [hv, hw]
            exact hiEq ⟨j.val, hjk⟩ hj
          · have hjle : j.val ≤ k := Nat.lt_succ_iff.mp j.isLt
            have hkj : k ≤ j.val := Nat.not_lt.mp hjk
            have hjval : j.val = k := Nat.le_antisymm hjle hkj
            have hjeq : j = Fin.last k := Fin.eq_of_val_eq hjval
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
              (Vec.snoc k xs x).idx i.castSucc = xs.idx i := by
            show
              (if hlt : i.val < k then
                  Vec.idx xs ⟨i.val, hlt⟩ else x) =
                Vec.idx xs i
            rw [dite_eq_left i.isLt]
            rfl
          have hw :
              (Vec.snoc k ys y).idx i.castSucc = ys.idx i := by
            show
              (if hlt : i.val < k then
                  Vec.idx ys ⟨i.val, hlt⟩ else y) =
                Vec.idx ys i
            rw [dite_eq_left i.isLt]
            rfl
          rw [hv, hw]
          exact hiLt
      | gt =>
        rw [hc] at h
        cases h

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


theorem T.mul_PZ_lt_of_compareVec_lt {lam : Nat}
    (u v : Vec (T lam) lam) (t : T lam)
    (h : compareVec u v = Ordering.lt) :
    T.mul (T.P u T.Z) t < T.P v T.Z := by
  cases t with
  | Z =>
    show compareT T.Z (T.P v T.Z) = Ordering.lt
    rfl
  | P tls add =>
    rw [T.mul]
    rw [T.oplus]
    exact T.P_lt_P_of_compareVec_lt u v (T.mul (T.P u T.Z) add) T.Z h

theorem T.fund_lt_self {lam : Nat} (s t : T lam) (hne : s ≠ T.Z) :
    T.fund s t < s := by
  have main :
      ∀ n : Nat, ∀ a b : T lam, T.size a = n → a ≠ T.Z →
        T.fund a b < a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a b hsize hanz
      cases a with
      | Z =>
        exact False.elim (hanz rfl)
      | P ls add =>
        by_cases hadd : add = T.Z
        · rw [hadd]
          rw [T.fund]
          rw [if_pos rfl]
          cases hmin : T.domVecMinIdx ls with
          | none =>
            rw [hmin]
            show compareT T.Z (T.P ls T.Z) = Ordering.lt
            rfl
          | some md =>
            cases md with
            | mk m d =>
              rw [hmin]
              have hdne : d ≠ .zero :=
                T.domVecMinIdx_some_ne_zero ls m d hmin
              have hspec := T.domVecMinIdx_some_spec ls m d hmin
              have hmne : ls[m] ≠ T.Z := by
                intro heq
                have hdom : T.dom (ls.idx m) = d := hspec.1
                rw [Vec.getElem_eq_idx] at heq
                rw [heq] at hdom
                have : d = .zero := hdom.symm
                exact hdne this
              have hmsize : T.size ls[m] < n := by
                have hlt := T.idx_size_lt_P ls T.Z m
                rw [hsize] at hlt
                exact hlt
              by_cases hd1 : d = .one
              · rw [if_pos hd1]
                cases m with
                | mk mv mh =>
                  cases mv with
                  | zero =>
                    have hrec :
                        T.fund ls[⟨0, mh⟩] T.Z < ls[⟨0, mh⟩] :=
                      ih (T.size ls[⟨0, mh⟩]) hmsize
                        ls[⟨0, mh⟩] T.Z rfl hmne
                    have hrecIdx :
                        T.fund ls[⟨0, mh⟩] T.Z <
                          ls.idx ⟨0, mh⟩ := by
                      rw [← Vec.getElem_eq_idx ls ⟨0, mh⟩]
                      exact hrec
                    have hvec :
                        compareVec
                          (ls.rplc ⟨0, mh⟩
                            (T.fund ls[⟨0, mh⟩] T.Z)) ls =
                          Ordering.lt :=
                      Vec.compare_rplc_lt ls ⟨0, mh⟩
                        (T.fund ls[⟨0, mh⟩] T.Z) hrecIdx
                    exact T.mul_PZ_lt_of_compareVec_lt
                      (ls.rplc ⟨0, mh⟩ (T.fund ls[⟨0, mh⟩] T.Z))
                      ls b hvec
                  | succ m' =>
                    have hrec :
                        T.fund ls[⟨m' + 1, mh⟩] T.Z <
                          ls[⟨m' + 1, mh⟩] :=
                      ih (T.size ls[⟨m' + 1, mh⟩]) hmsize
                        ls[⟨m' + 1, mh⟩] T.Z rfl hmne
                    have hrecIdx :
                        T.fund ls[⟨m' + 1, mh⟩] T.Z <
                          ls.idx ⟨m' + 1, mh⟩ := by
                      rw [← Vec.getElem_eq_idx ls ⟨m' + 1, mh⟩]
                      exact hrec
                    let j : Fin lam := ⟨m', Nat.lt_of_succ_lt mh⟩
                    have hvec :
                        compareVec
                          ((ls.rplc ⟨m' + 1, mh⟩
                            (T.fund ls[⟨m' + 1, mh⟩] T.Z)).rplc j b)
                          ls = Ordering.lt :=
                      Vec.compare_rplc_rplc_lt ls
                        ⟨m' + 1, mh⟩ j
                        (T.fund ls[⟨m' + 1, mh⟩] T.Z) b
                        (Nat.lt_succ_self m') hrecIdx
                    exact T.P_lt_P_of_compareVec_lt
                      ((ls.rplc ⟨m' + 1, mh⟩
                        (T.fund ls[⟨m' + 1, mh⟩] T.Z)).rplc j b)
                      ls T.Z T.Z hvec
              · rw [if_neg hd1]
                by_cases hdO : d = .Omega
                · rw [if_pos hdO]
                  let arg :=
                    T.iter (fun x => T.fund ls[m] x) b
                  have hrec :
                      T.fund ls[m] arg < ls[m] :=
                    ih (T.size ls[m]) hmsize
                      ls[m] arg rfl hmne
                  have hrecIdx :
                      T.fund ls[m] arg < ls.idx m := by
                    rw [← Vec.getElem_eq_idx ls m]
                    exact hrec
                  have hvec :
                      compareVec
                        (ls.rplc m (T.fund ls[m] arg)) ls =
                        Ordering.lt :=
                    Vec.compare_rplc_lt ls m
                      (T.fund ls[m] arg) hrecIdx
                  exact T.P_lt_P_of_compareVec_lt
                    (ls.rplc m (T.fund ls[m] arg))
                    ls T.Z T.Z hvec
                · rw [if_neg hdO]
                  have hrec :
                      T.fund ls[m] b < ls[m] :=
                    ih (T.size ls[m]) hmsize
                      ls[m] b rfl hmne
                  have hrecIdx :
                      T.fund ls[m] b < ls.idx m := by
                    rw [← Vec.getElem_eq_idx ls m]
                    exact hrec
                  have hvec :
                      compareVec
                        (ls.rplc m (T.fund ls[m] b)) ls =
                        Ordering.lt :=
                    Vec.compare_rplc_lt ls m
                      (T.fund ls[m] b) hrecIdx
                  exact T.P_lt_P_of_compareVec_lt
                    (ls.rplc m (T.fund ls[m] b))
                    ls T.Z T.Z hvec
        · rw [T.fund]
          rw [if_neg hadd]
          have haddsize : T.size add < n := by
            have hlt := T.add_size_lt_P ls add
            rw [hsize] at hlt
            exact hlt
          have hrec : T.fund add b < add :=
            ih (T.size add) haddsize add b rfl hadd
          show compareT (T.P ls (T.fund add b)) (T.P ls add) =
            Ordering.lt
          rw [show compareVec ls ls = Ordering.eq from Vec_refl ls]
          exact hrec
  exact main (T.size s) s t rfl hne

theorem T.head_mono {lam : Nat} (a b : T lam) (h : a < b) :
    T.head a ≤ T.head b := by
  cases a with
  | Z =>
    exact T.Z_le (T.head b)
  | P als aadd =>
    cases b with
    | Z =>
      show compareT (T.P als aadd) T.Z = Ordering.lt at h
      cases h
    | P bls badd =>
      show
        (match compareVec als bls with
        | Ordering.eq => compareT aadd badd
        | ord => ord) = Ordering.lt at h
      cases hc : compareVec als bls with
      | lt =>
        exact Or.inl (T.P_lt_P_of_compareVec_lt als bls T.Z T.Z hc)
      | eq =>
        have hls : als = bls := Vec_eq_sound als bls hc
        rw [hls]
        exact Or.inr rfl
      | gt =>
        rw [hc] at h
        cases h

theorem T.head_fund_le {lam : Nat} (s t : T lam) :
    T.head (T.fund s t) ≤ T.head s := by
  cases s with
  | Z =>
    rw [T.fund]
    exact T.Z_le T.Z
  | P ls add =>
    have hne : T.P ls add ≠ T.Z := by
      intro h
      cases h
    exact T.head_mono (T.fund (T.P ls add) t) (T.P ls add)
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

def Vec.GAll {lam m : Nat} : Vec (T lam) m → List (T lam)
| .nil => []
| .snoc _ v last => Vec.GAll v ++ [last] ++ T.G last

theorem T.G_P_eq {lam : Nat} (ls : Vec (T lam) lam) (add : T lam) :
    T.G (T.P ls add) = Vec.GAll ls ++ T.G add := by
  rfl

theorem Vec.GAll_mem_iff {lam m : Nat} (v : Vec (T lam) m) (y : T lam) :
    y ∈ Vec.GAll v ↔
      ∃ i : Fin m, y = v.idx i ∨ y ∈ T.G (v.idx i) := by
  induction v with
  | nil =>
    constructor
    · intro h
      exact False.elim (List.not_mem_nil y h)
    · intro h
      obtain ⟨i, _⟩ := h
      exact i.elim0
  | snoc k xs x ih =>
    rw [Vec.GAll]
    constructor
    · intro h
      rw [List.mem_append, List.mem_append] at h
      cases h with
      | inl hleft =>
        cases hleft with
        | inl hxs =>
          obtain ⟨i, hi⟩ := ih.mp hxs
          refine ⟨i.castSucc, ?_⟩
          have hidx :
              (Vec.snoc k xs x).idx i.castSucc = xs.idx i := by
            show
              (if hlt : i.val < k then Vec.idx xs ⟨i.val, hlt⟩ else x) =
                Vec.idx xs i
            rw [dite_eq_left i.isLt]
            rfl
          rw [hidx]
          exact hi
        | inr hx =>
          have heq : y = x := List.mem_singleton.mp hx
          refine ⟨Fin.last k, Or.inl ?_⟩
          have hidx :
              (Vec.snoc k xs x).idx (Fin.last k) = x := by
            show
              (if hlt : k < k then Vec.idx xs ⟨k, hlt⟩ else x) = x
            rw [dite_eq_right (Nat.lt_irrefl k)]
          rw [hidx]
          exact heq
      | inr hGx =>
        refine ⟨Fin.last k, Or.inr ?_⟩
        have hidx :
            (Vec.snoc k xs x).idx (Fin.last k) = x := by
          show
            (if hlt : k < k then Vec.idx xs ⟨k, hlt⟩ else x) = x
          rw [dite_eq_right (Nat.lt_irrefl k)]
        rw [hidx]
        exact hGx
    · intro h
      obtain ⟨i, hi⟩ := h
      by_cases hik : i.val < k
      · have hidx :
            (Vec.snoc k xs x).idx i = xs.idx ⟨i.val, hik⟩ := by
          show
            (if hlt : i.val < k then Vec.idx xs ⟨i.val, hlt⟩ else x) =
              Vec.idx xs ⟨i.val, hik⟩
          rw [dite_eq_left hik]
          rfl
        rw [hidx] at hi
        apply List.mem_append_left (T.G x)
        apply List.mem_append_left [x]
        apply ih.mpr
        exact ⟨⟨i.val, hik⟩, hi⟩
      · have hikle : i.val ≤ k := Nat.lt_succ_iff.mp i.isLt
        have hk : k ≤ i.val := Nat.not_lt.mp hik
        have hval : i.val = k := Nat.le_antisymm hikle hk
        have hieq : i = Fin.last k := Fin.eq_of_val_eq hval
        rw [hieq] at hi
        have hidx :
            (Vec.snoc k xs x).idx (Fin.last k) = x := by
          show
            (if hlt : k < k then Vec.idx xs ⟨k, hlt⟩ else x) = x
          rw [dite_eq_right (Nat.lt_irrefl k)]
        rw [hidx] at hi
        cases hi with
        | inl hyx =>
          apply List.mem_append_left (T.G x)
          apply List.mem_append_right (Vec.GAll xs)
          exact List.mem_singleton.mpr hyx
        | inr hGx =>
          exact List.mem_append_right (Vec.GAll xs ++ [x]) hGx

inductive T.isNF {lam : Nat} : T lam → Prop where
| z : isNF Z
| p (ls : Vec (T lam) lam) (add : T lam)
  (h0 : ∀ x ∈ Vec.toList ls, isNF x) (h1 : isNF add)
  (h2 : ∀ x ∈ Vec.toList ls, ∀ y ∈ G x, y < x)
  (h3 : head add ≤ P ls Z) : isNF (P ls add)

def T.decidableBAllLt {lam : Nat} (l : List (T lam)) (x : T lam) :
    Decidable (∀ y ∈ l, y < x) :=
  match l with
  | [] => isTrue (fun y hy => False.elim (List.not_mem_nil y hy))
  | y :: ys =>
    match (inferInstance : Decidable (y < x)) with
    | isFalse hny => isFalse (fun h => hny (h y List.mem_cons_self))
    | isTrue hy =>
      match T.decidableBAllLt ys x with
      | isFalse hnys =>
        isFalse (fun h => hnys (fun z hz => h z (List.mem_cons_of_mem y hz)))
      | isTrue hys =>
        isTrue (fun z hz =>
          match List.mem_cons.mp hz with
          | Or.inl heq => heq ▸ hy
          | Or.inr hmem => hys z hmem)

def Vec.decidableAllG {lam m : Nat} (v : Vec (T lam) m) :
    Decidable (∀ x ∈ Vec.toList v, ∀ y ∈ T.G x, y < x) :=
  match v with
  | .nil => isTrue (fun x hx => False.elim (List.not_mem_nil x hx))
  | .snoc _ xs x =>
    match Vec.decidableAllG xs with
    | isFalse hnxs =>
      isFalse (fun h =>
        hnxs (fun y hy =>
          h y (List.mem_append_left [x] hy)))
    | isTrue hxs =>
      match T.decidableBAllLt (T.G x) x with
      | isFalse hnx =>
        isFalse (fun h =>
          hnx (h x (List.mem_append_right (Vec.toList xs) (List.mem_singleton_self x))))
      | isTrue hx =>
        isTrue (fun y hy =>
          match List.mem_append.mp hy with
          | Or.inl hmem => hxs y hmem
          | Or.inr hmem =>
            have heq : y = x := List.mem_singleton.mp hmem
            heq ▸ hx)

mutual
  def T.decIsNF {lam : Nat} (s : T lam) : Decidable (T.isNF s) :=
    match s with
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
          match Vec.decidableAllG ls with
          | isFalse hn2 =>
            isFalse (fun h =>
              match h with
              | .p _ _ _ _ h2 _ => hn2 h2)
          | isTrue h2 =>
            match (inferInstance : Decidable (T.head add ≤ T.P ls T.Z)) with
            | isFalse hn3 =>
              isFalse (fun h =>
                match h with
                | .p _ _ _ _ _ h3 => hn3 h3)
            | isTrue h3 => isTrue (T.isNF.p ls add h0 h1 h2 h3)

  def Vec.decAllNF {lam m : Nat} (v : Vec (T lam) m) :
      Decidable (∀ x ∈ Vec.toList v, T.isNF x) :=
    match v with
    | .nil => isTrue (fun x hx => False.elim (List.not_mem_nil x hx))
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
            hnx (h x (List.mem_append_right (Vec.toList xs) (List.mem_singleton_self x))))
        | isTrue hx =>
          isTrue (fun y hy =>
            match List.mem_append.mp hy with
            | Or.inl hmem => hxs y hmem
            | Or.inr hmem =>
              have heq : y = x := List.mem_singleton.mp hmem
              heq ▸ hx)
end

instance {lam : Nat} (s : T lam) : Decidable (T.isNF s) := T.decIsNF s

def T.isNFComp {lam : Nat} (s : T lam) : Prop :=
  T.isNF s ∧ ∀ y ∈ T.G s, y < s



theorem Vec.mem_Gres {lam m : Nat} (v : Vec (T lam) m) (y : T lam) :
    y ∈
      (let rec res {q : Nat} (vt : Vec (T lam) q) : List (T lam) :=
        match vt with
        | .nil => []
        | .snoc n xs last => res xs ++ [last] ++ T.G last
      res v) ↔
    ∃ x, x ∈ Vec.toList v ∧ (y = x ∨ y ∈ T.G x) := by
  induction v with
  | nil =>
    constructor
    · intro h
      exact False.elim (List.not_mem_nil y h)
    · intro h
      obtain ⟨x, hx, _⟩ := h
      exact False.elim (List.not_mem_nil x hx)
  | snoc k xs last ih =>
    change
      y ∈
          ((let rec res {q : Nat} (vt : Vec (T lam) q) : List (T lam) :=
            match vt with
            | .nil => []
            | .snoc n us z => res us ++ [z] ++ T.G z
          res xs) ++ [last] ++ T.G last) ↔
        ∃ x, x ∈ (Vec.toList xs ++ [last]) ∧
          (y = x ∨ y ∈ T.G x)
    constructor
    · intro hy
      have hy' :
          y ∈
            (let rec res {q : Nat} (vt : Vec (T lam) q) : List (T lam) :=
              match vt with
              | .nil => []
              | .snoc n us z => res us ++ [z] ++ T.G z
            res xs) ∨
          y ∈ [last] ∨ y ∈ T.G last := by
        cases List.mem_append.mp hy with
        | inl hleft =>
          cases List.mem_append.mp hleft with
          | inl hres => exact Or.inl hres
          | inr hlast => exact Or.inr (Or.inl hlast)
        | inr hg => exact Or.inr (Or.inr hg)
      cases hy' with
      | inl hres =>
        obtain ⟨x, hx, hxy⟩ := ih.mp hres
        refine ⟨x, List.mem_append_left [last] hx, hxy⟩
      | inr hr =>
        cases hr with
        | inl hlast =>
          have heq : y = last := List.mem_singleton.mp hlast
          refine ⟨last, List.mem_append_right (Vec.toList xs)
            (List.mem_singleton_self last), Or.inl heq⟩
        | inr hg =>
          refine ⟨last, List.mem_append_right (Vec.toList xs)
            (List.mem_singleton_self last), Or.inr hg⟩
    · intro h
      obtain ⟨x, hx, hxy⟩ := h
      cases List.mem_append.mp hx with
      | inl hxs =>
        have hres :
            y ∈
              (let rec res {q : Nat} (vt : Vec (T lam) q) : List (T lam) :=
                match vt with
                | .nil => []
                | .snoc n us z => res us ++ [z] ++ T.G z
              res xs) :=
          ih.mpr ⟨x, hxs, hxy⟩
        exact List.mem_append_left (T.G last)
          (List.mem_append_left [last] hres)
      | inr hlast =>
        have heq : x = last := List.mem_singleton.mp hlast
        rw [heq] at hxy
        cases hxy with
        | inl hylast =>
          exact List.mem_append_left (T.G last)
            (List.mem_append_right
              (let rec res {q : Nat} (vt : Vec (T lam) q) : List (T lam) :=
                match vt with
                | .nil => []
                | .snoc n us z => res us ++ [z] ++ T.G z
              res xs)
              (List.mem_singleton.mpr hylast))
        | inr hyg =>
          exact List.mem_append_right
            ((let rec res {q : Nat} (vt : Vec (T lam) q) : List (T lam) :=
              match vt with
              | .nil => []
              | .snoc n us z => res us ++ [z] ++ T.G z
            res xs) ++ [last]) hyg

theorem T.mem_G_P {lam : Nat} (ls : Vec (T lam) lam) (add y : T lam) :
    y ∈ T.G (T.P ls add) ↔
      (∃ x, x ∈ Vec.toList ls ∧ (y = x ∨ y ∈ T.G x)) ∨
      y ∈ T.G add := by
  change
    y ∈
        ((let rec res {q : Nat} (vt : Vec (T lam) q) : List (T lam) :=
          match vt with
          | .nil => []
          | .snoc n xs last => res xs ++ [last] ++ T.G last
        res ls) ++ T.G add) ↔
      (∃ x, x ∈ Vec.toList ls ∧ (y = x ∨ y ∈ T.G x)) ∨
        y ∈ T.G add
  constructor
  · intro hy
    cases List.mem_append.mp hy with
    | inl hres => exact Or.inl ((Vec.mem_Gres ls y).mp hres)
    | inr hadd => exact Or.inr hadd
  · intro hy
    cases hy with
    | inl hres =>
      exact List.mem_append_left (T.G add)
        ((Vec.mem_Gres ls y).mpr hres)
    | inr hadd =>
      exact List.mem_append_right
        (let rec res {q : Nat} (vt : Vec (T lam) q) : List (T lam) :=
          match vt with
          | .nil => []
          | .snoc n xs last => res xs ++ [last] ++ T.G last
        res ls) hadd

theorem T.isNF_G_isNFComp {lam : Nat} (s : T lam)
    (hs : T.isNF s) :
    ∀ x ∈ T.G s, T.isNFComp x := by
  induction hs with
  | z =>
    intro x hx
    rw [T.G] at hx
    exact False.elim (List.not_mem_nil x hx)
  | p ls add h0 h1 h2 h3 ih0 ih1 =>
    intro x hx
    cases (T.mem_G_P ls add x).mp hx with
    | inl hv =>
      obtain ⟨q, hq, hcase⟩ := hv
      cases hcase with
      | inl hxq =>
        rw [hxq]
        constructor
        · exact h0 q hq
        · exact h2 q hq
      | inr hxG =>
        exact ih0 q hq x hxG
    | inr hxG =>
      exact ih1 x hxG

theorem T.isNFComp_Z {lam : Nat} : T.isNFComp (T.Z : T lam) := by
  constructor
  · exact T.isNF.z
  · intro y hy
    rw [T.G] at hy
    exact False.elim (List.not_mem_nil y hy)

theorem T.isNF_P_coord_NFComp {lam : Nat} (ls : Vec (T lam) lam) (add : T lam)
    (h : T.isNF (T.P ls add)) :
    ∀ i : Fin lam, T.isNFComp (ls.idx i) := by
  cases h with
  | p _ _ h0 h1 h2 h3 =>
    intro i
    have hmem : ls.idx i ∈ Vec.toList ls := by
      apply (Vec.mem_toList_iff_idx ls (ls.idx i)).mpr
      exact ⟨i, rfl⟩
    constructor
    · exact h0 (ls.idx i) hmem
    · exact h2 (ls.idx i) hmem

theorem T.isNF_PZ_of_coords {lam : Nat} (ls : Vec (T lam) lam)
    (h : ∀ i : Fin lam, T.isNFComp (ls.idx i)) :
    T.isNF (T.P ls T.Z) := by
  apply T.isNF.p ls T.Z
  · intro x hx
    obtain ⟨i, hi⟩ := (Vec.mem_toList_iff_idx ls x).mp hx
    rw [← hi]
    exact (h i).1
  · exact T.isNF.z
  · intro x hx y hy
    obtain ⟨i, hi⟩ := (Vec.mem_toList_iff_idx ls x).mp hx
    rw [← hi] at hy
    have hc := (h i).2 y hy
    rw [hi] at hc
    exact hc
  · exact T.Z_le (T.P ls T.Z)



theorem T.term_lt_P_of_self_at {lam : Nat}
    (x : T lam) (v w : Vec (T lam) lam) (q : Fin lam)
    (hx : T.isNFComp x)
    (hold : x < T.P v T.Z)
    (hwq : w.idx q = x)
    (hhigh : ∀ j : Fin lam, q.val < j.val → w.idx j = v.idx j) :
    x < T.P w T.Z := by
  cases x with
  | Z =>
    show compareT T.Z (T.P w T.Z) = Ordering.lt
    rfl
  | P xs xadd =>
    have hvlt : compareVec xs v = Ordering.lt := by
      show
        (match compareVec xs v with
        | Ordering.eq => compareT xadd T.Z
        | ord => ord) = Ordering.lt at hold
      cases hc : compareVec xs v with
      | lt =>
        exact hc
      | eq =>
        rw [hc] at hold
        cases xadd <;> cases hold
      | gt =>
        rw [hc] at hold
        cases hold
    obtain ⟨p, hpHigh, hpLt⟩ :=
      Vec.compare_lt_has_pivot xs v hvlt
    by_cases hqp : q.val < p.val
    · have hcmp : compareVec xs w = Ordering.lt := by
        apply Vec.compare_lt_of_pivot xs w p
        · intro j hpj
          have hqj : q.val < j.val :=
            Nat.lt_trans hqp hpj
          rw [hhigh j hqj]
          exact hpHigh j hpj
        · have hpw : w.idx p = v.idx p :=
            hhigh p hqp
          rw [hpw]
          exact hpLt
      exact T.P_lt_P_of_compareVec_lt xs w xadd T.Z hcmp
    · have hpq : p.val ≤ q.val := Nat.not_lt.mp hqp
      have hself : xs.idx q < T.P xs xadd := by
        have hmemCoord : xs.idx q ∈ Vec.toList xs := by
          apply (Vec.mem_toList_iff_idx xs (xs.idx q)).mpr
          exact ⟨q, rfl⟩
        have hmemG : xs.idx q ∈ T.G (T.P xs xadd) := by
          apply (T.mem_G_P xs xadd (xs.idx q)).mpr
          exact Or.inl
            ⟨xs.idx q, hmemCoord, Or.inl rfl⟩
        exact hx.2 (xs.idx q) hmemG
      have hcmp : compareVec xs w = Ordering.lt := by
        apply Vec.compare_lt_of_pivot xs w q
        · intro j hqj
          have hpj : p.val < j.val :=
            Nat.lt_of_le_of_lt hpq hqj
          rw [hhigh j hqj]
          exact hpHigh j hpj
        · rw [hwq]
          exact hself
      exact T.P_lt_P_of_compareVec_lt xs w xadd T.Z hcmp

theorem T.rplc_two_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam) (i j : Fin lam) (a b : T lam)
    (hij : i.val ≠ j.val)
    (hs : T.isNF (T.P ls T.Z))
    (ha : T.isNFComp a) (hb : T.isNFComp b) :
    T.isNF (T.P ((ls.rplc i a).rplc j b) T.Z) := by
  have holdCoord := T.isNF_P_coord_NFComp ls T.Z hs
  apply T.isNF_PZ_of_coords ((ls.rplc i a).rplc j b)
  intro q
  by_cases hqj : q.val = j.val
  · have hqe : q = j := Fin.eq_of_val_eq hqj
    rw [hqe]
    rw [Vec.rplc_idx_same]
    exact hb
  · rw [Vec.rplc_idx_of_ne (ls.rplc i a) j q b hqj]
    by_cases hqi : q.val = i.val
    · have hqe : q = i := Fin.eq_of_val_eq hqi
      rw [hqe]
      rw [Vec.rplc_idx_same]
      exact ha
    · rw [Vec.rplc_idx_of_ne ls i q a hqi]
      exact holdCoord q

theorem T.rplc_min_NFComp_closed {lam : Nat}
    (ls : Vec (T lam) lam) (m : Fin lam) (d : Dom) (a : T lam)
    (hs : T.isNFComp (T.P ls T.Z))
    (hmin : T.domVecMinIdx ls = some (m, d))
    (ha : T.isNFComp a)
    (halt : a < ls.idx m) :
    T.isNFComp (T.P (ls.rplc m a) T.Z) := by
  have hspec := T.domVecMinIdx_some_spec ls m d hmin
  have holdCoord := T.isNF_P_coord_NFComp ls T.Z hs.1
  have hcoord :
      ∀ i : Fin lam, T.isNFComp ((ls.rplc m a).idx i) := by
    intro i
    by_cases him : i.val = m.val
    · have hieq : i = m := Fin.eq_of_val_eq him
      rw [hieq]
      rw [Vec.rplc_idx_same]
      exact ha
    · rw [Vec.rplc_idx_of_ne ls m i a him]
      exact holdCoord i
  have hnf : T.isNF (T.P (ls.rplc m a) T.Z) :=
    T.isNF_PZ_of_coords (ls.rplc m a) hcoord
  constructor
  · exact hnf
  · intro y hy
    cases (T.mem_G_P (ls.rplc m a) T.Z y).mp hy with
    | inl hv =>
      obtain ⟨x, hx, hxy⟩ := hv
      obtain ⟨i, hi⟩ :=
        (Vec.mem_toList_iff_idx (ls.rplc m a) x).mp hx
      have hxic : T.isNFComp x := by
        rw [← hi]
        exact hcoord i
      have hxlt : x < T.P (ls.rplc m a) T.Z := by
        by_cases him : i.val < m.val
        · have hdom0 : T.dom (ls.idx i) = .zero :=
            hspec.2 i him
          have hzi : ls.idx i = T.Z :=
            T.dom_zero_eq_Z (ls.idx i) hdom0
          have hine : i.val ≠ m.val := Nat.ne_of_lt him
          have hr :
              (ls.rplc m a).idx i = ls.idx i :=
            Vec.rplc_idx_of_ne ls m i a hine
          rw [← hi, hr, hzi]
          show compareT T.Z (T.P (ls.rplc m a) T.Z) =
            Ordering.lt
          rfl
        · by_cases hmi : m.val < i.val
          · have hine : i.val ≠ m.val := Nat.ne_of_gt hmi
            have hr :
                (ls.rplc m a).idx i = ls.idx i :=
              Vec.rplc_idx_of_ne ls m i a hine
            have holdMem :
                ls.idx i ∈ T.G (T.P ls T.Z) := by
              apply (T.mem_G_P ls T.Z (ls.idx i)).mpr
              have himem : ls.idx i ∈ Vec.toList ls := by
                apply (Vec.mem_toList_iff_idx ls (ls.idx i)).mpr
                exact ⟨i, rfl⟩
              exact Or.inl
                ⟨ls.idx i, himem, Or.inl rfl⟩
            have holdLt : ls.idx i < T.P ls T.Z :=
              hs.2 (ls.idx i) holdMem
            have hhigh :
                ∀ j : Fin lam, i.val < j.val →
                  (ls.rplc m a).idx j = ls.idx j := by
              intro j hij
              have hmj : m.val < j.val :=
                Nat.lt_trans hmi hij
              have hjne : j.val ≠ m.val :=
                Nat.ne_of_gt hmj
              exact Vec.rplc_idx_of_ne ls m j a hjne
            have hb :=
              T.term_lt_P_of_self_at
                (ls.idx i) ls (ls.rplc m a) i
                (holdCoord i) holdLt hr hhigh
            rw [← hi, hr]
            exact hb
          · have himle : i.val ≤ m.val := Nat.not_lt.mp hmi
            have hmile : m.val ≤ i.val := Nat.not_lt.mp him
            have hval : i.val = m.val :=
              Nat.le_antisymm himle hmile
            have hieq : i = m := Fin.eq_of_val_eq hval
            rw [hieq] at hi
            have hr :
                (ls.rplc m a).idx m = a :=
              Vec.rplc_idx_same ls m a
            have hia : a = x := by
              rw [← hi]
              exact hr.symm.symm
            have holdMem :
                ls.idx m ∈ T.G (T.P ls T.Z) := by
              apply (T.mem_G_P ls T.Z (ls.idx m)).mpr
              have hmmem : ls.idx m ∈ Vec.toList ls := by
                apply (Vec.mem_toList_iff_idx ls (ls.idx m)).mpr
                exact ⟨m, rfl⟩
              exact Or.inl
                ⟨ls.idx m, hmmem, Or.inl rfl⟩
            have holdLtCoord : ls.idx m < T.P ls T.Z :=
              hs.2 (ls.idx m) holdMem
            have haold : a < T.P ls T.Z :=
              strict_partial_order.trans a (ls.idx m)
                (T.P ls T.Z) halt holdLtCoord
            have hhigh :
                ∀ j : Fin lam, m.val < j.val →
                  (ls.rplc m a).idx j = ls.idx j := by
              intro j hmj
              exact Vec.rplc_idx_of_ne ls m j a
                (Nat.ne_of_gt hmj)
            have hb :=
              T.term_lt_P_of_self_at
                a ls (ls.rplc m a) m
                ha haold hr hhigh
            rw [hia]
            exact hb
      cases hxy with
      | inl hyx =>
        rw [hyx]
        exact hxlt
      | inr hyg =>
        have hyx : y < x := hxic.2 y hyg
        exact strict_partial_order.trans y x
          (T.P (ls.rplc m a) T.Z) hyx hxlt
    | inr hz =>
      rw [T.G] at hz
      exact False.elim (List.not_mem_nil y hz)

theorem T.G_size_lt {lam : Nat} :
    ∀ s y : T lam, y ∈ T.G s → T.size y < T.size s := by
  intro s
  have main :
      ∀ n : Nat, ∀ a y : T lam, T.size a = n →
        y ∈ T.G a → T.size y < T.size a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a y hsize hy
      cases a with
      | Z =>
        rw [T.G] at hy
        exact False.elim (List.not_mem_nil y hy)
      | P ls add =>
        cases (T.mem_G_P ls add y).mp hy with
        | inl hv =>
          obtain ⟨x, hx, hcase⟩ := hv
          obtain ⟨i, hi⟩ := (Vec.mem_toList_iff_idx ls x).mp hx
          have hxsize : T.size x < Vec.size ls := by
            rw [← hi]
            exact Vec.idx_size_lt ls i
          have hvec :
              Vec.size ls < T.size (T.P ls add) := by
            show Vec.size ls < 1 + Vec.size ls + T.size add
            have hle :
                Vec.size ls ≤ Vec.size ls + T.size add :=
              Nat.le_add_right _ _
            have hlt :
                Vec.size ls + T.size add <
                  1 + (Vec.size ls + T.size add) :=
              Nat.lt_add_of_pos_left Nat.zero_lt_one
            have heq :
                1 + (Vec.size ls + T.size add) =
                  1 + Vec.size ls + T.size add :=
              (Nat.add_assoc 1 (Vec.size ls) (T.size add)).symm
            calc
              Vec.size ls ≤ Vec.size ls + T.size add := hle
              _ < 1 + (Vec.size ls + T.size add) := hlt
              _ = 1 + Vec.size ls + T.size add := heq
          cases hcase with
          | inl hyx =>
            rw [hyx]
            exact Nat.lt_trans hxsize hvec
          | inr hyg =>
            have hxn : T.size x < n := by
              have hsx : T.size x < T.size (T.P ls add) :=
                Nat.lt_trans hxsize hvec
              rw [hsize] at hsx
              exact hsx
            have hrec :
                T.size y < T.size x :=
              ih (T.size x) hxn x y rfl hyg
            exact Nat.lt_trans hrec (Nat.lt_trans hxsize hvec)
        | inr hadd =>
          have haddsize :
              T.size add < T.size (T.P ls add) :=
            T.add_size_lt_P ls add
          have haddn : T.size add < n := by
            rw [hsize] at haddsize
            exact haddsize
          have hrec :
              T.size y < T.size add :=
            ih (T.size add) haddn add y rfl hadd
          exact Nat.lt_trans hrec (T.add_size_lt_P ls add)
  exact fun s y hy => main (T.size s) s y rfl hy

theorem T.vec_G_size_lt {lam : Nat} (ls : Vec (T lam) lam)
    (x y : T lam) (hx : x ∈ Vec.toList ls)
    (hy : y = x ∨ y ∈ T.G x) :
    T.size y < Vec.size ls := by
  obtain ⟨i, hi⟩ := (Vec.mem_toList_iff_idx ls x).mp hx
  have hxsize : T.size x < Vec.size ls := by
    rw [← hi]
    exact Vec.idx_size_lt ls i
  cases hy with
  | inl heq =>
    rw [heq]
    exact hxsize
  | inr hyg =>
    exact Nat.lt_trans (T.G_size_lt x y hyg) hxsize

theorem T.vec_G_lt_same_vector_any {lam : Nat}
    (ls : Vec (T lam) lam) (oldAdd newAdd y : T lam)
    (hsize : T.size y < Vec.size ls)
    (hold : y < T.P ls oldAdd) :
    y < T.P ls newAdd := by
  cases y with
  | Z =>
    show compareT T.Z (T.P ls newAdd) = Ordering.lt
    rfl
  | P ys yadd =>
    show
      (match compareVec ys ls with
      | Ordering.eq => compareT yadd newAdd
      | ord => ord) = Ordering.lt
    cases hc : compareVec ys ls with
    | lt =>
      rw [hc]
    | eq =>
      have hys : ys = ls := Vec_eq_sound ys ls hc
      rw [hys] at hsize
      have hge :
          Vec.size ls ≤
            T.size (T.P ls yadd) := by
        show Vec.size ls ≤ 1 + Vec.size ls + T.size yadd
        have h1 : Vec.size ls ≤ 1 + Vec.size ls :=
          Nat.le_add_left (Vec.size ls) 1
        have h2 :
            1 + Vec.size ls ≤
              1 + Vec.size ls + T.size yadd :=
          Nat.le_add_right _ _
        exact Nat.le_trans h1 h2
      exact False.elim ((Nat.not_lt_of_ge hge) hsize)
    | gt =>
      show compareT (T.P ys yadd) (T.P ls oldAdd) =
        Ordering.lt at hold
      rw [hc] at hold
      cases hold

theorem T.lt_P_self_of_isNF_head_le {lam : Nat}
    (a : T lam) (ha : T.isNF a) :
    ∀ ls : Vec (T lam) lam,
      T.head a ≤ T.P ls T.Z →
      a < T.P ls a := by
  induction ha with
  | z =>
    intro ls h
    show compareT T.Z (T.P ls T.Z) = Ordering.lt
    rfl
  | p als aadd h0 h1 h2 h3 ih0 ih1 =>
    intro ls hh
    show
      (match compareVec als ls with
      | Ordering.eq => compareT aadd (T.P als aadd)
      | ord => ord) = Ordering.lt
    cases hc : compareVec als ls with
    | lt =>
      rw [hc]
    | eq =>
      have hals : als = ls := Vec_eq_sound als ls hc
      rw [← hals]
      rw [show compareVec als als = Ordering.eq from Vec_refl als]
      exact ih1 als h3
    | gt =>
      have hh' :
          T.P als T.Z ≤ T.P ls T.Z := hh
      cases hh' with
      | inl hlt =>
        show
          (match compareVec als ls with
          | Ordering.eq => compareT T.Z T.Z
          | ord => ord) = Ordering.lt at hlt
        rw [hc] at hlt
        cases hlt
      | inr heq =>
        have hcmp :
            compareT (T.P als T.Z) (T.P ls T.Z) =
              Ordering.eq := by
          rw [heq]
          exact T_refl (T.P ls T.Z)
        show
          (match compareVec als ls with
          | Ordering.eq => compareT T.Z T.Z
          | ord => ord) = Ordering.eq at hcmp
        rw [hc] at hcmp
        cases hcmp

theorem T.P_tail_NFComp_closed {lam : Nat}
    (ls : Vec (T lam) lam) (oldAdd newAdd : T lam)
    (hold : T.isNFComp (T.P ls oldAdd))
    (hnew : T.isNFComp newAdd)
    (hhead : T.head newAdd ≤ T.P ls T.Z) :
    T.isNFComp (T.P ls newAdd) := by
  have holdNF := hold.1
  cases holdNF with
  | p _ _ h0 hOldAdd h2 h3 =>
    have hnf : T.isNF (T.P ls newAdd) :=
      T.isNF.p ls newAdd h0 hnew.1 h2 hhead
    constructor
    · exact hnf
    · intro y hy
      cases (T.mem_G_P ls newAdd y).mp hy with
      | inl hvec =>
        obtain ⟨x, hx, hxy⟩ := hvec
        have hyOld : y ∈ T.G (T.P ls oldAdd) := by
          apply (T.mem_G_P ls oldAdd y).mpr
          exact Or.inl ⟨x, hx, hxy⟩
        have hyltOld : y < T.P ls oldAdd :=
          hold.2 y hyOld
        have hysize : T.size y < Vec.size ls :=
          T.vec_G_size_lt ls x y hx hxy
        exact T.vec_G_lt_same_vector_any
          ls oldAdd newAdd y hysize hyltOld
      | inr htail =>
        have hyltNew : y < newAdd :=
          hnew.2 y htail
        have hnewlt :
            newAdd < T.P ls newAdd :=
          T.lt_P_self_of_isNF_head_le newAdd hnew.1 ls hhead
        exact strict_partial_order.trans y newAdd
          (T.P ls newAdd) hyltNew hnewlt


theorem T.isNFComp_PZ_of_coords_lt {lam : Nat}
    (ls : Vec (T lam) lam)
    (hcomp : ∀ i : Fin lam, T.isNFComp (ls.idx i))
    (hlt : ∀ i : Fin lam, ls.idx i < T.P ls T.Z) :
    T.isNFComp (T.P ls T.Z) := by
  constructor
  · exact T.isNF_PZ_of_coords ls hcomp
  · intro y hy
    cases (T.mem_G_P ls T.Z y).mp hy with
    | inl hv =>
      obtain ⟨x, hx, hcase⟩ := hv
      obtain ⟨i, hi⟩ := (Vec.mem_toList_iff_idx ls x).mp hx
      cases hcase with
      | inl hyx =>
        rw [hyx]
        rw [← hi]
        exact hlt i
      | inr hyg =>
        have hyxlt : y < x := by
          rw [← hi] at hyg
          have hc := (hcomp i).2 y hyg
          rw [hi] at hc
          exact hc
        have hxparent : x < T.P ls T.Z := by
          rw [← hi]
          exact hlt i
        exact strict_partial_order.trans y x (T.P ls T.Z)
          hyxlt hxparent
    | inr hz =>
      rw [T.G] at hz
      exact False.elim (List.not_mem_nil y hz)

theorem T.single_rplc_PZ_NFComp_closed {lam : Nat}
    (ls : Vec (T lam) lam) (m : Fin lam) (z : T lam)
    (hold : T.isNFComp (T.P ls T.Z))
    (hz : T.isNFComp z)
    (hzx : z < ls.idx m)
    (hlow : ∀ q : Fin lam, q.val < m.val → ls.idx q = T.Z) :
    T.isNFComp (T.P (ls.rplc m z) T.Z) := by
  let newv := ls.rplc m z
  have hOldCoord : ∀ q : Fin lam, T.isNFComp (ls.idx q) :=
    T.isNF_P_coord_NFComp ls T.Z hold.1
  have hOldLt : ∀ q : Fin lam, ls.idx q < T.P ls T.Z := by
    intro q
    have hmem : ls.idx q ∈ T.G (T.P ls T.Z) := by
      apply (T.mem_G_P ls T.Z (ls.idx q)).mpr
      have hqmem : ls.idx q ∈ Vec.toList ls :=
        (Vec.mem_toList_iff_idx ls (ls.idx q)).mpr ⟨q, rfl⟩
      exact Or.inl ⟨ls.idx q, hqmem, Or.inl rfl⟩
    exact hold.2 (ls.idx q) hmem
  have hNewComp : ∀ q : Fin lam, T.isNFComp (newv.idx q) := by
    intro q
    by_cases hqm : q.val = m.val
    · have hq : q = m := Fin.eq_of_val_eq hqm
      rw [hq]
      show T.isNFComp ((ls.rplc m z).idx m)
      rw [Vec.rplc_idx_same]
      exact hz
    · show T.isNFComp ((ls.rplc m z).idx q)
      rw [Vec.rplc_idx_of_ne ls m q z hqm]
      exact hOldCoord q
  have hNewLt : ∀ q : Fin lam, newv.idx q < T.P newv T.Z := by
    intro q
    by_cases hqm : q.val = m.val
    · have hq : q = m := Fin.eq_of_val_eq hqm
      rw [hq]
      have hnewm : newv.idx m = z := by
        show (ls.rplc m z).idx m = z
        exact Vec.rplc_idx_same ls m z
      have hzold :
          z < T.P ls T.Z :=
        strict_partial_order.trans z (ls.idx m) (T.P ls T.Z)
          hzx (hOldLt m)
      exact T.pivot_term_lt_updated_parent
        ls newv m z
        (fun j hj => by
          show ls.idx j = (ls.rplc m z).idx j
          rw [Vec.rplc_idx_of_ne ls m j z (Nat.ne_of_gt hj)])
        hnewm hzold hz
    · by_cases hqmLt : q.val < m.val
      · have hqz : ls.idx q = T.Z := hlow q hqmLt
        have hnewq : newv.idx q = T.Z := by
          show (ls.rplc m z).idx q = T.Z
          rw [Vec.rplc_idx_of_ne ls m q z hqm]
          exact hqz
        rw [hnewq]
        show compareT T.Z (T.P newv T.Z) = Ordering.lt
        rfl
      · have hmq : m.val < q.val := by
          have hle : m.val ≤ q.val := Nat.not_lt.mp hqmLt
          exact Nat.lt_of_le_of_ne hle (Ne.symm hqm)
        have hnewq : newv.idx q = ls.idx q := by
          show (ls.rplc m z).idx q = ls.idx q
          rw [Vec.rplc_idx_of_ne ls m q z (Nat.ne_of_gt hmq)]
        rw [hnewq]
        apply T.coord_lt_preserved_below_update ls newv q
        · intro j hqj
          show ls.idx j = (ls.rplc m z).idx j
          have hmj : m.val < j.val :=
            Nat.lt_of_lt_of_le hmq hqj
          rw [Vec.rplc_idx_of_ne ls m j z (Nat.ne_of_gt hmj)]
        · exact hOldLt q
  exact T.isNFComp_PZ_of_coords_lt newv hNewComp hNewLt

theorem T.P_le_P_same {lam : Nat} (ls : Vec (T lam) lam)
    (a b : T lam) (h : a ≤ b) :
    T.P ls a ≤ T.P ls b := by
  cases h with
  | inl hlt =>
    apply Or.inl
    show compareT (T.P ls a) (T.P ls b) = Ordering.lt
    rw [show compareVec ls ls = Ordering.eq from Vec_refl ls]
    exact hlt
  | inr heq =>
    rw [heq]
    exact Or.inr rfl

theorem T.mul_PZ_lt_next {lam : Nat} (ls : Vec (T lam) lam) :
    ∀ t : T lam,
      T.mul (T.P ls T.Z) t <
        T.P ls (T.mul (T.P ls T.Z) t) := by
  intro t
  induction t with
  | Z =>
    rw [T.mul]
    show compareT T.Z (T.P ls T.Z) = Ordering.lt
    rfl
  | P tls add ih =>
    rw [T.mul]
    rw [T.oplus]
    show compareT
      (T.P ls (T.mul (T.P ls T.Z) add))
      (T.P ls (T.P ls (T.mul (T.P ls T.Z) add))) =
        Ordering.lt
    rw [show compareVec ls ls = Ordering.eq from Vec_refl ls]
    exact ih

theorem T.head_mul_PZ_le {lam : Nat} (ls : Vec (T lam) lam) :
    ∀ t : T lam,
      T.head (T.mul (T.P ls T.Z) t) ≤ T.P ls T.Z := by
  intro t
  cases t with
  | Z =>
    rw [T.mul]
    exact T.Z_le (T.P ls T.Z)
  | P tls add =>
    rw [T.mul]
    rw [T.oplus]
    exact Or.inr rfl

theorem T.mul_PZ_NFComp_closed {lam : Nat}
    (ls : Vec (T lam) lam)
    (hbase : T.isNFComp (T.P ls T.Z)) :
    ∀ t : T lam, T.isNFComp (T.mul (T.P ls T.Z) t) := by
  intro t
  induction t with
  | Z =>
    rw [T.mul]
    exact T.isNFComp_Z
  | P tls add ih =>
    rw [T.mul]
    rw [T.oplus]
    have hbaseNF := hbase.1
    cases hbaseNF with
    | p _ _ h0 hz h2 h3 =>
      have hnf :
          T.isNF
            (T.P ls (T.mul (T.P ls T.Z) add)) := by
        apply T.isNF.p ls (T.mul (T.P ls T.Z) add)
        · exact h0
        · exact ih.1
        · exact h2
        · exact T.head_mul_PZ_le ls add
      constructor
      · exact hnf
      · intro y hy
        cases (T.mem_G_P ls (T.mul (T.P ls T.Z) add) y).mp hy with
        | inl hvec =>
          have hybase : y ∈ T.G (T.P ls T.Z) := by
            apply (T.mem_G_P ls T.Z y).mpr
            exact Or.inl hvec
          have hya : y < T.P ls T.Z := hbase.2 y hybase
          have htail : T.Z ≤ T.mul (T.P ls T.Z) add :=
            T.Z_le (T.mul (T.P ls T.Z) add)
          have hle :
              T.P ls T.Z ≤
                T.P ls (T.mul (T.P ls T.Z) add) :=
            T.P_le_P_same ls T.Z
              (T.mul (T.P ls T.Z) add) htail
          exact lt_of_lt_of_le_thm T y
            (T.P ls T.Z)
            (T.P ls (T.mul (T.P ls T.Z) add))
            hya hle
        | inr htail =>
          have hyu :
              y < T.mul (T.P ls T.Z) add :=
            ih.2 y htail
          have hu :
              T.mul (T.P ls T.Z) add <
                T.P ls (T.mul (T.P ls T.Z) add) :=
            T.mul_PZ_lt_next ls add
          exact strict_partial_order.trans y
            (T.mul (T.P ls T.Z) add)
            (T.P ls (T.mul (T.P ls T.Z) add))
            hyu hu


def T.GZ {lam : Nat} (z : T lam) : List (T lam) :=
  [z] ++ T.G z ++ [T.Z]

def T.listLe {lam : Nat} (xs ys : List (T lam)) : Prop :=
  ∀ x, x ∈ xs → ∃ y, y ∈ ys ∧ x ≤ y

def T.SDom {lam : Nat} (z b a : T lam) : Prop :=
  b < a ∧
    ∀ c, b ≤ c → c ≤ a →
      T.listLe (T.G b) (T.G c ++ T.GZ z)

theorem T.G_trans {lam : Nat} :
    ∀ a x y : T lam, x ∈ T.G a → y ∈ T.G x → y ∈ T.G a := by
  intro a
  have main :
      ∀ n : Nat, ∀ s x y : T lam, T.size s = n →
        x ∈ T.G s → y ∈ T.G x → y ∈ T.G s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s x y hsize hx hy
      cases s with
      | Z =>
        rw [T.G] at hx
        exact False.elim (List.not_mem_nil x hx)
      | P ls add =>
        cases (T.mem_G_P ls add x).mp hx with
        | inl hv =>
          obtain ⟨u, hu, hxu⟩ := hv
          cases hxu with
          | inl hxu =>
            rw [hxu] at hy
            apply (T.mem_G_P ls add y).mpr
            exact Or.inl ⟨u, hu, Or.inr hy⟩
          | inr hG =>
            obtain ⟨i, hi⟩ := (Vec.mem_toList_iff_idx ls u).mp hu
            have husize : T.size u < T.size (T.P ls add) := by
              have h1 : T.size u < Vec.size ls := by
                rw [← hi]
                exact Vec.idx_size_lt ls i
              have h2 : Vec.size ls < T.size (T.P ls add) := by
                show Vec.size ls < 1 + Vec.size ls + T.size add
                have hle : Vec.size ls ≤ Vec.size ls + T.size add :=
                  Nat.le_add_right _ _
                have hlt :
                    Vec.size ls + T.size add <
                      1 + (Vec.size ls + T.size add) :=
                  Nat.lt_add_of_pos_left Nat.zero_lt_one
                have heq :
                    1 + (Vec.size ls + T.size add) =
                      1 + Vec.size ls + T.size add :=
                  (Nat.add_assoc 1 (Vec.size ls) (T.size add)).symm
                calc
                  Vec.size ls ≤ Vec.size ls + T.size add := hle
                  _ < 1 + (Vec.size ls + T.size add) := hlt
                  _ = 1 + Vec.size ls + T.size add := heq
              exact Nat.lt_trans h1 h2
            have hun : T.size u < n := by
              rw [hsize] at husize
              exact husize
            have hyr : y ∈ T.G u :=
              ih (T.size u) hun u x y rfl hG hy
            apply (T.mem_G_P ls add y).mpr
            exact Or.inl ⟨u, hu, Or.inr hyr⟩
        | inr hGa =>
          have hasize : T.size add < n := by
            have hlt := T.add_size_lt_P ls add
            rw [hsize] at hlt
            exact hlt
          have hyr : y ∈ T.G add :=
            ih (T.size add) hasize add x y rfl hGa hy
          apply (T.mem_G_P ls add y).mpr
          exact Or.inr hyr
  exact fun a x y hx hy => main (T.size a) a x y rfl hx hy

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
      exact False.elim (hn (fun x hx =>
        False.elim (List.not_mem_nil x hx)))
    | cons a as ih =>
      intro hn
      by_cases ha : a < b
      · have htail : ¬ (∀ x ∈ as, x < b) := by
          intro hall
          apply hn
          intro x hx
          cases List.mem_cons.mp hx with
          | inl heq =>
            rw [← heq]
            exact ha
          | inr hmem =>
            exact hall x hmem
        obtain ⟨x, hx, hnx⟩ := ih htail
        exact ⟨x, List.mem_cons_of_mem a hx, hnx⟩
      · exact ⟨a, List.mem_cons_self, ha⟩
  exact main (T.G s) h

theorem T.find_violating_source {lam : Nat} (b c₀ w : T lam)
    (hw : w ∈ T.G c₀) (hbw : b ≤ w) :
    ∃ c, c ∈ T.G c₀ ∧ b ≤ c ∧
      ∀ x ∈ T.G c, x < b := by
  generalize hn : T.size w = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases hbound : ∀ x ∈ T.G w, x < b
    · exact ⟨w, hw, hbw, hbound⟩
    · obtain ⟨x, hx, hnx⟩ := T.exists_G_not_lt w b hbound
      have hbx : b ≤ x := by
        cases strict_linear_order.total x b with
        | inl hxb =>
          exact False.elim (hnx hxb)
        | inr hr =>
          cases hr with
          | inl hbx =>
            exact Or.inl hbx
          | inr heq =>
            exact Or.inr heq.symm
      have hxsize : T.size x < n := by
        have hs := T.G_size_lt w x hx
        rw [hn] at hs
        exact hs
      have hxc₀ : x ∈ T.G c₀ :=
        T.G_trans c₀ w x hw hx
      exact ih (T.size x) hxsize x hxc₀ hbx rfl

theorem T.GZ_bound_trans {lam : Nat} (z b a : T lam)
    (hzb : ∀ x ∈ T.GZ z, x < b)
    (hba : b < a) :
    ∀ x ∈ T.GZ z, x < a := by
  intro x hx
  exact strict_partial_order.trans x b a (hzb x hx) hba

theorem T.SDom_G_lt_upper {lam : Nat} (z b a : T lam)
    (hs : T.SDom z b a)
    (hGa : ∀ x ∈ T.G a, x < a)
    (hGz : ∀ x ∈ T.GZ z, x < b) :
    ∀ y ∈ T.G b, y < a := by
  intro y hy
  have hba : b ≤ a := Or.inl hs.1
  have haa : a ≤ a := partial_order.refl a
  obtain ⟨w, hw, hyw⟩ := hs.2 a hba haa y hy
  cases List.mem_append.mp hw with
  | inl hwa =>
    have hwlt : w < a := hGa w hwa
    exact lt_of_le_of_lt_thm T y w a hyw hwlt
  | inr hwz =>
    have hwltb : w < b := hGz w hwz
    have hyltb : y < b :=
      lt_of_le_of_lt_thm T y w b hyw hwltb
    exact strict_partial_order.trans y b a hyltb hs.1

theorem T.SDom_G_closed {lam : Nat} (z b a : T lam)
    (hs : T.SDom z b a)
    (hGa : ∀ x ∈ T.G a, x < a)
    (hGz : ∀ x ∈ T.GZ z, x < b) :
    ∀ y ∈ T.G b, y < b := by
  intro y hy
  cases strict_linear_order.total y b with
  | inl hyb =>
    exact hyb
  | inr hr =>
    have hby : b ≤ y := by
      cases hr with
      | inl hby =>
        exact Or.inl hby
      | inr heq =>
        exact Or.inr heq.symm
    obtain ⟨c, hcG, hbc, hcBound⟩ :=
      T.find_violating_source b b y hy hby
    have hca : c < a :=
      T.SDom_G_lt_upper z b a hs hGa hGz c hcG
    have hcaLe : c ≤ a := Or.inl hca
    obtain ⟨w, hw, hcw⟩ := hs.2 c hbc hcaLe c hcG
    have hwb : w < b := by
      cases List.mem_append.mp hw with
      | inl hwc =>
        exact hcBound w hwc
      | inr hwz =>
        exact hGz w hwz
    have hcb : c < b :=
      lt_of_le_of_lt_thm T c w b hcw hwb
    have hbb : b < b :=
      lt_of_le_of_lt_thm T b c b hbc hcb
    exact False.elim (strict_partial_order.irrefl b hbb)

theorem T.head_mono_le {lam : Nat} (a b : T lam)
    (h : a ≤ b) : T.head a ≤ T.head b := by
  cases h with
  | inl hlt =>
    exact T.head_mono a b hlt
  | inr heq =>
    rw [heq]
    exact partial_order.refl (T.head b)

theorem T.P_same_le_iff {lam : Nat} (ls : Vec (T lam) lam)
    (a b : T lam) :
    T.P ls a ≤ T.P ls b ↔ a ≤ b := by
  constructor
  · intro h
    cases h with
    | inl hlt =>
      left
      show compareT a b = Ordering.lt
      show compareT (T.P ls a) (T.P ls b) = Ordering.lt at hlt
      rw [show compareVec ls ls = Ordering.eq from Vec_refl ls] at hlt
      exact hlt
    | inr heq =>
      right
      cases heq
      rfl
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
    partial_order.antisymm (T.head c) (T.P ls T.Z)
      hheadU hheadL
  cases c with
  | Z =>
    rw [T.head] at hheadEq
    cases hheadEq
  | P cs d =>
    rw [T.head] at hheadEq
    have hcs : cs = ls := by
      cases hheadEq
      rfl
    subst cs
    refine ⟨d, rfl, ?_, ?_⟩
    · exact (T.P_same_le_iff ls a d).mp hl
    · exact (T.P_same_le_iff ls d b).mp hu

theorem T.SDom_tail {lam : Nat} (z b a : T lam)
    (ls : Vec (T lam) lam) (hs : T.SDom z b a) :
    T.SDom z (T.P ls b) (T.P ls a) := by
  constructor
  · show compareT (T.P ls b) (T.P ls a) = Ordering.lt
    rw [show compareVec ls ls = Ordering.eq from Vec_refl ls]
    exact hs.1
  · intro c hbc hca
    have hba : b ≤ a := Or.inl hs.1
    obtain ⟨d, hcd, hbd, hda⟩ :=
      T.sandwich_same_vector ls b a c hba hbc hca
    rw [hcd]
    intro x hx
    cases (T.mem_G_P ls b x).mp hx with
    | inl hvec =>
      refine ⟨x, ?_, partial_order.refl x⟩
      apply List.mem_append_left (T.GZ z)
      apply (T.mem_G_P ls d x).mpr
      exact Or.inl hvec
    | inr htail =>
      obtain ⟨y, hy, hxy⟩ := hs.2 d hbd hda x htail
      cases List.mem_append.mp hy with
      | inl hyd =>
        refine ⟨y, ?_, hxy⟩
        apply List.mem_append_left (T.GZ z)
        apply (T.mem_G_P ls d y).mpr
        exact Or.inr hyd
      | inr hyz =>
        exact ⟨y, List.mem_append_right (T.G (T.P ls d)) hyz, hxy⟩



theorem Vec.compare_rplc_same_index_lt {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) (a b : T lam)
    (hab : a < b) :
    compareVec (v.rplc i a) (v.rplc i b) = Ordering.lt := by
  apply Vec.compare_lt_of_pivot (v.rplc i a) (v.rplc i b) i
  · intro j hij
    have hji : j.val ≠ i.val := Nat.ne_of_gt hij
    rw [Vec.rplc_idx_of_ne v i j a hji]
    rw [Vec.rplc_idx_of_ne v i j b hji]
  · rw [Vec.rplc_idx_same]
    rw [Vec.rplc_idx_same]
    exact hab

theorem T.fund_Omega_ne_Z {lam : Nat} (s t : T lam)
    (hd : T.dom s = .Omega) :
    T.fund s t ≠ T.Z := by
  cases s with
  | Z =>
    rw [T.dom] at hd
    cases hd
  | P ls add =>
    by_cases hadd : add = T.Z
    · subst add
      cases hmin : T.domVecMinIdx ls with
      | none =>
        rw [T.dom, if_pos rfl, hmin] at hd
        cases hd
      | some md =>
        cases md with
        | mk m d =>
          rw [T.dom, if_pos rfl, hmin] at hd
          by_cases hd1 : d = .one
          · rw [if_pos hd1] at hd
            cases m with
            | mk mv mh =>
              cases mv with
              | zero =>
                rw [if_pos rfl] at hd
                cases hd
              | succ mv =>
                have hne : mv + 1 ≠ 0 := Nat.succ_ne_zero mv
                rw [if_neg hne] at hd
                rw [T.fund, if_pos rfl, hmin, if_pos hd1]
                intro heq
                cases heq
          · rw [if_neg hd1] at hd
            cases hd
    · rw [T.fund, if_neg hadd]
      intro heq
      cases heq

theorem T.fund_Omega_strict_mono {lam : Nat} (s t₀ t₁ : T lam)
    (hd : T.dom s = .Omega) (hlt : t₀ < t₁) :
    T.fund s t₀ < T.fund s t₁ := by
  generalize hn : T.size s = n
  induction n using Nat.strong_induction_on generalizing s t₀ t₁ with
  | h n ih =>
    cases s with
    | Z =>
      rw [T.dom] at hd
      cases hd
    | P ls add =>
      by_cases hadd : add = T.Z
      · subst add
        cases hmin : T.domVecMinIdx ls with
        | none =>
          rw [T.dom, if_pos rfl, hmin] at hd
          cases hd
        | some md =>
          cases md with
          | mk m d =>
            rw [T.dom, if_pos rfl, hmin] at hd
            by_cases hd1 : d = .one
            · rw [if_pos hd1] at hd
              cases m with
              | mk mv mh =>
                cases mv with
                | zero =>
                  rw [if_pos rfl] at hd
                  cases hd
                | succ mv =>
                  have hne : mv + 1 ≠ 0 := Nat.succ_ne_zero mv
                  rw [if_neg hne] at hd
                  let mi : Fin lam := ⟨mv + 1, mh⟩
                  let mj : Fin lam := ⟨mv, Nat.lt_of_succ_lt mh⟩
                  have hvec :
                      compareVec
                        ((ls.rplc mi (T.fund ls[mi] T.Z)).rplc mj t₀)
                        ((ls.rplc mi (T.fund ls[mi] T.Z)).rplc mj t₁) =
                          Ordering.lt :=
                    Vec.compare_rplc_same_index_lt
                      (ls.rplc mi (T.fund ls[mi] T.Z)) mj t₀ t₁ hlt
                  rw [T.fund, if_pos rfl, hmin, if_pos hd1]
                  exact T.P_lt_P_of_compareVec_lt _ _ T.Z T.Z hvec
            · rw [if_neg hd1] at hd
              cases hd
      · have hdadd : T.dom add = .Omega := by
          rw [T.dom, if_neg hadd] at hd
          exact hd
        have hsz : T.size add < n := by
          have hs := T.add_size_lt_P ls add
          rw [hn] at hs
          exact hs
        have hrec :
            T.fund add t₀ < T.fund add t₁ :=
          ih (T.size add) hsz add t₀ t₁ rfl hdadd hlt
        rw [T.fund, if_neg hadd]
        show
          (match compareVec ls ls with
          | Ordering.eq => compareT (T.fund add t₀) (T.fund add t₁)
          | ord => ord) = Ordering.lt
        rw [Vec_refl ls]
        exact hrec

theorem T.iter_fund_lt_next {lam : Nat} (s t : T lam)
    (hd : T.dom s = .Omega) :
    T.iter (fun x => T.fund s x) t <
      T.fund s (T.iter (fun x => T.fund s x) t) := by
  induction t with
  | Z =>
    rw [T.iter]
    have hne : T.fund s T.Z ≠ T.Z :=
      T.fund_Omega_ne_Z s T.Z hd
    cases T.Z_le (T.fund s T.Z) with
    | inl hlt =>
      exact hlt
    | inr heq =>
      exact False.elim (hne heq.symm)
  | P ls add ih =>
    rw [T.iter]
    exact T.fund_Omega_strict_mono s
      (T.iter (fun x => T.fund s x) add)
      (T.fund s (T.iter (fun x => T.fund s x) add))
      hd ih


theorem T.GZ_lt_of_NFComp_lt {lam : Nat} (z b : T lam)
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
      exact strict_partial_order.trans x z b hxz hzb
  | inr hzero =>
    have heq : x = T.Z := List.mem_singleton.mp hzero
    rw [heq]
    have hle : T.Z ≤ z := T.Z_le z
    exact lt_of_le_of_lt_thm T T.Z z b hle hzb

theorem T.NFComp_of_SDom {lam : Nat} (z b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp a)
    (hz : T.isNFComp z)
    (hdom : T.SDom z b a)
    (hzb : z < b) :
    T.isNFComp b := by
  constructor
  · exact hb
  · exact T.SDom_G_closed z b a hdom ha.2
      (T.GZ_lt_of_NFComp_lt z b hz hzb)

theorem T.NFComp_of_SDom_Z_or_eq {lam : Nat} (b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp a)
    (hdom : T.SDom T.Z b a) :
    T.isNFComp b := by
  by_cases hbz : b = T.Z
  · rw [hbz]
    exact T.isNFComp_Z
  · have hzb : T.Z < b := by
      cases T.Z_le b with
      | inl hlt => exact hlt
      | inr heq => exact False.elim (hbz heq.symm)
    exact T.NFComp_of_SDom T.Z b a hb ha
      T.isNFComp_Z hdom hzb


theorem Vec.interval_pivot_properties {lam m : Nat}
    (low mid high : Vec (T lam) m) (i : Fin m)
    (heqAbove :
      ∀ j : Fin m, i.val < j.val → low.idx j = high.idx j)
    (hpivot : low.idx i < high.idx i)
    (hlm : compareVec low mid = Ordering.lt ∨ low = mid)
    (hmh : compareVec mid high = Ordering.lt ∨ mid = high) :
    (∀ j : Fin m, i.val < j.val → mid.idx j = high.idx j) ∧
      low.idx i ≤ mid.idx i := by
  cases hlm with
  | inr heq =>
    subst mid
    constructor
    · intro j hij
      exact heqAbove j hij
    · exact Or.inr rfl
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
              have hpq : p = q := Fin.eq_of_val_eq heqVal.symm
              subst q
              have hlp : low.idx p = high.idx p :=
                heqAbove p hip
              have hcycle : low.idx p < low.idx p := by
                have htrans :=
                  strict_partial_order.trans
                    (low.idx p) (mid.idx p) (high.idx p)
                    hpLt hqLt
                rw [← hlp] at htrans
                exact htrans
              exact False.elim
                (strict_partial_order.irrefl (low.idx p) hcycle)
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
                (strict_partial_order.irrefl (high.idx q) hbad)
      · exact Nat.not_lt.mp hip
    constructor
    · intro j hij
      have hpj : p.val < j.val :=
        Nat.lt_of_le_of_lt hpi hij
      have hlmEq : low.idx j = mid.idx j :=
        hpEq j hpj
      have hlhEq : low.idx j = high.idx j :=
        heqAbove j hij
      exact hlmEq.symm.trans hlhEq
    · cases Nat.lt_or_eq_of_le hpi with
      | inl hpiLt =>
        exact Or.inr (hpEq i hpiLt)
      | inr hpiEq =>
        have hpeqi : p = i := Fin.eq_of_val_eq hpiEq
        rw [hpeqi] at hpLt
        exact Or.inl hpLt

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
