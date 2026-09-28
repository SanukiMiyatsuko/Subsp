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
      simp only [Vec.idx, Vec.size]
      split
      · have h := ih ⟨i.val, ‹i.val < k›⟩
        omega
      · omega

theorem Vec.getElem_eq_idx {A : Type} {n : Nat} (v : Vec A n) (m : Fin n) :
    v[m] = v.idx m := by
  rfl

theorem T.idx_size_lt_P {lam : Nat} (ls : Vec (T lam) lam) (add : T lam) (i : Fin lam) :
    T.size (ls[i]) < T.size (T.P ls add) := by
  have h := Vec.idx_size_lt ls i
  simp only [Vec.getElem_eq_idx, T.size]
  omega

theorem T.add_size_lt_P {lam : Nat} (ls : Vec (T lam) lam) (add : T lam) :
    T.size add < T.size (T.P ls add) := by
  simp only [T.size]
  omega

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
    (v : Vec (T lam) m) (i : Fin m) (d : Dom)
    (h : T.domVecMinIdx v = some (i, d)) :
    d ≠ .zero ∧ T.dom (v.idx i) = d ∧
      ∀ j : Fin m, j.val < i.val →
        T.dom (v.idx j) = .zero := by
  simpa only [h] using T.domVecMinIdx_spec v

theorem T.dom_PZ_one_iff {lam : Nat} (ls : Vec (T lam) lam) :
    T.dom (T.P ls T.Z) = .one ↔ T.domVecMinIdx ls = none := by
  simp only [T.dom, ite_true]
  cases T.domVecMinIdx ls with
  | none => simp
  | some md =>
      obtain ⟨m, d⟩ := md
      by_cases hd : d = Dom.one <;> by_cases hm : m.val = 0 <;> simp [hd, hm]

theorem T.dom_PZ_Omega {lam : Nat} (ls : Vec (T lam) lam)
    (hd : T.dom (T.P ls T.Z) = .Omega) :
    ∃ (k : Nat) (h : k + 1 < lam), T.domVecMinIdx ls = some (⟨k + 1, h⟩, Dom.one) := by
  cases hmin : T.domVecMinIdx ls with
  | none => simp [T.dom, hmin] at hd
  | some md =>
      obtain ⟨⟨k, hk⟩, d⟩ := md
      have hh : d = Dom.one ∧ k ≠ 0 := by
        by_cases hd1 : d = Dom.one <;> by_cases hm : k = 0 <;> simp_all [T.dom]
      obtain ⟨rfl, hm⟩ := hh
      cases k with
      | zero => exact False.elim (hm rfl)
      | succ k => exact ⟨k, hk, rfl⟩

theorem T.dom_zero_eq_Z {lam : Nat} (s : T lam)
    (hdom : T.dom s = .zero) : s = T.Z := by
  cases s with
  | Z => rfl
  | P ls add =>
      by_cases hadd : add = T.Z
      · subst add
        simp only [T.dom, ite_true] at hdom
        split at hdom
        · cases hdom
        · split at hdom
          · split at hdom <;> cases hdom
          · cases hdom
      · rw [T.dom, ite_eq_right hadd] at hdom
        exact False.elim (hadd (T.dom_zero_eq_Z add hdom))

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
                  | zero => exact T.mul_PZ_lt_of_compareVec_lt _ _ _ (Vec.compare_rplc_lt _ _ _ (hrec T.Z))
                  | succ r =>
                      exact T.P_lt_P_of_compareVec_lt _ _ _ _
                        (Vec.compare_rplc_rplc_lt _ _ _ _ _ (Nat.lt_succ_self r) (hrec T.Z))
                · simp only [hd1, ite_false]
                  split <;> exact T.P_lt_P_of_compareVec_lt _ _ _ _ (Vec.compare_rplc_lt _ _ _ (hrec _))
          · rw [T.fund, ite_eq_right hadd]
            change (match compareVec ls ls with
              | .eq => compareT (T.fund add t) add | ord => ord) = .lt
            rw [Vec_refl]
            exact ih _ (T.add_size_lt_P ls add) t hadd

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

theorem T.head_fund_le {lam : Nat}
    (s t : T lam) :
    T.head (T.fund s t) ≤ T.head s := by
  cases s with
  | Z => rw [T.fund]; exact T.Z_le _
  | P ls add => exact T.head_mono _ _ (T.fund_lt_self _ _ (by intro h; cases h))

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
  | nil => exact i.elim0
  | snoc k xs last ih =>
      by_cases h : i.val < k
      · simp only [Vec.idx, h, dite_true, T.G.res, List.mem_append, List.mem_singleton]
        exact Or.inl (Or.inl (ih ⟨i.val, h⟩))
      · simp [Vec.idx, h, T.G.res]

theorem Vec.Gres_mem_G_of_idx {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m)
    (y : T lam) (hy : y ∈ T.G (v.idx i)) :
    y ∈ T.G.res v := by
  induction v with
  | nil => exact i.elim0
  | snoc k xs last ih =>
      by_cases h : i.val < k
      · simp only [Vec.idx, h, dite_true] at hy
        exact List.mem_append_left _ (List.mem_append_left _ (ih ⟨i.val, h⟩ hy))
      · simp only [Vec.idx, h, dite_false] at hy
        exact List.mem_append_right _ hy

theorem Vec.Gres_cases {lam m : Nat}
    (v : Vec (T lam) m) (y : T lam)
    (hy : y ∈ T.G.res v) :
    ∃ i : Fin m, y = v.idx i ∨ y ∈ T.G (v.idx i) := by
  induction v with
  | nil => cases hy
  | snoc k xs last ih =>
      simp only [T.G.res, List.mem_append, List.mem_singleton] at hy
      rcases hy with (hxs | rfl) | hG
      · obtain ⟨i, hi⟩ := ih hxs
        exact ⟨i.castSucc, by simpa [Vec.idx, i.isLt] using hi⟩
      · exact ⟨Fin.last k, Or.inl (by simp [Vec.idx])⟩
      · exact ⟨Fin.last k, Or.inr (by simpa [Vec.idx] using hG)⟩

theorem T.mem_G_P {lam : Nat}
    (ls : Vec (T lam) lam) (add y : T lam) :
    y ∈ T.G (T.P ls add) ↔
      (∃ i : Fin lam,
        y = ls.idx i ∨ y ∈ T.G (ls.idx i)) ∨
      y ∈ T.G add := by
  rw [T.G_P_eq, List.mem_append]
  apply or_congr_left
  constructor
  · exact Vec.Gres_cases ls y
  · rintro ⟨i, rfl | h⟩
    · exact Vec.Gres_mem_of_idx ls i
    · exact Vec.Gres_mem_G_of_idx ls i y h

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
    (fun y => (inferInstance : Decidable (T.lt y x)))

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
  exact ⟨T.isNF.z, by intro y hy; cases hy⟩

theorem T.isNF_P_coord_NFComp {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNF (T.P ls add)) :
    ∀ i : Fin lam, T.isNFComp (ls.idx i) := by
  cases hs with
  | p _ _ h0 _ h2 _ => exact fun i => ⟨h0 _ (Vec.idx_mem_toList ls i), h2 _ (Vec.idx_mem_toList ls i)⟩

theorem T.isNF_PZ_of_coords {lam : Nat}
    (ls : Vec (T lam) lam)
    (h : ∀ i : Fin lam, T.isNFComp (ls.idx i)) :
    T.isNF (T.P ls T.Z) := by
  have hc : ∀ x ∈ Vec.toList ls, T.isNFComp x := by
    intro x hx
    obtain ⟨i, rfl⟩ := Vec.mem_toList_exists_idx ls x hx
    exact h i
  exact T.isNF.p ls T.Z (fun x hx => (hc x hx).1) T.isNF.z
    (fun x hx => (hc x hx).2) (Or.inl rfl)

theorem T.coord_lt_of_NFComp_P {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (hs : T.isNFComp (T.P ls add)) :
    ∀ i : Fin lam, ls.idx i < T.P ls add := by
  exact fun i => hs.2 _ ((T.mem_G_P ls add _).mpr (Or.inl ⟨i, Or.inl rfl⟩))

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
  | Z => rfl
  | P xs xadd =>
      have hvlt : compareVec xs v = .lt := by
        change (match compareVec xs v with
          | .eq => compareT xadd T.Z | ord => ord) = .lt at hold
        cases hc : compareVec xs v with
        | lt => rfl
        | eq => rw [hc] at hold; cases xadd <;> cases hold
        | gt => simp [hc] at hold
      apply T.P_lt_P_of_compareVec_lt
      apply Vec.compare_lt_after_pivot_update xs v w q (fun j hj => (hhigh j hj).symm) hvlt
      rw [hwq]
      exact T.coord_lt_of_NFComp_P xs xadd hx q

theorem T.rplc_min_NFComp_closed {lam : Nat}
    (ls : Vec (T lam) lam) (m : Fin lam)
    (d : Dom) (a : T lam)
    (hs : T.isNFComp (T.P ls T.Z))
    (hmin : T.domVecMinIdx ls = some (m, d))
    (ha : T.isNFComp a)
    (halt : a < ls.idx m) :
    T.isNFComp (T.P (ls.rplc m a) T.Z) := by
  have hspec := T.domVecMinIdx_some_spec ls m d hmin
  have holdCoord := T.isNF_P_coord_NFComp ls T.Z hs.1
  have hcoord (i : Fin lam) : T.isNFComp ((ls.rplc m a).idx i) := by
    by_cases hi : i.val = m.val
    · rw [Fin.eq_of_val_eq hi, Vec.rplc_idx_same]; exact ha
    · rw [Vec.rplc_idx_of_ne _ _ _ _ hi]; exact holdCoord i
  have hilt (i : Fin lam) : (ls.rplc m a).idx i < T.P (ls.rplc m a) T.Z := by
    by_cases hi : i.val < m.val
    · rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hi), T.dom_zero_eq_Z _ (hspec.2.2 i hi)]
      rfl
    · refine T.term_lt_P_of_self_at _ ls _ i (hcoord i) ?_ rfl ?_
      · by_cases him : i.val = m.val
        · rw [Fin.eq_of_val_eq him, Vec.rplc_idx_same]
          exact strict_partial_order.trans _ _ _ halt (T.coord_lt_of_NFComp_P ls T.Z hs m)
        · rw [Vec.rplc_idx_of_ne _ _ _ _ him]
          exact T.coord_lt_of_NFComp_P ls T.Z hs i
      · intro j hj
        exact Vec.rplc_idx_of_ne _ _ _ _ (by omega)
  refine ⟨T.isNF_PZ_of_coords _ hcoord, ?_⟩
  intro y hy
  rcases (T.mem_G_P _ _ y).mp hy with ⟨i, rfl | hyg⟩ | hz
  · exact hilt i
  · exact strict_partial_order.trans _ _ _ ((hcoord i).2 y hyg) (hilt i)
  · cases hz

theorem Vec.mem_toList_iff_idx {A : Type} {n : Nat}
    (v : Vec A n) (x : A) :
    x ∈ Vec.toList v ↔ ∃ i : Fin n, v.idx i = x := by
  exact ⟨Vec.mem_toList_exists_idx v x, fun ⟨i, hi⟩ => hi ▸ Vec.idx_mem_toList v i⟩

theorem T.P_tail_lt {lam : Nat} (ls : Vec (T lam) lam)
    (a b : T lam) (h : a < b) :
    T.P ls a < T.P ls b := by
  simpa only [LT.lt, T.lt, compareT, Vec_refl] using h

theorem T.le_refl {lam : Nat} (a : T lam) : a ≤ a := by
  exact Or.inr (T_refl a)

theorem T.le_trans {lam : Nat} (a b c : T lam)
    (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases hab with h | h
  · rcases hbc with h' | h'
    · exact Or.inl (T_trans _ _ _ h h')
    · rw [← T_eq_sound _ _ h']; exact Or.inl h
  · rwa [T_eq_sound _ _ h]

theorem T.le_antisymm {lam : Nat} (a b : T lam)
    (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases hab with h | h
  · rcases hba with h' | h'
    · exact False.elim (strict_partial_order.irrefl a (T_trans _ _ _ h h'))
    · exact (T_eq_sound _ _ h').symm
  · exact T_eq_sound _ _ h

theorem T.P_le_P_same {lam : Nat} (ls : Vec (T lam) lam)
    (a b : T lam) (h : a ≤ b) :
    T.P ls a ≤ T.P ls b := by
  simpa only [LE.le, T.le, compareT, Vec_refl] using h

theorem T.isNF_G_isNFComp {lam : Nat} (s : T lam)
    (hs : T.isNF s) :
    ∀ x ∈ T.G s, T.isNFComp x := by
  induction hs with
  | z => intro x hx; cases hx
  | p ls add h0 _ h2 _ ih0 ih1 =>
      intro x hx
      rcases (T.mem_G_P ls add x).mp hx with ⟨i, rfl | hi⟩ | hi
      · exact ⟨h0 _ (Vec.idx_mem_toList ls i), h2 _ (Vec.idx_mem_toList ls i)⟩
      · exact ih0 _ (Vec.idx_mem_toList ls i) x hi
      · exact ih1 x hi

theorem T.head_mono_le {lam : Nat} (a b : T lam)
    (h : a ≤ b) : T.head a ≤ T.head b := by
  rcases h with h | h
  · exact T.head_mono _ _ h
  · rw [T_eq_sound _ _ h]; exact T.le_refl _

theorem T.P_same_le_iff {lam : Nat} (ls : Vec (T lam) lam)
    (a b : T lam) :
    T.P ls a ≤ T.P ls b ↔ a ≤ b := by
  simp only [LE.le, T.le, compareT, Vec_refl]

theorem T.sandwich_same_vector {lam : Nat}
    (ls : Vec (T lam) lam) (a b c : T lam)
    (hl : T.P ls a ≤ c)
    (hu : c ≤ T.P ls b) :
    ∃ d, c = T.P ls d ∧ a ≤ d ∧ d ≤ b := by
  have hh := T.le_antisymm _ _ (T.head_mono_le c (T.P ls b) hu) (T.head_mono_le (T.P ls a) c hl)
  cases c with
  | Z => cases hh
  | P cs d =>
      change T.P cs T.Z = T.P ls T.Z at hh
      cases hh
      exact ⟨d, rfl, (T.P_same_le_iff _ _ _).mp hl, (T.P_same_le_iff _ _ _).mp hu⟩

theorem T.vector_rel_of_P_le_P {lam : Nat}
    (v w : Vec (T lam) lam) (a b : T lam)
    (h : T.P v a ≤ T.P w b) :
    compareVec v w = Ordering.lt ∨ v = w := by
  rcases h with h | h
  · change (match compareVec v w with
      | .eq => compareT a b | ord => ord) = .lt at h
    cases hc : compareVec v w with
    | lt => exact Or.inl rfl
    | eq => exact Or.inr (Vec_eq_sound _ _ hc)
    | gt => simp [hc] at h
  · cases T_eq_sound _ _ h; exact Or.inr rfl

theorem T.lt_of_le_of_lt {lam : Nat} (a b c : T lam)
    (hab : a ≤ b) (hbc : b < c) : a < c := by
  rcases hab with h | h
  · exact T_trans _ _ _ h hbc
  · rwa [T_eq_sound _ _ h]

theorem T.lt_of_lt_of_le {lam : Nat} (a b c : T lam)
    (hab : a < b) (hbc : b ≤ c) : a < c := by
  rcases hbc with h | h
  · exact T_trans _ _ _ hab h
  · rwa [← T_eq_sound _ _ h]

def T.GZ {lam : Nat} (z : T lam) : List (T lam) :=
  [z] ++ T.G z ++ [T.Z]

def T.listLe {lam : Nat} (xs ys : List (T lam)) : Prop :=
  ∀ x, x ∈ xs → ∃ y, y ∈ ys ∧ x ≤ y

def T.SDom {lam : Nat} (z b a : T lam) : Prop :=
  b < a ∧
    ∀ c, b ≤ c → c ≤ a →
      T.listLe (T.G b) (T.G c ++ T.GZ z)

def T.ZeroDom {lam : Nat} (b a : T lam) : Prop :=
  b < a ∧
    ∀ c : T lam, b ≤ c → c ≤ a →
      ∀ x ∈ T.G b,
        ∃ y : T lam, y ∈ T.G c ++ [T.Z] ∧ x ≤ y

theorem T.SDom_tail {lam : Nat}
    (z b a : T lam) (ls : Vec (T lam) lam)
    (hs : T.SDom z b a) :
    T.SDom z (T.P ls b) (T.P ls a) := by
  refine ⟨T.P_tail_lt ls b a hs.1, ?_⟩
  intro c hbc hca x hx
  obtain ⟨d, rfl, hbd, hda⟩ := T.sandwich_same_vector ls b a c hbc hca
  rcases (T.mem_G_P ls b x).mp hx with hv | ht
  · exact ⟨x, List.mem_append_left _ ((T.mem_G_P ls d x).mpr (Or.inl hv)), T.le_refl x⟩
  · obtain ⟨y, hy, hxy⟩ := hs.2 d hbd hda x ht
    refine ⟨y, ?_, hxy⟩
    simpa [T.G_P_eq, List.mem_append, or_assoc] using Or.inr hy

theorem T.ZeroDom_tail {lam : Nat}
    (ls : Vec (T lam) lam) (a b : T lam)
    (hdom : T.ZeroDom b a) :
    T.ZeroDom (T.P ls b) (T.P ls a) := by
  have hs : T.SDom T.Z b a := by simpa [T.SDom, T.listLe, T.GZ, T.G, T.ZeroDom] using hdom
  simpa [T.SDom, T.listLe, T.GZ, T.G, T.ZeroDom] using T.SDom_tail T.Z b a ls hs

theorem T.fund_one_master {lam : Nat} (s : T lam) :
    ∀ (_ : T.isNF s), T.dom s = .one →
      T.isNF (T.fund s T.Z) ∧
        T.ZeroDom (T.fund s T.Z) s := by
  intro hs
  induction hs with
  | z => intro h; cases h
  | p ls add h0 _ h2 h3 _ ih =>
      intro hd
      by_cases hadd : add = T.Z
      · subst add
        rw [T.fund_PZ_none ls T.Z ((T.dom_PZ_one_iff ls).mp hd)]
        exact ⟨T.isNF.z, rfl, by intro c _ _ x hx; cases hx⟩
      · obtain ⟨hnf, hrel⟩ := ih (by simpa [T.dom, hadd] using hd)
        rw [T.fund, ite_eq_right hadd]
        exact ⟨T.isNF.p ls _ h0 hnf h2 (T.le_trans _ _ _ (T.head_fund_le add T.Z) h3),
          T.ZeroDom_tail ls add _ hrel⟩

theorem T.G_size_lt {lam : Nat} :
    ∀ s y : T lam, y ∈ T.G s → T.size y < T.size s := by
  intro s
  induction s using (measure T.size).wf.induction with
  | h s ih =>
      intro y hy
      cases s with
      | Z => cases hy
      | P ls add =>
          rcases (T.mem_G_P ls add y).mp hy with ⟨i, rfl | hG⟩ | hG
          · exact T.idx_size_lt_P ls add i
          · have hi := T.idx_size_lt_P ls add i
            exact Nat.lt_trans (ih _ hi y hG) hi
          · have hi := T.add_size_lt_P ls add
            exact Nat.lt_trans (ih _ hi y hG) hi

theorem T.G_trans {lam : Nat} :
    ∀ a x y : T lam,
      x ∈ T.G a → y ∈ T.G x → y ∈ T.G a := by
  intro a
  induction a using (measure T.size).wf.induction with
  | h a ih =>
      intro x y hx hy
      cases a with
      | Z => cases hx
      | P ls add =>
          apply (T.mem_G_P ls add y).mpr
          rcases (T.mem_G_P ls add x).mp hx with ⟨i, rfl | hG⟩ | hG
          · exact Or.inl ⟨i, Or.inr hy⟩
          · exact Or.inl ⟨i, Or.inr (ih _ (T.idx_size_lt_P ls add i) x y hG hy)⟩
          · exact Or.inr (ih _ (T.add_size_lt_P ls add) x y hG hy)

theorem T.exists_G_not_lt {lam : Nat} (s b : T lam)
    (h : ¬ (∀ x ∈ T.G s, x < b)) :
    ∃ x, x ∈ T.G s ∧ ¬ x < b := by
  generalize T.G s = l at h ⊢
  induction l with
  | nil => exact False.elim (h (by simp))
  | cons a as ih =>
      by_cases ha : T.lt a b
      · obtain ⟨x, hx, hn⟩ := ih (fun hall => h (by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hall x hx))
        exact ⟨x, List.mem_cons_of_mem a hx, hn⟩
      · exact ⟨a, List.mem_cons_self, ha⟩

theorem T.find_violating_source {lam : Nat}
    (b c₀ w : T lam)
    (hw : w ∈ T.G c₀) (hbw : b ≤ w) :
    ∃ c, c ∈ T.G c₀ ∧ b ≤ c ∧
      ∀ x ∈ T.G c, x < b := by
  induction w using (measure T.size).wf.induction with
  | h w ih =>
      cases T.decForallMem (T.G w) (fun x => x < b) (fun x => inferInstanceAs (Decidable (T.lt x b))) with
      | isTrue h => exact ⟨w, hw, hbw, h⟩
      | isFalse h =>
          obtain ⟨x, hx, hn⟩ := T.exists_G_not_lt w b h
          apply ih x (T.G_size_lt w x hx) (T.G_trans c₀ w x hw hx)
          rcases T_total x b with h | h | rfl
          · exact False.elim (hn h)
          · exact Or.inl h
          · exact T.le_refl _

theorem T.GZ_lt_of_NFComp_lt {lam : Nat}
    (z b : T lam)
    (hz : T.isNFComp z) (hzb : z < b) :
    ∀ x ∈ T.GZ z, x < b := by
  intro x hx
  simp only [T.GZ, List.mem_append, List.mem_singleton] at hx
  rcases hx with (rfl | hx) | rfl
  · exact hzb
  · exact T_trans _ _ _ (hz.2 x hx) hzb
  · exact T.lt_of_le_of_lt _ _ _ (T.Z_le z) hzb

theorem T.SDom_G_lt_upper {lam : Nat}
    (z b a : T lam)
    (hs : T.SDom z b a)
    (hGa : ∀ x ∈ T.G a, x < a)
    (hGz : ∀ x ∈ T.GZ z, x < b) :
    ∀ y ∈ T.G b, y < a := by
  intro y hy
  obtain ⟨w, hw, hyw⟩ := hs.2 a (Or.inl hs.1) (T.le_refl a) y hy
  apply T.lt_of_le_of_lt _ _ _ hyw
  rcases List.mem_append.mp hw with h | h
  · exact hGa w h
  · exact T_trans _ _ _ (hGz w h) hs.1

theorem T.SDom_G_closed {lam : Nat}
    (z b a : T lam)
    (hs : T.SDom z b a)
    (hGa : ∀ x ∈ T.G a, x < a)
    (hGz : ∀ x ∈ T.GZ z, x < b) :
    ∀ y ∈ T.G b, y < b := by
  intro y hy
  by_cases hyb : T.lt y b
  · exact hyb
  · have hby : b ≤ y := by
      rcases T_total y b with h | h | rfl
      · exact False.elim (hyb h)
      · exact Or.inl h
      · exact T.le_refl _
    obtain ⟨c, hcG, hbc, hcBound⟩ := T.find_violating_source b b y hy hby
    obtain ⟨w, hw, hcw⟩ := hs.2 c hbc (Or.inl (T.SDom_G_lt_upper z b a hs hGa hGz c hcG)) c hcG
    have hwb : w < b := (List.mem_append.mp hw).elim (hcBound w) (hGz w)
    exact False.elim (strict_partial_order.irrefl b
      (T.lt_of_le_of_lt _ _ _ hbc (T.lt_of_le_of_lt _ _ _ hcw hwb)))

theorem T.NFComp_of_SDom {lam : Nat}
    (z b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp a)
    (hz : T.isNFComp z)
    (hdom : T.SDom z b a)
    (hzb : z < b) :
    T.isNFComp b := by
  exact ⟨hb, T.SDom_G_closed z b a hdom ha.2 (T.GZ_lt_of_NFComp_lt z b hz hzb)⟩

theorem T.NFComp_of_SDom_Z_or_eq {lam : Nat}
    (b a : T lam)
    (hb : T.isNF b) (ha : T.isNFComp a)
    (hdom : T.SDom T.Z b a) :
    T.isNFComp b := by
  cases b with
  | Z => exact T.isNFComp_Z
  | P ls add => exact T.NFComp_of_SDom T.Z _ a hb ha T.isNFComp_Z hdom rfl

theorem T.NFComp_of_ZeroDom {lam : Nat}
    (a b : T lam) (hb : T.isNF b)
    (ha : T.isNFComp a) (hdom : T.ZeroDom b a) :
    T.isNFComp b := by
  apply T.NFComp_of_SDom_Z_or_eq b a hb ha
  simpa [T.SDom, T.listLe, T.GZ, T.G, T.ZeroDom] using hdom

theorem T.fund_one_NFComp_closed {lam : Nat} (s : T lam)
    (hs : T.isNFComp s) (hd : T.dom s = .one) :
    T.isNFComp (T.fund s T.Z) := by
  obtain ⟨hnf, hdom⟩ := T.fund_one_master s hs.1 hd
  exact T.NFComp_of_ZeroDom s _ hnf hs hdom

theorem T.rplc_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam) (i : Fin lam) (a : T lam)
    (hs : T.isNF (T.P ls T.Z))
    (ha : T.isNFComp a) :
    T.isNF (T.P (ls.rplc i a) T.Z) := by
  apply T.isNF_PZ_of_coords
  intro q
  by_cases h : q.val = i.val
  · rw [Fin.eq_of_val_eq h, Vec.rplc_idx_same]; exact ha
  · rw [Vec.rplc_idx_of_ne _ _ _ _ h]; exact T.isNF_P_coord_NFComp _ _ hs q

theorem T.rplc_two_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam) (i j : Fin lam)
    (a b : T lam)
    (hs : T.isNF (T.P ls T.Z))
    (ha : T.isNFComp a) (hb : T.isNFComp b) :
    T.isNF
      (T.P ((ls.rplc i a).rplc j b) T.Z) := by
  exact T.rplc_NF_closed _ j b (T.rplc_NF_closed ls i a hs ha) hb

theorem T.mul_PZ_lt_next {lam : Nat}
    (ls : Vec (T lam) lam) :
    ∀ t : T lam,
      T.mul (T.P ls T.Z) t <
        T.P ls (T.mul (T.P ls T.Z) t) := by
  intro t
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P us add _ ih => exact T.P_tail_lt ls _ _ ih
  | nil => trivial
  | snoc => trivial

theorem T.head_mul_PZ_le {lam : Nat}
    (ls : Vec (T lam) lam) :
    ∀ t : T lam,
      T.head (T.mul (T.P ls T.Z) t) ≤
        T.P ls T.Z := by
  intro t
  cases t with
  | Z => exact T.Z_le _
  | P tls add => exact T.le_refl _

theorem T.mul_PZ_NF_closed {lam : Nat}
    (ls : Vec (T lam) lam)
    (hbase : T.isNF (T.P ls T.Z)) :
    ∀ t : T lam,
      T.isNF (T.mul (T.P ls T.Z) t) := by
  intro t
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact T.isNF.z
  | P us add _ ih =>
      cases hbase with
      | p _ _ h0 _ h2 _ => exact T.isNF.p ls _ h0 ih h2 (T.head_mul_PZ_le ls add)
  | nil => trivial
  | snoc => trivial

theorem T.mul_PZ_NFComp_closed {lam : Nat}
    (ls : Vec (T lam) lam)
    (hbase : T.isNFComp (T.P ls T.Z)) :
    ∀ t : T lam,
      T.isNFComp (T.mul (T.P ls T.Z) t) := by
  intro t
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact T.isNFComp_Z
  | P us add _ ih =>
      refine ⟨T.mul_PZ_NF_closed ls hbase.1 (T.P us add), ?_⟩
      intro y hy
      rcases (T.mem_G_P ls (T.mul (T.P ls T.Z) add) y).mp hy with hv | ht
      · exact T.lt_of_lt_of_le _ _ _ (hbase.2 y ((T.mem_G_P ls T.Z y).mpr (Or.inl hv)))
          (T.P_le_P_same ls _ _ (T.Z_le _))
      · exact T_trans _ _ _ (ih.2 y ht) (T.mul_PZ_lt_next ls add)
  | nil => trivial
  | snoc => trivial

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
  rcases hlm with hlt | rfl
  · obtain ⟨p, hpEq, hpLt⟩ := Vec.compare_lt_has_pivot low mid hlt
    have hpi : p.val ≤ i.val := by
      apply Nat.le_of_not_gt
      intro hip
      rcases hmh with h | rfl
      · obtain ⟨q, hqEq, hqLt⟩ := Vec.compare_lt_has_pivot mid high h
        rcases Nat.lt_trichotomy q.val p.val with hqp | heq | hpq
        · rw [hqEq p hqp, ← heqAbove p hip] at hpLt
          exact strict_partial_order.irrefl _ hpLt
        · obtain rfl := Fin.eq_of_val_eq heq
          have hc := T_trans _ _ _ hpLt hqLt
          rw [← heqAbove q hip] at hc
          exact strict_partial_order.irrefl (low.idx q) hc
        · rw [← hpEq q hpq, heqAbove q (by omega)] at hqLt
          exact strict_partial_order.irrefl _ hqLt
      · rw [← heqAbove p hip] at hpLt
        exact strict_partial_order.irrefl _ hpLt
    have hhigh (j : Fin m) (hj : i.val < j.val) : mid.idx j = high.idx j :=
      (hpEq j (by omega)).symm.trans (heqAbove j hj)
    refine ⟨hhigh, ?_, ?_⟩
    · rcases Nat.lt_or_eq_of_le hpi with h | h
      · rw [hpEq i h]; exact T.le_refl _
      · rw [Fin.eq_of_val_eq h] at hpLt; exact Or.inl hpLt
    · rcases hmh with h | rfl
      · obtain ⟨q, hqEq, hqLt⟩ := Vec.compare_lt_has_pivot mid high h
        have hqi : q.val ≤ i.val := by
          apply Nat.le_of_not_gt
          intro hiq
          rw [hhigh q hiq] at hqLt
          exact strict_partial_order.irrefl _ hqLt
        rcases Nat.lt_or_eq_of_le hqi with h | h
        · rw [hqEq i h]; exact T.le_refl _
        · rw [Fin.eq_of_val_eq h] at hqLt; exact Or.inl hqLt
      · exact T.le_refl _
  · exact ⟨heqAbove, T.le_refl _, Or.inl hpivot⟩

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
  refine ⟨T.P_lt_P_of_compareVec_lt _ _ _ _ (Vec.compare_lt_of_pivot low high i hAbove hPivotLt), ?_⟩
  intro c hlc hch
  cases c with
  | Z => rcases hlc with h | h <;> cases h
  | P mid add =>
      have hBetween := Vec.interval_pivot_properties low mid high i hAbove hPivotLt
        (T.vector_rel_of_P_le_P _ _ _ _ hlc) (T.vector_rel_of_P_le_P _ _ _ _ hch)
      intro x hx
      rcases (T.mem_G_P low T.Z x).mp hx with ⟨q, hqx⟩ | ht
      · rcases Nat.lt_trichotomy q.val i.val with hqi | hqi | hiq
        · refine ⟨x, List.mem_append_right _ ?_, T.le_refl x⟩
          rcases hBelow q hqi with hz | hz
          · simp only [hz, T.G, List.not_mem_nil, or_false] at hqx
            subst x; simp [T.GZ]
          · rw [hz] at hqx
            simp only [T.GZ, List.mem_append, List.mem_singleton]
            exact Or.inl hqx
        · obtain rfl := Fin.eq_of_val_eq hqi
          refine ⟨mid.idx q, List.mem_append_left _ ((T.mem_G_P mid add _).mpr (Or.inl ⟨q, Or.inl rfl⟩)), ?_⟩
          rcases hqx with rfl | hx
          · exact hBetween.2.1
          · exact Or.inl (T.lt_of_lt_of_le _ _ _ (hPivotComp.2 x hx) hBetween.2.1)
        · have he := (hAbove q hiq).trans (hBetween.1 q hiq).symm
          rw [he] at hqx
          exact ⟨x, List.mem_append_left _ ((T.mem_G_P mid add x).mpr (Or.inl ⟨q, hqx⟩)), T.le_refl x⟩
      · cases ht

theorem Vec.compare_rplc_same_index_lt {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m)
    (a b : T lam) (hab : a < b) :
    compareVec (v.rplc i a) (v.rplc i b) =
      Ordering.lt := by
  apply Vec.compare_lt_of_pivot _ _ i
  · intro j hij
    rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hij), Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hij)]
  · simpa only [Vec.rplc_idx_same] using hab

theorem T.fund_P_tail_eq {lam : Nat}
    (ls : Vec (T lam) lam) (add t : T lam)
    (hadd : add ≠ T.Z) :
    T.fund (T.P ls add) t =
      T.P ls (T.fund add t) := by
  rw [T.fund, ite_eq_right hadd]

theorem T.fund_Omega_ne_Z {lam : Nat}
    (s t : T lam) (hd : T.dom s = .Omega) :
    T.fund s t ≠ T.Z := by
  cases s with
  | Z => cases hd
  | P ls add =>
      by_cases hadd : add = T.Z
      · subst add
        obtain ⟨k, hk, hmin⟩ := T.dom_PZ_Omega ls hd
        rw [T.fund, ite_eq_left rfl, hmin]; intro h; cases h
      · rw [T.fund_P_tail_eq _ _ _ hadd]; intro h; cases h

theorem T.fund_Omega_strict_mono {lam : Nat}
    (s x y : T lam)
    (hd : T.dom s = .Omega)
    (hxy : x < y) :
    T.fund s x < T.fund s y := by
  induction s using T.rec (motive_2 := fun _ _ => True) with
  | Z => cases hd
  | P ls add _ ih =>
      by_cases hadd : add = T.Z
      · subst add
        obtain ⟨k, hk, hmin⟩ := T.dom_PZ_Omega ls hd
        rw [T.fund, ite_eq_left rfl, hmin, T.fund, ite_eq_left rfl, hmin]
        exact T.P_lt_P_of_compareVec_lt _ _ _ _ (Vec.compare_rplc_same_index_lt _ _ _ _ hxy)
      · rw [T.fund_P_tail_eq _ _ _ hadd, T.fund_P_tail_eq _ _ _ hadd]
        exact T.P_tail_lt _ _ _ (ih (by simpa [T.dom, hadd] using hd))
  | nil => trivial
  | snoc => trivial

theorem T.iter_fund_lt_next {lam : Nat}
    (s t : T lam) (hd : T.dom s = .Omega) :
    T.iter (fun x => T.fund s x) t <
      T.fund s
        (T.iter (fun x => T.fund s x) t) := by
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z =>
      rw [T.iter]
      cases he : T.fund s T.Z with
      | Z => exact False.elim (T.fund_Omega_ne_Z s T.Z hd he)
      | P ls add => rfl
  | P us add _ ih => exact T.fund_Omega_strict_mono s _ _ hd ih
  | nil => trivial
  | snoc => trivial

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
  apply T.SDom_PZ_pivot_comp z ((ls.rplc m b).rplc j z) ls m
  · intro q hq
    rw [Vec.rplc_idx_of_ne _ _ _ _ (by omega), Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hq)]
  · simpa only [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hjm), Vec.rplc_idx_same] using hblt
  · simpa only [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hjm), Vec.rplc_idx_same] using hb
  · intro q hq
    by_cases hqj : q.val = j.val
    · right; rw [Fin.eq_of_val_eq hqj, Vec.rplc_idx_same]
    · left
      rw [Vec.rplc_idx_of_ne _ _ _ _ hqj, Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hq)]
      exact T.dom_zero_eq_Z _ ((T.domVecMinIdx_some_spec ls m d hmin).2.2 q hq)

theorem T.fund_Omega_master {lam : Nat}
    (s z : T lam)
    (hs : T.isNF s)
    (hd : T.dom s = .Omega)
    (hz : T.isNFComp z) :
    T.isNF (T.fund s z) ∧
      T.SDom z (T.fund s z) s := by
  induction hs with
  | z => cases hd
  | p ls add h0 h1 h2 h3 _ ih =>
      by_cases hadd : add = T.Z
      · subst add
        have hparent := T.isNF.p ls T.Z h0 h1 h2 h3
        obtain ⟨k, hk, hmin⟩ := T.dom_PZ_Omega ls hd
        have hspec := T.domVecMinIdx_some_spec ls ⟨k + 1, hk⟩ Dom.one hmin
        have hc := T.fund_one_NFComp_closed _ (T.isNF_P_coord_NFComp ls T.Z hparent _) hspec.2.1
        have hlt := T.fund_lt_self (ls.idx ⟨k + 1, hk⟩) T.Z (by
          intro he; have hd := hspec.2.1; rw [he] at hd; cases hd)
        rw [T.fund, ite_eq_left rfl, hmin]
        exact ⟨T.rplc_two_NF_closed _ _ _ _ z hparent hc hz,
          T.SDom_rplc_lower z ls _ _ Dom.one _ (Nat.lt_succ_self k) hmin hc hlt⟩
      · obtain ⟨hnf, hsd⟩ := ih (by simpa [T.dom, hadd] using hd)
        rw [T.fund_P_tail_eq _ _ _ hadd]
        exact ⟨T.isNF.p ls _ h0 hnf h2 (T.le_trans _ _ _ (T.head_fund_le add z) h3),
          T.SDom_tail z _ add ls hsd⟩

theorem T.fund_iter_NFComp_core {lam : Nat} (s t : T lam)
    (hs : T.isNFComp s)
    (hd : T.dom s = .Omega) :
    T.isNFComp
      (T.fund s (T.iter (fun x => T.fund s x) t)) := by
  have step (u) (hu : T.isNFComp (T.iter (T.fund s) u)) :
      T.isNFComp (T.fund s (T.iter (T.fund s) u)) := by
    obtain ⟨hnf, hsd⟩ := T.fund_Omega_master s _ hs.1 hd hu
    exact T.NFComp_of_SDom _ _ s hnf hs hu hsd (T.iter_fund_lt_next s u hd)
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => exact step T.Z T.isNFComp_Z
  | P us add _ ih => exact step (T.P us add) ih
  | nil => trivial
  | snoc => trivial

theorem T.G_mul_PZ_subset {lam : Nat}
    (ls : Vec (T lam) lam) :
    ∀ t x : T lam,
      x ∈ T.G (T.mul (T.P ls T.Z) t) →
        x ∈ T.G (T.P ls T.Z) := by
  intro t
  induction t using T.rec (motive_2 := fun _ _ => True) with
  | Z => intro x hx; cases hx
  | P us add _ ih =>
      intro x hx
      rcases (T.mem_G_P ls (T.mul (T.P ls T.Z) add) x).mp hx with hv | ht
      · exact (T.mem_G_P ls T.Z x).mpr (Or.inl hv)
      · exact ih x ht
  | nil => trivial
  | snoc => trivial

theorem T.SDom_mul_PZ {lam : Nat}
    (u v : Vec (T lam) lam) (t : T lam)
    (hvec : compareVec u v = Ordering.lt)
    (hbase :
      T.SDom T.Z (T.P u T.Z) (T.P v T.Z)) :
    T.SDom T.Z
      (T.mul (T.P u T.Z) t) (T.P v T.Z) := by
  refine ⟨T.mul_PZ_lt_of_compareVec_lt u v t hvec, ?_⟩
  intro c hmc hcv x hx
  cases t with
  | Z => cases hx
  | P ts add =>
      exact hbase.2 c (T.le_trans _ _ _ (T.P_le_P_same u _ _ (T.Z_le _)) hmc) hcv x
        (T.G_mul_PZ_subset u (T.P ts add) x hx)

theorem T.SDom_rplc_min_Z {lam : Nat}
    (ls : Vec (T lam) lam) (m : Fin lam) (d : Dom)
    (b : T lam)
    (hmin : T.domVecMinIdx ls = some (m, d))
    (hb : T.isNFComp b)
    (hblt : b < ls.idx m) :
    T.SDom T.Z
      (T.P (ls.rplc m b) T.Z)
      (T.P ls T.Z) := by
  apply T.SDom_PZ_pivot_comp T.Z (ls.rplc m b) ls m
  · exact fun j hj => Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_gt hj)
  · simpa only [Vec.rplc_idx_same] using hblt
  · simpa only [Vec.rplc_idx_same] using hb
  · intro q hq
    left
    rw [Vec.rplc_idx_of_ne _ _ _ _ (Nat.ne_of_lt hq)]
    exact T.dom_zero_eq_Z _ ((T.domVecMinIdx_some_spec ls m d hmin).2.2 q hq)

theorem T.fund_omega_master {lam : Nat}
    (s t : T lam)
    (hs : T.isNF s)
    (hd : T.dom s = .omega) :
    T.isNF (T.fund s t) ∧
      T.SDom T.Z (T.fund s t) s := by
  induction hs with
  | z => cases hd
  | p ls add h0 h1 h2 h3 ihls ihadd =>
      by_cases hadd : add = T.Z
      · subst add
        have hparent := T.isNF.p ls T.Z h0 h1 h2 h3
        cases hmin : T.domVecMinIdx ls with
        | none => simp [T.dom, hmin] at hd
        | some md =>
            obtain ⟨m, d⟩ := md
            have hspec := T.domVecMinIdx_some_spec ls m d hmin
            have hc := T.isNF_P_coord_NFComp ls T.Z hparent m
            have hne : ls.idx m ≠ T.Z := by
              intro he; have h := hspec.2.1; rw [he] at h; exact hspec.1 h.symm
            have lift (u) (hu : T.isNFComp (T.fund (ls.idx m) u)) :
                T.isNF (T.P (ls.rplc m (T.fund (ls.idx m) u)) T.Z) ∧
                T.SDom T.Z (T.P (ls.rplc m (T.fund (ls.idx m) u)) T.Z) (T.P ls T.Z) :=
              ⟨T.rplc_NF_closed ls m _ hparent hu,
                T.SDom_rplc_min_Z ls m d _ hmin hu (T.fund_lt_self _ u hne)⟩
            cases d with
            | zero => exact False.elim (hspec.1 rfl)
            | one =>
                have hm0 : m.val = 0 := by
                  by_cases hm : m.val = 0 <;> simp_all [T.dom]
                have hu := T.fund_one_NFComp_closed _ hc hspec.2.1
                obtain ⟨hnf, hsd⟩ := lift T.Z hu
                obtain ⟨mv, mh⟩ := m
                change mv = 0 at hm0
                subst mv
                rw [T.fund, ite_eq_left rfl, hmin]
                exact ⟨T.mul_PZ_NF_closed _ hnf t, T.SDom_mul_PZ _ _ t
                  (Vec.compare_rplc_lt _ _ _ (T.fund_lt_self _ _ hne)) hsd⟩
            | omega =>
                obtain ⟨hnf, hsd⟩ := ihls _ (Vec.idx_mem_toList ls m) hspec.2.1
                rw [T.fund, ite_eq_left rfl, hmin]
                exact lift t (T.NFComp_of_SDom_Z_or_eq _ _ hnf hc hsd)
            | Omega =>
                rw [T.fund, ite_eq_left rfl, hmin]
                exact lift _ (T.fund_iter_NFComp_core _ t hc hspec.2.1)
      · obtain ⟨hnf, hsd⟩ := ihadd (by simpa [T.dom, hadd] using hd)
        rw [T.fund_P_tail_eq _ _ _ hadd]
        exact ⟨T.isNF.p ls _ h0 hnf h2 (T.le_trans _ _ _ (T.head_fund_le add t) h3),
          T.SDom_tail T.Z _ add ls hsd⟩

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
  exact ⟨fun hd t => T.fund_omega_master s t hs hd, fun hd z hz => T.fund_Omega_master s z hs hd hz⟩

theorem T.fund_omega_NFComp_closed {lam : Nat} (s t : T lam)
    (hs : T.isNFComp s)
    (hd : T.dom s = .omega) :
    T.isNFComp (T.fund s t) := by
  obtain ⟨hnf, hsd⟩ := T.fund_omega_master s t hs.1 hd
  exact T.NFComp_of_SDom_Z_or_eq _ s hnf hs hsd

theorem T.fund_iter_NFComp {lam : Nat} (s t : T lam)
    (hs : T.isNFComp s)
    (hd : T.dom s = .Omega) :
    T.isNFComp
      (T.fund s (T.iter (fun x => T.fund s x) t)) := by
  exact T.fund_iter_NFComp_core s t hs hd

theorem T.fund_one_arg_irrel {lam : Nat}
    (s t : T lam) (hd : T.dom s = .one) :
    T.fund s t = T.fund s T.Z := by
  induction s using T.rec (motive_2 := fun _ _ => True) with
  | Z => cases hd
  | P ls add _ ih =>
      by_cases hadd : add = T.Z
      · subst add
        have hn := (T.dom_PZ_one_iff ls).mp hd
        rw [T.fund_PZ_none _ _ hn, T.fund_PZ_none _ _ hn]
      · rw [T.fund_P_tail_eq _ _ _ hadd, T.fund_P_tail_eq _ _ _ hadd,
          ih (by simpa [T.dom, hadd] using hd)]
  | nil => trivial
  | snoc => trivial

theorem T.fund_NF_closed {lam : Nat} (s t : T lam)
    (hs : T.isNF s)
    (ht : T.dom s = .Omega → T.isNFComp t) :
    T.isNF (T.fund s t) := by
  cases hdom : T.dom s with
  | zero => rw [T.dom_zero_eq_Z s hdom, T.fund]; exact T.isNF.z
  | one => rw [T.fund_one_arg_irrel s t hdom]; exact (T.fund_one_master s hs hdom).1
  | omega => exact (T.fund_omega_master s t hs hdom).1
  | Omega => exact (T.fund_Omega_master s t hs hdom (ht hdom)).1

end new
