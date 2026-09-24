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
    have hqj : q.val ≠ j.val := by
      intro heq
      have : q.val < i.val := heq ▸ hji
      exact (Nat.lt_asymm hiq this) hiq
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
