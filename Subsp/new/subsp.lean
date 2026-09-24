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

def T.decLt {lam : Nat} (x y : T lam) : Decidable (x < y) :=
  inferInstanceAs (Decidable (compareT x y = Ordering.lt))

def T.decLe {lam : Nat} (x y : T lam) : Decidable (x ≤ y) :=
  inferInstanceAs
    (Decidable
      (compareT x y = Ordering.lt ∨ compareT x y = Ordering.eq))

def T.decidableAllLt {lam : Nat} (l : List (T lam)) (x : T lam) :
    Decidable (∀ y ∈ l, y < x) :=
  match l with
  | [] => isTrue (fun y hy => False.elim (List.not_mem_nil hy))
  | y :: ys =>
    match T.decLt y x with
    | isFalse hny =>
      isFalse (fun h => hny (h y List.mem_cons_self))
    | isTrue hy =>
      match T.decidableAllLt ys x with
      | isFalse hnys =>
        isFalse (fun h =>
          hnys (fun z hz => h z (List.mem_cons_of_mem y hz)))
      | isTrue hys =>
        isTrue (fun z hz =>
          match List.mem_cons.mp hz with
          | Or.inl heq => heq ▸ hy
          | Or.inr hmem => hys z hmem)

def Vec.decidableAllG {lam m : Nat} (v : Vec (T lam) m) :
    Decidable (∀ x ∈ Vec.toList v, ∀ y ∈ T.G x, y < x) :=
  match v with
  | .nil =>
    isTrue (fun x hx => False.elim (List.not_mem_nil hx))
  | .snoc _ xs x =>
    match Vec.decidableAllG xs with
    | isFalse hnxs =>
      isFalse (fun h =>
        hnxs (fun y hy =>
          h y (List.mem_append_left [x] hy)))
    | isTrue hxs =>
      match T.decidableAllLt (T.G x) x with
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
            match T.decLe (T.head add) (T.P ls T.Z) with
            | isFalse hn3 =>
              isFalse (fun h =>
                match h with
                | .p _ _ _ _ _ h3 => hn3 h3)
            | isTrue h3 =>
              isTrue (T.isNF.p ls add h0 h1 h2 h3)

  def Vec.decAllNF {lam m : Nat} (v : Vec (T lam) m) :
      Decidable (∀ x ∈ Vec.toList v, T.isNF x) :=
    match v with
    | .nil =>
      isTrue (fun x hx => False.elim (List.not_mem_nil hx))
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
end

instance {lam : Nat} (s : T lam) : Decidable (T.isNF s) :=
  T.decIsNF s

def T.isNFComp {lam : Nat} (s : T lam) : Prop :=
  T.isNF s ∧ ∀ y ∈ T.G s, y < s

theorem T.domVecMinIdx_none_all_zero {lam m : Nat}
    (v : Vec (T lam) m) (h : T.domVecMinIdx v = none) :
    ∀ i : Fin m, T.dom (v.idx i) = .zero := by
  induction v with
  | nil =>
    intro i
    exact i.elim0
  | snoc k xs x ih =>
    intro i
    rw [T.domVecMinIdx] at h
    cases hrec : T.domVecMinIdx xs with
    | some p =>
      rw [hrec] at h
      cases h
    | none =>
      rw [hrec] at h
      by_cases hx : T.dom x = .zero
      · rw [if_pos hx] at h
        by_cases hi : i.val < k
        · change T.dom
            (if hlt : i.val < k then
              Vec.idx xs ⟨i.val, hlt⟩ else x) = .zero
          rw [dite_eq_left hi]
          exact ih hrec ⟨i.val, hi⟩
        · change T.dom
            (if hlt : i.val < k then
              Vec.idx xs ⟨i.val, hlt⟩ else x) = .zero
          rw [dite_eq_right hi]
          exact hx
      · rw [if_neg hx] at h
        cases h

theorem T.domVecMinIdx_some_spec {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) (d : Dom)
    (h : T.domVecMinIdx v = some (i, d)) :
    T.dom (v.idx i) = d ∧
      ∀ j : Fin m, j.val < i.val →
        T.dom (v.idx j) = .zero := by
  induction v generalizing d with
  | nil =>
    exact i.elim0
  | snoc k xs x ih =>
    rw [T.domVecMinIdx] at h
    cases hrec : T.domVecMinIdx xs with
    | some p =>
      cases p with
      | mk i' d' =>
        rw [hrec] at h
        have hspec := ih i' d' hrec
        cases h
        constructor
        · have hidx :
              (Vec.snoc k xs x).idx i'.castSucc = xs.idx i' := by
            change
              (if hlt : i'.val < k then
                Vec.idx xs ⟨i'.val, hlt⟩ else x) = xs.idx i'
            rw [dite_eq_left i'.isLt]
          rw [hidx]
          exact hspec.1
        · intro j hj
          have hjk : j.val < k :=
            Nat.lt_trans hj i'.isLt
          change T.dom
              (if hlt : j.val < k then
                Vec.idx xs ⟨j.val, hlt⟩ else x) = .zero
          rw [dite_eq_left hjk]
          exact hspec.2 ⟨j.val, hjk⟩ hj
    | none =>
      rw [hrec] at h
      by_cases hx : T.dom x = .zero
      · rw [if_pos hx] at h
        cases h
      · rw [if_neg hx] at h
        cases h
        constructor
        · change T.dom
            (if hlt : k < k then
              Vec.idx xs ⟨k, hlt⟩ else x) = T.dom x
          rw [dite_eq_right (Nat.lt_irrefl k)]
        · intro j hj
          have hjk : j.val < k := hj
          change T.dom
              (if hlt : j.val < k then
                Vec.idx xs ⟨j.val, hlt⟩ else x) = .zero
          rw [dite_eq_left hjk]
          exact T.domVecMinIdx_none_all_zero xs hrec ⟨j.val, hjk⟩

theorem T.domVecMinIdx_some_ne_zero {lam m : Nat}
    (v : Vec (T lam) m) (i : Fin m) (d : Dom)
    (h : T.domVecMinIdx v = some (i, d)) :
    d ≠ .zero := by
  induction v generalizing d with
  | nil =>
    exact i.elim0
  | snoc k xs x ih =>
    rw [T.domVecMinIdx] at h
    cases hrec : T.domVecMinIdx xs with
    | some p =>
      cases p with
      | mk i' d' =>
        rw [hrec] at h
        have hne := ih i' d' hrec
        cases h
        exact hne
    | none =>
      rw [hrec] at h
      by_cases hx : T.dom x = .zero
      · rw [if_pos hx] at h
        cases h
      · rw [if_neg hx] at h
        cases h
        exact hx

theorem T.dom_zero_eq_Z {lam : Nat}
    (s : T lam) (h : T.dom s = .zero) :
    s = T.Z := by
  cases s with
  | Z =>
    rfl
  | P ls add =>
    rw [T.dom] at h
    by_cases hadd : add = T.Z
    · rw [ite_eq_left hadd] at h
      cases hmin : T.domVecMinIdx ls with
      | none =>
        rw [hmin] at h
        cases h
      | some p =>
        cases p with
        | mk m d =>
          rw [hmin] at h
          change
            (if d = .one then
              if m.val = 0 then .omega else .Omega
            else .omega) = .zero at h
          by_cases hd1 : d = .one
          · rw [ite_eq_left hd1] at h
            by_cases hm0 : m.val = 0
            · rw [ite_eq_left hm0] at h
              cases h
            · rw [ite_eq_right hm0] at h
              cases h
          · rw [ite_eq_right hd1] at h
            cases h
    · rw [ite_eq_right hadd] at h
      have hz : add = T.Z :=
        T.dom_zero_eq_Z add h
      exact False.elim (hadd hz)
termination_by T.size s
decreasing_by
  change T.size add < T.size (T.P ls add)
  exact T.add_size_lt_P ls add

theorem T.Z_le {lam : Nat} (s : T lam) : T.Z ≤ s := by
  cases s with
  | Z =>
    exact Or.inr rfl
  | P ls add =>
    exact Or.inl rfl

theorem Vec.rplc_idx_same {A : Type} {n : Nat}
    (v : Vec A n) (i : Fin n) (a : A) :
    (v.rplc i a).idx i = a := by
  rw [Vec.rplc, Vec.ofFn_idx]
  rw [ite_eq_left rfl]

theorem Vec.rplc_idx_of_ne {A : Type} {n : Nat}
    (v : Vec A n) (i j : Fin n) (a : A)
    (hij : j ≠ i) :
    (v.rplc i a).idx j = v.idx j := by
  rw [Vec.rplc, Vec.ofFn_idx]
  have hval : j.val ≠ i.val := by
    intro h
    apply hij
    exact Fin.eq_of_val_eq h
  rw [ite_eq_right hval]
  exact Vec.getElem_eq_idx v j

theorem Vec.idx_mem_toList {A : Type} {n : Nat}
    (v : Vec A n) (i : Fin n) :
    v.idx i ∈ Vec.toList v := by
  induction v with
  | nil =>
    exact i.elim0
  | snoc k xs x ih =>
    by_cases h : i.val < k
    · change
        (if h' : i.val < k then
          Vec.idx xs ⟨i.val, h'⟩
        else x) ∈ Vec.toList xs ++ [x]
      rw [dite_eq_left h]
      exact List.mem_append_left [x] (ih ⟨i.val, h⟩)
    · change
        (if h' : i.val < k then
          Vec.idx xs ⟨i.val, h'⟩
        else x) ∈ Vec.toList xs ++ [x]
      rw [dite_eq_right h]
      exact List.mem_append_right (Vec.toList xs)
        (List.mem_singleton_self x)

theorem T.isNFComp_Z {lam : Nat} :
    T.isNFComp (T.Z : T lam) := by
  constructor
  · exact T.isNF.z
  · intro y hy
    change y ∈ ([] : List (T lam)) at hy
    exact False.elim (List.not_mem_nil hy)

theorem T.isNF_P_coord_NFComp {lam : Nat}
    (ls : Vec (T lam) lam) (add : T lam)
    (h : T.isNF (T.P ls add)) :
    ∀ i : Fin lam, T.isNFComp (ls.idx i) := by
  cases h with
  | p _ _ h0 h1 h2 h3 =>
    intro i
    have hmem : ls.idx i ∈ Vec.toList ls :=
      Vec.idx_mem_toList ls i
    constructor
    · exact h0 (ls.idx i) hmem
    · exact h2 (ls.idx i) hmem

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
