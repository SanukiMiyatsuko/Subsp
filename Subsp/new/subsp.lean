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

def T.LF {lam : Nat} : Nat → T lam
| 0 => Z
| n + 1 =>
  match lam with
  | 0 => P Vec.nil Z
  | lam' + 1 =>
    P (Vec.ofFn (lam' + 1) (fun i => if i = lam' then LF n else Z)) Z

inductive T.isOT (lam : Nat) : T lam → Prop where
| base (n : Nat) : isOT lam (LF n)
| step (s : T lam) (hs : isOT lam s) (n : Nat) : isOT lam (fund s (ofNat n))

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

instance {lam : Nat} (s : T lam) : Decidable (T.isNF s) := sorry

end new
