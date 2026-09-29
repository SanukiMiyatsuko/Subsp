import Subsp.order

namespace new

inductive Vec (A : Type) : Nat → Type where
| nil : Vec A 0
| snoc (n : Nat) : Vec A n → A → Vec A (n + 1)

inductive T (n : Nat) where
| Z : T n
| P (ls : Vec (T n) n) (add : T n) : T n

mutual
  def decEqT {n : Nat} : (x y : T n) → Decidable (x = y)
    | .Z, .Z => isTrue rfl
    | .Z, .P _ _ => isFalse (fun h => by cases h)
    | .P _ _, .Z => isFalse (fun h => by cases h)
    | .P ls₁ add₁, .P ls₂ add₂ =>
      match decEqVec ls₁ ls₂ with
      | isTrue h₁ =>
        match decEqT add₁ add₂ with
        | isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
        | isFalse h₂ => isFalse (fun h => by cases h; exact h₂ rfl)
      | isFalse h₁ => isFalse (fun h => by cases h; exact h₁ rfl)

  def decEqVec {n m : Nat} : (v₁ v₂ : Vec (T n) m) → Decidable (v₁ = v₂)
    | .nil, .nil => isTrue rfl
    | .snoc _ xs x, .snoc _ ys y =>
      match decEqT x y with
      | isTrue h₁ =>
        match decEqVec xs ys with
        | isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
        | isFalse h₂ => isFalse (fun h => by cases h; exact h₂ rfl)
      | isFalse h₁ => isFalse (fun h => by cases h; exact h₁ rfl)
end

instance {n : Nat} : DecidableEq (Vec (T n) n) := decEqVec
instance {n : Nat} : DecidableEq (T n) := decEqT

def Vec.idx {A : Type} {n : Nat} : Vec A n → Fin n → A
| nil, i => i.elim0
| snoc m xs x, i =>
  if h : i.val < m then
    Vec.idx xs ⟨i.val, h⟩
  else
    x

instance {A : Type} {n : Nat} : GetElem (Vec A n) Nat A (fun _ i => i < n) where
  getElem v i h := v.idx ⟨i, h⟩

mutual
  def compareT {n : Nat} : T n → T n → Ordering
    | .Z, .Z => .eq
    | .Z, .P _ _ => .lt
    | .P _ _, .Z => .gt
    | .P ls₁ add₁, .P ls₂ add₂ =>
      match compareVec ls₁ ls₂ with
      | .eq => compareT add₁ add₂
      | ord => ord

  def compareVec {n m : Nat} : Vec (T n) m → Vec (T n) m → Ordering
    | .nil, .nil => .eq
    | .snoc _ xs₁ x₁, .snoc _ xs₂ x₂ =>
      match compareT x₁ x₂ with
      | .eq => compareVec xs₁ xs₂
      | ord => ord
end

instance {n : Nat} : Ord (T n) := ⟨compareT⟩

def T.lt {n : Nat} (x y : T n) : Prop := compareT x y = .lt
def T.le {n : Nat} (x y : T n) : Prop := compareT x y = .lt ∨ compareT x y = .eq

instance {n : Nat} : LT (T n) := ⟨T.lt⟩
instance {n : Nat} : LE (T n) := ⟨T.le⟩

instance {n : Nat} (x y : T n) : Decidable (T.lt x y) :=
  inferInstanceAs (Decidable (compareT x y = .lt))

instance {n : Nat} (x y : T n) : Decidable (T.le x y) :=
  inferInstanceAs (Decidable (compareT x y = .lt ∨ compareT x y = .eq))

mutual
  theorem T_refl {n : Nat} (x : T n) : compareT x x = Ordering.eq := by
    cases x with
    | Z => rfl
    | P ls add => simp only [compareT, Vec_refl ls, T_refl add]

  theorem Vec_refl {n m : Nat} (v : Vec (T n) m) : compareVec v v = Ordering.eq := by
    cases v with
    | nil => rfl
    | snoc _ xs x => simp only [compareVec, T_refl x, Vec_refl xs]

end

mutual
  theorem T_eq_sound {n : Nat} (x y : T n) (h : compareT x y = Ordering.eq) : x = y := by
    cases x with
    | Z => cases y <;> first | rfl | cases h
    | P vx ax =>
      cases y with
      | Z => cases h
      | P vy ay =>
        simp only [compareT] at h
        cases hc : compareVec vx vy with
        | lt | gt => simp [hc] at h
        | eq =>
            have hv := Vec_eq_sound vx vy hc
            have ha := T_eq_sound ax ay (by simpa [hc] using h)
            cases hv; cases ha; rfl

  theorem Vec_eq_sound {n m : Nat} (v w : Vec (T n) m)
      (h : compareVec v w = Ordering.eq) : v = w := by
    cases v with
    | nil => cases w; rfl
    | snoc k xs x =>
      cases w with
      | snoc _ ys y =>
        simp only [compareVec] at h
        cases hc : compareT x y with
        | lt | gt => simp [hc] at h
        | eq =>
            have hv := Vec_eq_sound xs ys (by simpa [hc] using h)
            have hx := T_eq_sound x y hc
            cases hv; cases hx; rfl

end

mutual
  theorem T_trans {n : Nat} (x y z : T n)
      (h1 : compareT x y = Ordering.lt) (h2 : compareT y z = Ordering.lt) :
      compareT x z = Ordering.lt := by
    cases x with
    | Z => cases y <;> cases z <;> simp_all [compareT]
    | P vx ax =>
      cases y with
      | Z => cases h1
      | P vy ay =>
        cases z with
        | Z => cases h2
        | P vz az =>
          simp only [compareT] at h1 h2 ⊢
          cases hxy : compareVec vx vy with
          | gt => simp [hxy] at h1
          | lt =>
            cases hyz : compareVec vy vz with
            | gt => simp [hyz] at h2
            | lt => simp only [Vec_trans vx vy vz hxy hyz]
            | eq => simp only [← Vec_eq_sound vy vz hyz, hxy]
          | eq =>
            cases Vec_eq_sound vx vy hxy
            simp only [Vec_refl] at h1
            cases hyz : compareVec vx vz with
            | gt => simp [hyz] at h2
            | lt => rfl
            | eq => exact T_trans ax ay az h1 (by simpa [hyz] using h2)

  theorem Vec_trans {n m : Nat} (u v w : Vec (T n) m)
      (h1 : compareVec u v = Ordering.lt) (h2 : compareVec v w = Ordering.lt) :
      compareVec u w = Ordering.lt := by
    cases u with
    | nil => cases v; cases w; cases h1
    | snoc k xs x =>
      cases v with
      | snoc _ ys y =>
        cases w with
        | snoc _ zs z =>
          simp only [compareVec] at h1 h2 ⊢
          cases hxy : compareT x y with
          | gt => simp [hxy] at h1
          | lt =>
            cases hyz : compareT y z with
            | gt => simp [hyz] at h2
            | lt => simp only [T_trans x y z hxy hyz]
            | eq => simp only [← T_eq_sound y z hyz, hxy]
          | eq =>
            cases T_eq_sound x y hxy
            simp only [T_refl] at h1
            cases hyz : compareT x z with
            | gt => simp [hyz] at h2
            | lt => rfl
            | eq => exact Vec_trans xs ys zs h1 (by simpa [hyz] using h2)

end

mutual
  theorem T_total {n : Nat} (x y : T n) :
      compareT x y = Ordering.lt ∨ compareT y x = Ordering.lt ∨ x = y := by
    cases x with
    | Z => cases y <;> simp [compareT]
    | P vx ax =>
      cases y with
      | Z => exact Or.inr (Or.inl rfl)
      | P vy ay =>
        rcases Vec_total vx vy with h | h | h
        · exact Or.inl (by simp [compareT, h])
        · exact Or.inr (Or.inl (by simp [compareT, h]))
        · cases h
          simpa [compareT, Vec_refl] using T_total ax ay

  theorem Vec_total {n m : Nat} (v w : Vec (T n) m) :
      compareVec v w = Ordering.lt ∨ compareVec w v = Ordering.lt ∨ v = w := by
    cases v with
    | nil => cases w; exact Or.inr (Or.inr rfl)
    | snoc k xs x =>
      cases w with
      | snoc _ ys y =>
        rcases T_total x y with h | h | h
        · exact Or.inl (by simp [compareVec, h])
        · exact Or.inr (Or.inl (by simp [compareVec, h]))
        · cases h
          simpa [compareVec, T_refl] using Vec_total xs ys

end

instance {n : Nat} : strict_linear_order (T n) where
  irrefl x h := by simp [LT.lt, T.lt, T_refl] at h
  trans x y z h1 h2 := T_trans x y z h1 h2
  total x y := T_total x y

def Vec.ofFn {A : Type} : (k : Nat) → (Fin k → A) → Vec A k
  | 0, _ => .nil
  | k + 1, f => Vec.snoc k (Vec.ofFn k (fun i => f i.castSucc)) (f (Fin.last k))

theorem Vec.ofFn_idx {A : Type} : ∀ (k : Nat) (f : Fin k → A) (i : Fin k),
    (Vec.ofFn k f).idx i = f i := by
  intro k
  induction k with
  | zero => intro f i; exact i.elim0
  | succ k ih =>
      intro f i
      simp only [Vec.ofFn, Vec.idx]
      split
      · exact ih _ _
      · congr 1
        apply Fin.eq_of_val_eq
        simp only [Fin.val_last]
        omega

def Vec.rplc {A : Type} {n : Nat} (v : Vec A n) (i : Fin n) (a : A) : Vec A n :=
  Vec.ofFn n (fun j =>
    if j.val = i.val then a
    else v[j])

def Vec.toList {A : Type} {n : Nat} : Vec A n → List A
| nil => []
| snoc _ v a => toList v ++ [a]

def T.oplus {lam : Nat} : T lam → T lam → T lam
| .Z, t => t
| .P ls add, t => .P ls (oplus add t)

instance {lam : Nat} : Add (T lam) where
  add := T.oplus

def T.mul {lam : Nat} (s : T lam) : T lam → T lam
| Z => Z
| P _ add => s + mul s add

def T.iter {lam : Nat} (F : T lam → T lam) : T lam → T lam
| Z => Z
| P _ add => F (iter F add)

def T.ofNat {lam : Nat} : Nat → T lam
| 0 => Z
| n + 1 => P (Vec.ofFn lam (fun _ => Z)) (ofNat n)

def T.head {lam : Nat} : T lam → T lam
| Z => Z
| P ls _ => P ls Z

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

end new
