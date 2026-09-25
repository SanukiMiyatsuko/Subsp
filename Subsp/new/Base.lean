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
    | P ls add =>
      have step : compareT (T.P ls add) (T.P ls add)
          = (match compareVec ls ls with
              | .eq => compareT add add
              | ord => ord) := rfl
      rw [step, Vec_refl ls]
      exact T_refl add

  theorem Vec_refl {n m : Nat} (v : Vec (T n) m) : compareVec v v = Ordering.eq := by
    cases v with
    | nil => rfl
    | snoc _ xs x =>
      have step : compareVec (Vec.snoc _ xs x) (Vec.snoc _ xs x)
          = (match compareT x x with
              | .eq => compareVec xs xs
              | ord => ord) := rfl
      rw [step, T_refl x]
      exact Vec_refl xs
end

mutual
  theorem T_eq_sound {n : Nat} (x y : T n) (h : compareT x y = Ordering.eq) : x = y := by
    cases x with
    | Z =>
      cases y with
      | Z => rfl
      | P ls add => cases h
    | P ls_x add_x =>
      cases y with
      | Z => cases h
      | P ls_y add_y =>
        have step : compareT (T.P ls_x add_x) (T.P ls_y add_y)
            = (match compareVec ls_x ls_y with
                | .eq => compareT add_x add_y
                | ord => ord) := rfl
        rw [step] at h
        cases hc : compareVec ls_x ls_y with
        | lt => rw [hc] at h; cases h
        | eq =>
          have heq_ls : ls_x = ls_y := Vec_eq_sound ls_x ls_y hc
          rw [hc] at h
          have heq_add : add_x = add_y := T_eq_sound add_x add_y h
          rw [heq_ls, heq_add]
        | gt => rw [hc] at h; cases h

  theorem Vec_eq_sound {n m : Nat} (v w : Vec (T n) m)
      (h : compareVec v w = Ordering.eq) : v = w := by
    cases v with
    | nil =>
      cases w with
      | nil => rfl
    | snoc _ xs_v x_v =>
      cases w with
      | snoc _ xs_w x_w =>
        have step : compareVec (Vec.snoc _ xs_v x_v) (Vec.snoc _ xs_w x_w)
            = (match compareT x_v x_w with
                | .eq => compareVec xs_v xs_w
                | ord => ord) := rfl
        rw [step] at h
        cases hc : compareT x_v x_w with
        | lt => rw [hc] at h; cases h
        | eq =>
          have heq_x : x_v = x_w := T_eq_sound x_v x_w hc
          rw [hc] at h
          have heq_xs : xs_v = xs_w := Vec_eq_sound xs_v xs_w h
          rw [heq_x, heq_xs]
        | gt => rw [hc] at h; cases h
end

mutual
  theorem T_trans {n : Nat} (x y z : T n)
      (h1 : compareT x y = Ordering.lt) (h2 : compareT y z = Ordering.lt) :
      compareT x z = Ordering.lt := by
    cases x with
    | Z =>
      cases y with
      | Z => cases h1
      | P ls_y add_y =>
        cases z with
        | Z => cases h2
        | P ls_z add_z => rfl
    | P ls_x add_x =>
      cases y with
      | Z => cases h1
      | P ls_y add_y =>
        cases z with
        | Z => cases h2
        | P ls_z add_z =>
          have step12 : compareT (T.P ls_x add_x) (T.P ls_y add_y)
              = (match compareVec ls_x ls_y with
                  | .eq => compareT add_x add_y
                  | ord => ord) := rfl
          have step23 : compareT (T.P ls_y add_y) (T.P ls_z add_z)
              = (match compareVec ls_y ls_z with
                  | .eq => compareT add_y add_z
                  | ord => ord) := rfl
          have step13 : compareT (T.P ls_x add_x) (T.P ls_z add_z)
              = (match compareVec ls_x ls_z with
                  | .eq => compareT add_x add_z
                  | ord => ord) := rfl
          rw [step12] at h1
          rw [step23] at h2
          rw [step13]
          cases hc12 : compareVec ls_x ls_y with
          | lt =>
            cases hc23 : compareVec ls_y ls_z with
            | lt =>
              have hv13 : compareVec ls_x ls_z = Ordering.lt :=
                Vec_trans ls_x ls_y ls_z hc12 hc23
              rw [hv13]
            | eq =>
              have heq23 : ls_y = ls_z := Vec_eq_sound ls_y ls_z hc23
              have hv13 : compareVec ls_x ls_z = Ordering.lt := by
                rw [← heq23]; exact hc12
              rw [hv13]
            | gt => rw [hc23] at h2; cases h2
          | eq =>
            have heq12 : ls_x = ls_y := Vec_eq_sound ls_x ls_y hc12
            cases hc23 : compareVec ls_y ls_z with
            | lt =>
              have hv13 : compareVec ls_x ls_z = Ordering.lt := by
                rw [heq12]; exact hc23
              rw [hv13]
            | eq =>
              have heq23 : ls_y = ls_z := Vec_eq_sound ls_y ls_z hc23
              have hls13 : ls_x = ls_z := heq12.trans heq23
              have hv13 : compareVec ls_x ls_z = Ordering.eq := by
                rw [hls13]; exact Vec_refl ls_z
              rw [hv13]
              rw [hc12] at h1
              rw [hc23] at h2
              exact T_trans add_x add_y add_z h1 h2
            | gt => rw [hc23] at h2; cases h2
          | gt => rw [hc12] at h1; cases h1

  theorem Vec_trans {n m : Nat} (u v w : Vec (T n) m)
      (h1 : compareVec u v = Ordering.lt) (h2 : compareVec v w = Ordering.lt) :
      compareVec u w = Ordering.lt := by
    cases u with
    | nil =>
      cases v with
      | nil =>
        cases w with
        | nil => cases h1
    | snoc _ xs_u x_u =>
      cases v with
      | snoc _ xs_v x_v =>
        cases w with
        | snoc _ xs_w x_w =>
          have step12 : compareVec (Vec.snoc _ xs_u x_u) (Vec.snoc _ xs_v x_v)
              = (match compareT x_u x_v with
                  | .eq => compareVec xs_u xs_v
                  | ord => ord) := rfl
          have step23 : compareVec (Vec.snoc _ xs_v x_v) (Vec.snoc _ xs_w x_w)
              = (match compareT x_v x_w with
                  | .eq => compareVec xs_v xs_w
                  | ord => ord) := rfl
          have step13 : compareVec (Vec.snoc _ xs_u x_u) (Vec.snoc _ xs_w x_w)
              = (match compareT x_u x_w with
                  | .eq => compareVec xs_u xs_w
                  | ord => ord) := rfl
          rw [step12] at h1
          rw [step23] at h2
          rw [step13]
          cases hc12 : compareT x_u x_v with
          | lt =>
            cases hc23 : compareT x_v x_w with
            | lt =>
              have ht13 : compareT x_u x_w = Ordering.lt :=
                T_trans x_u x_v x_w hc12 hc23
              rw [ht13]
            | eq =>
              have heq23 : x_v = x_w := T_eq_sound x_v x_w hc23
              have ht13 : compareT x_u x_w = Ordering.lt := by
                rw [← heq23]; exact hc12
              rw [ht13]
            | gt => rw [hc23] at h2; cases h2
          | eq =>
            have heq12 : x_u = x_v := T_eq_sound x_u x_v hc12
            cases hc23 : compareT x_v x_w with
            | lt =>
              have ht13 : compareT x_u x_w = Ordering.lt := by
                rw [heq12]; exact hc23
              rw [ht13]
            | eq =>
              have heq23 : x_v = x_w := T_eq_sound x_v x_w hc23
              have hx13 : x_u = x_w := heq12.trans heq23
              have ht13 : compareT x_u x_w = Ordering.eq := by
                rw [hx13]; exact T_refl x_w
              rw [ht13]
              rw [hc12] at h1
              rw [hc23] at h2
              exact Vec_trans xs_u xs_v xs_w h1 h2
            | gt => rw [hc23] at h2; cases h2
          | gt => rw [hc12] at h1; cases h1
end

mutual
  theorem T_total {n : Nat} (x y : T n) :
      compareT x y = Ordering.lt ∨ compareT y x = Ordering.lt ∨ x = y := by
    cases x with
    | Z =>
      cases y with
      | Z => exact Or.inr (Or.inr rfl)
      | P ls add => exact Or.inl rfl
    | P ls_x add_x =>
      cases y with
      | Z => exact Or.inr (Or.inl rfl)
      | P ls_y add_y =>
        have stepXY : compareT (T.P ls_x add_x) (T.P ls_y add_y)
            = (match compareVec ls_x ls_y with
                | .eq => compareT add_x add_y
                | ord => ord) := rfl
        have stepYX : compareT (T.P ls_y add_y) (T.P ls_x add_x)
            = (match compareVec ls_y ls_x with
                | .eq => compareT add_y add_x
                | ord => ord) := rfl
        cases Vec_total ls_x ls_y with
        | inl hvlt =>
          apply Or.inl
          rw [stepXY, hvlt]
        | inr hv =>
          cases hv with
          | inl hvlt =>
            apply Or.inr; apply Or.inl
            rw [stepYX, hvlt]
          | inr hveq =>
            have hvxy : compareVec ls_x ls_y = Ordering.eq := by
              rw [hveq]; exact Vec_refl ls_y
            have hvyx : compareVec ls_y ls_x = Ordering.eq := by
              rw [hveq]; exact Vec_refl ls_y
            cases T_total add_x add_y with
            | inl htlt =>
              apply Or.inl
              rw [stepXY, hvxy]
              exact htlt
            | inr ht =>
              cases ht with
              | inl htlt =>
                apply Or.inr; apply Or.inl
                rw [stepYX, hvyx]
                exact htlt
              | inr hteq =>
                apply Or.inr; apply Or.inr
                rw [hveq, hteq]

  theorem Vec_total {n m : Nat} (v w : Vec (T n) m) :
      compareVec v w = Ordering.lt ∨ compareVec w v = Ordering.lt ∨ v = w := by
    cases v with
    | nil =>
      cases w with
      | nil => exact Or.inr (Or.inr rfl)
    | snoc _ xs_v x_v =>
      cases w with
      | snoc _ xs_w x_w =>
        have stepVW : compareVec (Vec.snoc _ xs_v x_v) (Vec.snoc _ xs_w x_w)
            = (match compareT x_v x_w with
                | .eq => compareVec xs_v xs_w
                | ord => ord) := rfl
        have stepWV : compareVec (Vec.snoc _ xs_w x_w) (Vec.snoc _ xs_v x_v)
            = (match compareT x_w x_v with
                | .eq => compareVec xs_w xs_v
                | ord => ord) := rfl
        cases T_total x_v x_w with
        | inl htlt =>
          apply Or.inl
          rw [stepVW, htlt]
        | inr ht =>
          cases ht with
          | inl htlt =>
            apply Or.inr; apply Or.inl
            rw [stepWV, htlt]
          | inr hteq =>
            have htvw : compareT x_v x_w = Ordering.eq := by
              rw [hteq]; exact T_refl x_w
            have htwv : compareT x_w x_v = Ordering.eq := by
              rw [hteq]; exact T_refl x_w
            cases Vec_total xs_v xs_w with
            | inl hvlt =>
              apply Or.inl
              rw [stepVW, htvw]
              exact hvlt
            | inr hv =>
              cases hv with
              | inl hvlt =>
                apply Or.inr; apply Or.inl
                rw [stepWV, htwv]
                exact hvlt
              | inr hveq =>
                apply Or.inr; apply Or.inr
                rw [hteq, hveq]
end

instance {n : Nat} : strict_linear_order (T n) where
  irrefl x h := by
    have h' : compareT x x = Ordering.lt := h
    have he : compareT x x = Ordering.eq := T_refl x
    rw [he] at h'
    cases h'
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
    show (Vec.snoc k (Vec.ofFn k (fun j => f j.castSucc)) (f (Fin.last k))).idx i = f i
    show (if h : i.val < k then Vec.idx (Vec.ofFn k (fun j => f j.castSucc)) ⟨i.val, h⟩
          else f (Fin.last k)) = f i
    apply Decidable.byCases (p := i.val < k)
    · intro h
      rw [dite_eq_left h]
      have heq : (⟨i.val, h⟩ : Fin k).castSucc = i := by
        apply Fin.eq_of_val_eq
        rfl
      rw [ih (fun j => f j.castSucc) ⟨i.val, h⟩]
      show f ((⟨i.val, h⟩ : Fin k).castSucc) = f i
      rw [heq]
    · intro h
      rw [dite_eq_right h]
      have hik : i.val ≤ k := Nat.lt_succ_iff.mp i.isLt
      have hge : k ≤ i.val := Nat.not_lt.mp h
      have hval : i.val = k := Nat.le_antisymm hik hge
      have : i = Fin.last k := by
        apply Fin.eq_of_val_eq
        exact hval
      rw [this]

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

end new
