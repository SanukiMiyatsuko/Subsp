import Subsp.Buchholz.Base

open T

inductive Dom1 where
| Zero
| One
| ω
| Ω (l : Nat)
deriving DecidableEq

def T.dom1 : T → Dom1
| Z => .Zero
| P s0 s1 s2 =>
  if s2 = Z then
    match T.dom1 s1 with
    | .Zero =>
      match s0 with
      | 0 => .One
      | l + 1 => .Ω l
    | .One => .ω
    | .ω => .ω
    | .Ω l =>
      if s0 ≤ l then
        .ω
      else .Ω l
  else T.dom1 s2

theorem dom1_P0_of_Zero (s1 : T) (h : T.dom1 s1 = Dom1.Zero) : T.dom1 (P 0 s1 Z) = Dom1.One := by
  rw [T.dom1.eq_2, h]
  rfl

theorem dom1_P0_of_One (s1 : T) (h : T.dom1 s1 = Dom1.One) : T.dom1 (P 0 s1 Z) = Dom1.ω := by
  rw [T.dom1.eq_2, h]
  rfl

theorem dom1_P0_of_ω (s1 : T) (h : T.dom1 s1 = Dom1.ω) : T.dom1 (P 0 s1 Z) = Dom1.ω := by
  rw [T.dom1.eq_2, h]
  rfl

theorem dom1_P0_of_Ω (s1 : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) : T.dom1 (P 0 s1 Z) = Dom1.ω := by
  rw [T.dom1.eq_2, h]
  show (if (0:Nat) ≤ l then Dom1.ω else Dom1.Ω l) = Dom1.ω
  rw [ite_eq_left (Nat.zero_le l)]

theorem dom1_Psucc_of_Zero (l0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.Zero) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.Ω l0 := by
  rw [T.dom1.eq_3, h]
  rfl

theorem dom1_Psucc_of_One (l0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.One) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.ω := by
  rw [T.dom1.eq_3, h]
  rfl

theorem dom1_Psucc_of_ω (l0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.ω) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.ω := by
  rw [T.dom1.eq_3, h]
  rfl

theorem dom1_Psucc_of_Ω_le (l0 l1 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.Ω l1) (hle : l0+1 ≤ l1) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.ω := by
  rw [T.dom1.eq_3, h]
  show (if l0+1 ≤ l1 then Dom1.ω else Dom1.Ω l1) = Dom1.ω
  rw [ite_eq_left hle]

theorem dom1_Psucc_of_Ω_gt (l0 l1 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.Ω l1) (hgt : ¬ (l0+1 ≤ l1)) :
    T.dom1 (P (l0+1) s1 Z) = Dom1.Ω l1 := by
  rw [T.dom1.eq_3, h]
  show (if l0+1 ≤ l1 then Dom1.ω else Dom1.Ω l1) = Dom1.Ω l1
  rw [ite_eq_right hgt]

theorem dom1_P_tail (s0 : Nat) (s1 : T) (s20 : Nat) (s21 s22 : T) :
    T.dom1 (P s0 s1 (P s20 s21 s22)) = T.dom1 (P s20 s21 s22) :=
  ((fun a => a) ∘ fun a => a) rfl

theorem dom1_P_of_One (s0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.One) : T.dom1 (P s0 s1 Z) = Dom1.ω := by
  cases s0 with
  | zero => exact dom1_P0_of_One s1 h
  | succ l0 => exact dom1_Psucc_of_One l0 s1 h

theorem dom1_P_of_ω (s0 : Nat) (s1 : T) (h : T.dom1 s1 = Dom1.ω) : T.dom1 (P s0 s1 Z) = Dom1.ω := by
  cases s0 with
  | zero => exact dom1_P0_of_ω s1 h
  | succ l0 => exact dom1_Psucc_of_ω l0 s1 h

theorem dom1_P_of_Ω (s0 : Nat) (s1 : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) :
    T.dom1 (P s0 s1 Z) = if s0 ≤ l then Dom1.ω else Dom1.Ω l := by
  cases s0 with
  | zero =>
    rw [dom1_P0_of_Ω s1 l h]
    rw [ite_eq_left (Nat.zero_le l)]
  | succ l0 =>
    apply Decidable.byCases (p := l0+1 ≤ l)
    · intro hle
      rw [dom1_Psucc_of_Ω_le l0 l s1 h hle, ite_eq_left hle]
    · intro hle
      rw [dom1_Psucc_of_Ω_gt l0 l s1 h hle, ite_eq_right hle]

theorem dom1_ne_Zero_of_P (s0 : Nat) (s1 s2 : T) : T.dom1 (P s0 s1 s2) ≠ Dom1.Zero := by
  induction s2 generalizing s0 s1 with
  | Z =>
    cases s0 with
    | zero =>
      cases hd : T.dom1 s1 with
      | Zero => rw [T.dom1.eq_2, hd]; intro h; cases h
      | One => rw [T.dom1.eq_2, hd]; intro h; cases h
      | ω => rw [T.dom1.eq_2, hd]; intro h; cases h
      | Ω l =>
        rw [T.dom1.eq_2, hd]
        show (if (0:Nat) ≤ l then Dom1.ω else Dom1.Ω l) ≠ Dom1.Zero
        split
        · intro h; cases h
        · intro h; cases h
    | succ l =>
      cases hd : T.dom1 s1 with
      | Zero => rw [T.dom1.eq_3, hd]; intro h; cases h
      | One => rw [T.dom1.eq_3, hd]; intro h; cases h
      | ω => rw [T.dom1.eq_3, hd]; intro h; cases h
      | Ω l' =>
        rw [T.dom1.eq_3, hd]
        show (if l+1 ≤ l' then Dom1.ω else Dom1.Ω l') ≠ Dom1.Zero
        split
        · intro h; cases h
        · intro h; cases h
  | P s20 s21 s22 ih1 ih2 =>
    intro h
    rw [dom1_P_tail s0 s1 s20 s21 s22] at h
    exact ih2 s20 s21 h

theorem dom1_Zero_imp_eq_Z (x : T) (h : T.dom1 x = Dom1.Zero) : x = Z := by
  cases x with
  | Z => rfl
  | P x0 x1 x2 => exact absurd h (dom1_ne_Zero_of_P x0 x1 x2)

def T.fund1 (s t : T) : T :=
  match s with
  | Z => Z
  | P s0 s1 s2 =>
    if s2 = Z then
      match _h1 : T.dom1 s1 with
      | .Zero =>
        match s0 with
        | 0 => Z
        | _ + 1 => t
      | .One => T.mul (P s0 (T.fund1 s1 Z) Z) t
      | .ω => P s0 (T.fund1 s1 t) Z
      | .Ω l =>
        if s0 ≤ l then
          let F := fun x => P l (T.fund1 s1 x) Z
          P s0 (T.fund1 s1 (T.iter F t)) Z
        else P s0 (T.fund1 s1 t) Z
    else P s0 s1 (T.fund1 s2 t)

theorem fund1_P0_of_Zero (s1 t : T) (h : T.dom1 s1 = Dom1.Zero) :
    T.fund1 (P 0 s1 Z) t = Z := by
  rw [T.fund1.eq_2, h]
  rfl

theorem fund1_P0_of_One (s1 t : T) (h : T.dom1 s1 = Dom1.One) :
    T.fund1 (P 0 s1 Z) t = T.mul (P 0 (T.fund1 s1 Z) Z) t := by
  rw [T.fund1.eq_2, h]
  rfl

theorem fund1_P0_of_ω (s1 t : T) (h : T.dom1 s1 = Dom1.ω) :
    T.fund1 (P 0 s1 Z) t = P 0 (T.fund1 s1 t) Z := by
  rw [T.fund1.eq_2, h]
  rfl

theorem fund1_P0_of_Ω (s1 t : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) :
    T.fund1 (P 0 s1 Z) t = P 0 (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t)) Z := by
  rw [T.fund1.eq_2, h]
  show (if (0:Nat) ≤ l then
          (let F := fun x => P l (T.fund1 s1 x) Z; P 0 (T.fund1 s1 (T.iter F t)) Z)
        else P 0 (T.fund1 s1 t) Z) = P 0 (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t)) Z
  rw [ite_eq_left (Nat.zero_le l)]

theorem fund1_Psucc_of_Zero (l0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.Zero) :
    T.fund1 (P (l0+1) s1 Z) t = t := by
  rw [T.fund1.eq_3, h]
  rfl

theorem fund1_Psucc_of_One (l0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.One) :
    T.fund1 (P (l0+1) s1 Z) t = T.mul (P (l0+1) (T.fund1 s1 Z) Z) t := by
  rw [T.fund1.eq_3, h]
  rfl

theorem fund1_Psucc_of_ω (l0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.ω) :
    T.fund1 (P (l0+1) s1 Z) t = P (l0+1) (T.fund1 s1 t) Z := by
  rw [T.fund1.eq_3, h]
  rfl

theorem fund1_Psucc_of_Ω_le (l0 l1 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.Ω l1) (hle : l0+1 ≤ l1) :
    T.fund1 (P (l0+1) s1 Z) t = P (l0+1) (T.fund1 s1 (T.iter (fun x => P l1 (T.fund1 s1 x) Z) t)) Z := by
  rw [T.fund1.eq_3, h]
  show (if l0+1 ≤ l1 then
          (let F := fun x => P l1 (T.fund1 s1 x) Z; P (l0+1) (T.fund1 s1 (T.iter F t)) Z)
        else P (l0+1) (T.fund1 s1 t) Z) = P (l0+1) (T.fund1 s1 (T.iter (fun x => P l1 (T.fund1 s1 x) Z) t)) Z
  rw [ite_eq_left hle]

theorem fund1_Psucc_of_Ω_gt (l0 l1 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.Ω l1) (hgt : ¬ (l0+1 ≤ l1)) :
    T.fund1 (P (l0+1) s1 Z) t = P (l0+1) (T.fund1 s1 t) Z := by
  rw [T.fund1.eq_3, h]
  show (if l0+1 ≤ l1 then
          (let F := fun x => P l1 (T.fund1 s1 x) Z; P (l0+1) (T.fund1 s1 (T.iter F t)) Z)
        else P (l0+1) (T.fund1 s1 t) Z) = P (l0+1) (T.fund1 s1 t) Z
  rw [ite_eq_right hgt]

theorem fund1_P_tail (s0 : Nat) (s1 : T) (t : T) (s20 : Nat) (s21 s22 : T) :
    T.fund1 (P s0 s1 (P s20 s21 s22)) t = P s0 s1 (T.fund1 (P s20 s21 s22) t) :=
  (congrArg (P s0 s1 (P s20 s21 s22)).fund1 ∘ fun a => a) rfl

theorem fund1_P_of_One (s0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.One) :
    T.fund1 (P s0 s1 Z) t = T.mul (P s0 (T.fund1 s1 Z) Z) t := by
  cases s0 with
  | zero => exact fund1_P0_of_One s1 t h
  | succ l0 => exact fund1_Psucc_of_One l0 s1 t h

theorem fund1_P_of_ω (s0 : Nat) (s1 t : T) (h : T.dom1 s1 = Dom1.ω) :
    T.fund1 (P s0 s1 Z) t = P s0 (T.fund1 s1 t) Z := by
  cases s0 with
  | zero => exact fund1_P0_of_ω s1 t h
  | succ l0 => exact fund1_Psucc_of_ω l0 s1 t h

theorem fund1_P_of_Ω_le (s0 : Nat) (s1 t : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) (hle : s0 ≤ l) :
    T.fund1 (P s0 s1 Z) t = P s0 (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t)) Z := by
  cases s0 with
  | zero => exact fund1_P0_of_Ω s1 t l h
  | succ l0 => exact fund1_Psucc_of_Ω_le l0 l s1 t h hle

theorem fund1_P_of_Ω_gt (s0 : Nat) (s1 t : T) (l : Nat) (h : T.dom1 s1 = Dom1.Ω l) (hgt : ¬ s0 ≤ l) :
    T.fund1 (P s0 s1 Z) t = P s0 (T.fund1 s1 t) Z := by
  cases s0 with
  | zero => exact absurd (Nat.zero_le l) hgt
  | succ l0 => exact fund1_Psucc_of_Ω_gt l0 l s1 t h hgt

inductive T.index_Prop1 (v : Nat) : T → Prop where
| z : T.index_Prop1 v Z
| p (s0 : Nat) (s1 s2 : T) : s0 ≤ v → T.index_Prop1 v s2 → T.index_Prop1 v (P s0 s1 s2)

theorem index_Prop1_lt_succ (l : Nat) (t : T) (h : T.index_Prop1 l t) :
    t < P (l+1) Z Z := by
  cases h with
  | z => exact T.Lt.Z_lt_P (l+1) Z Z
  | p s0' s1' s2' hle hrec =>
    have hlt : s0' < l + 1 := Nat.lt_succ_of_le hle
    exact T.Lt.p_head s0' (l+1) s1' Z s2' Z hlt

theorem iter_index_Prop1 (l : Nat) (g : T → T) (hg : ∀ x, ∃ y, g x = P l y Z) (t : T) :
    T.index_Prop1 l (T.iter g t) := by
  cases t with
  | Z => rw [T.iter.eq_1]; exact T.index_Prop1.z
  | P n t0 t1 =>
    rw [T.iter.eq_2]
    obtain ⟨y, hy⟩ := hg (T.iter g t1)
    rw [hy]
    exact T.index_Prop1.p l y Z (Nat.le_refl l) T.index_Prop1.z

def T.ValidArg1 (s t : T) : Prop :=
  match T.dom1 s with
  | .Zero => False
  | .One => t = Z
  | .ω => T.IsN t
  | .Ω l => index_Prop1 l t

theorem ValidArg1_Zero_iff (s t : T) (h : T.dom1 s = Dom1.Zero) : T.ValidArg1 s t ↔ False := by
  unfold T.ValidArg1; rw [h]

theorem ValidArg1_One_iff (s t : T) (h : T.dom1 s = Dom1.One) : T.ValidArg1 s t ↔ t = Z := by
  unfold T.ValidArg1; rw [h]

theorem ValidArg1_ω_iff (s t : T) (h : T.dom1 s = Dom1.ω) : T.ValidArg1 s t ↔ T.IsN t := by
  unfold T.ValidArg1; rw [h]

theorem ValidArg1_Ω_iff (s t : T) (l : Nat) (h : T.dom1 s = Dom1.Ω l) : T.ValidArg1 s t ↔ T.index_Prop1 l t := by
  unfold T.ValidArg1; rw [h]

theorem T.ValidArg1_tail_iff (s0 : Nat) (s1 : T) (s20 : Nat) (s21 s22 t : T) :
    T.ValidArg1 (P s0 s1 (P s20 s21 s22)) t ↔ T.ValidArg1 (P s20 s21 s22) t := by
  unfold T.ValidArg1
  rw [dom1_P_tail s0 s1 s20 s21 s22]

theorem T.fund1_fall (s t : T) (hv : T.ValidArg1 s t) : T.fund1 s t < s := by
  induction s generalizing t with
  | Z =>
    exact absurd hv (fun h => (ValidArg1_Zero_iff Z t T.dom1.eq_1).mp h)
  | P s0 s1 s2 ih1 ih2 =>
    cases s2 with
    | Z =>
      cases hd : T.dom1 s1 with
      | Zero =>
        have hs1Z : s1 = Z := dom1_Zero_imp_eq_Z s1 hd
        cases s0 with
        | zero =>
          rw [fund1_P0_of_Zero s1 t hd, hs1Z]
          exact T.Lt.Z_lt_P 0 Z Z
        | succ l0 =>
          have hva : T.ValidArg1 (P (l0+1) s1 Z) t ↔ T.index_Prop1 l0 t :=
            ValidArg1_Ω_iff (P (l0+1) s1 Z) t l0 (dom1_Psucc_of_Zero l0 s1 hd)
          have hip : T.index_Prop1 l0 t := hva.mp hv
          have hlt : t < P (l0+1) Z Z := index_Prop1_lt_succ l0 t hip
          rw [fund1_Psucc_of_Zero l0 s1 t hd, hs1Z]
          exact hlt
      | One =>
        have hva : T.ValidArg1 (P s0 s1 Z) t ↔ T.IsN t :=
          ValidArg1_ω_iff (P s0 s1 Z) t (dom1_P_of_One s0 s1 hd)
        have hisn : T.IsN t := hva.mp hv
        have hva1 : T.ValidArg1 s1 Z ↔ Z = Z := ValidArg1_One_iff s1 Z hd
        have hv1 : T.ValidArg1 s1 Z := hva1.mpr rfl
        have hlt1 : T.fund1 s1 Z < s1 := ih1 Z hv1
        rw [fund1_P_of_One s0 s1 t hd]
        exact match mul_shape s0 (T.fund1 s1 Z) t hisn with
        | Or.inl hZ => by
          rw [hZ]; exact T.Lt.Z_lt_P s0 s1 Z
        | Or.inr ⟨Y, hY⟩ => by
          rw [hY]; exact T.Lt.p_mid s0 (T.fund1 s1 Z) s1 Y Z hlt1
      | ω =>
        have hva : T.ValidArg1 (P s0 s1 Z) t ↔ T.IsN t :=
          ValidArg1_ω_iff (P s0 s1 Z) t (dom1_P_of_ω s0 s1 hd)
        have hisn : T.IsN t := hva.mp hv
        have hva1 : T.ValidArg1 s1 t ↔ T.IsN t := ValidArg1_ω_iff s1 t hd
        have hv1 : T.ValidArg1 s1 t := hva1.mpr hisn
        have hlt1 : T.fund1 s1 t < s1 := ih1 t hv1
        rw [fund1_P_of_ω s0 s1 t hd]
        exact T.Lt.p_mid s0 (T.fund1 s1 t) s1 Z Z hlt1
      | Ω l =>
        apply Decidable.byCases (p := s0 ≤ l)
        · intro hle
          have hindex : T.index_Prop1 l (T.iter (fun x => P l (T.fund1 s1 x) Z) t) :=
            iter_index_Prop1 l (fun x => P l (T.fund1 s1 x) Z) (fun x => ⟨T.fund1 s1 x, rfl⟩) t
          have hva1 : T.ValidArg1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t) ↔
              T.index_Prop1 l (T.iter (fun x => P l (T.fund1 s1 x) Z) t) :=
            ValidArg1_Ω_iff s1 _ l hd
          have hv1 : T.ValidArg1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t) := hva1.mpr hindex
          have hlt1 : T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t) < s1 := ih1 _ hv1
          rw [fund1_P_of_Ω_le s0 s1 t l hd hle]
          exact T.Lt.p_mid s0 _ s1 Z Z hlt1
        · intro hle
          have hdm : T.dom1 (P s0 s1 Z) = Dom1.Ω l := by
            rw [dom1_P_of_Ω s0 s1 l hd, ite_eq_right hle]
          have hva : T.ValidArg1 (P s0 s1 Z) t ↔ T.index_Prop1 l t :=
            ValidArg1_Ω_iff (P s0 s1 Z) t l hdm
          have hip : T.index_Prop1 l t := hva.mp hv
          have hva1 : T.ValidArg1 s1 t ↔ T.index_Prop1 l t := ValidArg1_Ω_iff s1 t l hd
          have hv1 : T.ValidArg1 s1 t := hva1.mpr hip
          have hlt1 : T.fund1 s1 t < s1 := ih1 t hv1
          rw [fund1_P_of_Ω_gt s0 s1 t l hd hle]
          exact T.Lt.p_mid s0 (T.fund1 s1 t) s1 Z Z hlt1
    | P s20 s21 s22 =>
      have htail_iff : T.ValidArg1 (P s0 s1 (P s20 s21 s22)) t ↔ T.ValidArg1 (P s20 s21 s22) t := by
        unfold T.ValidArg1
        rw [dom1_P_tail s0 s1 s20 s21 s22]
      have hv2 : T.ValidArg1 (P s20 s21 s22) t := htail_iff.mp hv
      have hlt2 : T.fund1 (P s20 s21 s22) t < P s20 s21 s22 := ih2 t hv2
      rw [fund1_P_tail s0 s1 t s20 s21 s22]
      exact T.Lt.p_tail s0 s1 (T.fund1 (P s20 s21 s22) t) (P s20 s21 s22) hlt2

theorem iter_F_step_mono (s1 : T) (l : Nat) (hd : T.dom1 s1 = Dom1.Ω l)
    (mono1 : ∀ t0 t1, t0 < t1 → T.ValidArg1 s1 t0 → T.ValidArg1 s1 t1 →
      T.fund1 s1 t0 < T.fund1 s1 t1)
    (n : Nat) :
    T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n) <
      T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat (n+1)) := by
  induction n with
  | zero =>
    show T.iter (fun x => P l (T.fund1 s1 x) Z) Z <
        T.iter (fun x => P l (T.fund1 s1 x) Z) (P 0 Z Z)
    show Z < (fun x => P l (T.fund1 s1 x) Z) (T.iter (fun x => P l (T.fund1 s1 x) Z) Z)
    show Z < P l (T.fund1 s1 Z) Z
    exact T.Lt.Z_lt_P l (T.fund1 s1 Z) Z
  | succ n' ih =>
    show T.iter (fun x => P l (T.fund1 s1 x) Z) (P 0 Z (T.ofNat n')) <
        T.iter (fun x => P l (T.fund1 s1 x) Z) (P 0 Z (T.ofNat (n'+1)))
    show (fun x => P l (T.fund1 s1 x) Z) (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n')) <
        (fun x => P l (T.fund1 s1 x) Z) (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat (n'+1)))
    show P l (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n'))) Z <
        P l (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat (n'+1)))) Z
    have hindexN : T.index_Prop1 l (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n')) :=
      iter_index_Prop1 l (fun x => P l (T.fund1 s1 x) Z) (fun x => ⟨T.fund1 s1 x, rfl⟩) (T.ofNat n')
    have hindexN1 : T.index_Prop1 l (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat (n'+1))) :=
      iter_index_Prop1 l (fun x => P l (T.fund1 s1 x) Z) (fun x => ⟨T.fund1 s1 x, rfl⟩) (T.ofNat (n'+1))
    have hva0 : T.ValidArg1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n')) :=
      (ValidArg1_Ω_iff s1 _ l hd).mpr hindexN
    have hva1 : T.ValidArg1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat (n'+1))) :=
      (ValidArg1_Ω_iff s1 _ l hd).mpr hindexN1
    have hlt : T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n')) <
        T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat (n'+1))) :=
      mono1 _ _ ih hva0 hva1
    exact T.Lt.p_mid l
      (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n')))
      (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat (n'+1)))) Z Z hlt

theorem iter_F_strict_mono_ofNat (s1 : T) (l : Nat) (hd : T.dom1 s1 = Dom1.Ω l)
    (mono1 : ∀ t0 t1, t0 < t1 → T.ValidArg1 s1 t0 → T.ValidArg1 s1 t1 →
      T.fund1 s1 t0 < T.fund1 s1 t1)
    (n1 : Nat) :
    ∀ n0, n0 < n1 → T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n0) <
      T.iter (fun x => P l (T.fund1 s1 x) Z) (T.ofNat n1) := by
  induction n1 with
  | zero => intro n0 h; exact absurd h (Nat.not_lt_zero n0)
  | succ n1' ih =>
    intro n0 h
    have hle : n0 ≤ n1' := Nat.le_of_lt_succ h
    rcases Nat.lt_or_eq_of_le hle with hlt2 | heq2
    · exact lt_trans_thm _ _ _ (ih n0 hlt2) (iter_F_step_mono s1 l hd mono1 n1')
    · rw [heq2]; exact iter_F_step_mono s1 l hd mono1 n1'

theorem iter_F_strict_mono (s1 : T) (l : Nat) (hd : T.dom1 s1 = Dom1.Ω l)
    (mono1 : ∀ t0 t1, t0 < t1 → T.ValidArg1 s1 t0 → T.ValidArg1 s1 t1 →
      T.fund1 s1 t0 < T.fund1 s1 t1)
    (t0 t1 : T) (hlt : t0 < t1) (hIsN0 : T.IsN t0) (hIsN1 : T.IsN t1) :
    T.iter (fun x => P l (T.fund1 s1 x) Z) t0 < T.iter (fun x => P l (T.fund1 s1 x) Z) t1 := by
  obtain ⟨n0, hn0⟩ := IsN_exists_ofNat hIsN0
  obtain ⟨n1, hn1⟩ := IsN_exists_ofNat hIsN1
  have hnlt : n0 < n1 := by
    apply ofNat_reflect_lt
    rw [← hn0, ← hn1]
    exact hlt
  rw [hn0, hn1]
  exact iter_F_strict_mono_ofNat s1 l hd mono1 n1 n0 hnlt

theorem T.fund1_strict_mono_dec (s t0 t1 : T) (hlt : t0 < t1)
    (ht0 : T.ValidArg1 s t0) (ht1 : T.ValidArg1 s t1) :
    T.fund1 s t0 < T.fund1 s t1 := by
  induction s generalizing t0 t1 with
  | Z =>
    exact absurd ht0 (fun h => (ValidArg1_Zero_iff Z t0 T.dom1.eq_1).mp h)
  | P s0 s1 s2 ih1 ih2 =>
    cases s2 with
    | Z =>
      cases hd : T.dom1 s1 with
      | Zero =>
        cases s0 with
        | zero =>
          have hva0 : T.ValidArg1 (P 0 s1 Z) t0 ↔ t0 = Z :=
            ValidArg1_One_iff (P 0 s1 Z) t0 (dom1_P0_of_Zero s1 hd)
          have hva1 : T.ValidArg1 (P 0 s1 Z) t1 ↔ t1 = Z :=
            ValidArg1_One_iff (P 0 s1 Z) t1 (dom1_P0_of_Zero s1 hd)
          have hteq0 : t0 = Z := hva0.mp ht0
          have hteq1 : t1 = Z := hva1.mp ht1
          rw [hteq0, hteq1] at hlt
          exact absurd hlt (lt_irrefl_thm Z)
        | succ l0 =>
          rw [fund1_Psucc_of_Zero l0 s1 t0 hd, fund1_Psucc_of_Zero l0 s1 t1 hd]
          exact hlt
      | One =>
        have hva0 : T.ValidArg1 (P s0 s1 Z) t0 ↔ T.IsN t0 :=
          ValidArg1_ω_iff (P s0 s1 Z) t0 (dom1_P_of_One s0 s1 hd)
        have hva1 : T.ValidArg1 (P s0 s1 Z) t1 ↔ T.IsN t1 :=
          ValidArg1_ω_iff (P s0 s1 Z) t1 (dom1_P_of_One s0 s1 hd)
        have hisn0 : T.IsN t0 := hva0.mp ht0
        have hisn1 : T.IsN t1 := hva1.mp ht1
        obtain ⟨n0, hn0⟩ := IsN_exists_ofNat hisn0
        obtain ⟨n1, hn1⟩ := IsN_exists_ofNat hisn1
        have hnlt : n0 < n1 := by
          apply ofNat_reflect_lt; rw [← hn0, ← hn1]; exact hlt
        have hXne : (P s0 (T.fund1 s1 Z) Z : T) ≠ Z := fun hcontra => by cases hcontra
        rw [fund1_P_of_One s0 s1 t0 hd, fund1_P_of_One s0 s1 t1 hd, hn0, hn1]
        exact mul_ofNat_strict_mono (P s0 (T.fund1 s1 Z) Z) hXne n1 n0 hnlt
      | ω =>
        have hva0 : T.ValidArg1 (P s0 s1 Z) t0 ↔ T.IsN t0 :=
          ValidArg1_ω_iff (P s0 s1 Z) t0 (dom1_P_of_ω s0 s1 hd)
        have hva1 : T.ValidArg1 (P s0 s1 Z) t1 ↔ T.IsN t1 :=
          ValidArg1_ω_iff (P s0 s1 Z) t1 (dom1_P_of_ω s0 s1 hd)
        have hisn0 : T.IsN t0 := hva0.mp ht0
        have hisn1 : T.IsN t1 := hva1.mp ht1
        have hv01 : T.ValidArg1 s1 t0 := (ValidArg1_ω_iff s1 t0 hd).mpr hisn0
        have hv11 : T.ValidArg1 s1 t1 := (ValidArg1_ω_iff s1 t1 hd).mpr hisn1
        have hlt1 : T.fund1 s1 t0 < T.fund1 s1 t1 := ih1 t0 t1 hlt hv01 hv11
        rw [fund1_P_of_ω s0 s1 t0 hd, fund1_P_of_ω s0 s1 t1 hd]
        exact T.Lt.p_mid s0 (T.fund1 s1 t0) (T.fund1 s1 t1) Z Z hlt1
      | Ω l =>
        apply Decidable.byCases (p := s0 ≤ l)
        · intro hle
          have hdm : T.dom1 (P s0 s1 Z) = Dom1.ω := by
            rw [dom1_P_of_Ω s0 s1 l hd, ite_eq_left hle]
          have hva0 : T.ValidArg1 (P s0 s1 Z) t0 ↔ T.IsN t0 := ValidArg1_ω_iff (P s0 s1 Z) t0 hdm
          have hva1 : T.ValidArg1 (P s0 s1 Z) t1 ↔ T.IsN t1 := ValidArg1_ω_iff (P s0 s1 Z) t1 hdm
          have hisn0 : T.IsN t0 := hva0.mp ht0
          have hisn1 : T.IsN t1 := hva1.mp ht1
          have hiterlt :
              T.iter (fun x => P l (T.fund1 s1 x) Z) t0 <
                T.iter (fun x => P l (T.fund1 s1 x) Z) t1 :=
            iter_F_strict_mono s1 l hd ih1 t0 t1 hlt hisn0 hisn1
          have hindex0 : T.index_Prop1 l (T.iter (fun x => P l (T.fund1 s1 x) Z) t0) :=
            iter_index_Prop1 l (fun x => P l (T.fund1 s1 x) Z) (fun x => ⟨T.fund1 s1 x, rfl⟩) t0
          have hindex1 : T.index_Prop1 l (T.iter (fun x => P l (T.fund1 s1 x) Z) t1) :=
            iter_index_Prop1 l (fun x => P l (T.fund1 s1 x) Z) (fun x => ⟨T.fund1 s1 x, rfl⟩) t1
          have hv01 : T.ValidArg1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t0) :=
            (ValidArg1_Ω_iff s1 _ l hd).mpr hindex0
          have hv11 : T.ValidArg1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t1) :=
            (ValidArg1_Ω_iff s1 _ l hd).mpr hindex1
          have hlt1 :
              T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t0) <
                T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t1) :=
            ih1 _ _ hiterlt hv01 hv11
          rw [fund1_P_of_Ω_le s0 s1 t0 l hd hle, fund1_P_of_Ω_le s0 s1 t1 l hd hle]
          exact T.Lt.p_mid s0
            (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t0))
            (T.fund1 s1 (T.iter (fun x => P l (T.fund1 s1 x) Z) t1)) Z Z hlt1
        · intro hle
          have hdm : T.dom1 (P s0 s1 Z) = Dom1.Ω l := by
            rw [dom1_P_of_Ω s0 s1 l hd, ite_eq_right hle]
          have hva0 : T.ValidArg1 (P s0 s1 Z) t0 ↔ T.index_Prop1 l t0 :=
            ValidArg1_Ω_iff (P s0 s1 Z) t0 l hdm
          have hva1 : T.ValidArg1 (P s0 s1 Z) t1 ↔ T.index_Prop1 l t1 :=
            ValidArg1_Ω_iff (P s0 s1 Z) t1 l hdm
          have hip0 : T.index_Prop1 l t0 := hva0.mp ht0
          have hip1 : T.index_Prop1 l t1 := hva1.mp ht1
          have hv01 : T.ValidArg1 s1 t0 := (ValidArg1_Ω_iff s1 t0 l hd).mpr hip0
          have hv11 : T.ValidArg1 s1 t1 := (ValidArg1_Ω_iff s1 t1 l hd).mpr hip1
          have hlt1 : T.fund1 s1 t0 < T.fund1 s1 t1 := ih1 t0 t1 hlt hv01 hv11
          rw [fund1_P_of_Ω_gt s0 s1 t0 l hd hle, fund1_P_of_Ω_gt s0 s1 t1 l hd hle]
          exact T.Lt.p_mid s0 (T.fund1 s1 t0) (T.fund1 s1 t1) Z Z hlt1
    | P s20 s21 s22 =>
      have htail_iff0 :
          T.ValidArg1 (P s0 s1 (P s20 s21 s22)) t0 ↔ T.ValidArg1 (P s20 s21 s22) t0 := by
        unfold T.ValidArg1; rw [dom1_P_tail s0 s1 s20 s21 s22]
      have htail_iff1 :
          T.ValidArg1 (P s0 s1 (P s20 s21 s22)) t1 ↔ T.ValidArg1 (P s20 s21 s22) t1 := by
        unfold T.ValidArg1; rw [dom1_P_tail s0 s1 s20 s21 s22]
      have hv02 : T.ValidArg1 (P s20 s21 s22) t0 := htail_iff0.mp ht0
      have hv12 : T.ValidArg1 (P s20 s21 s22) t1 := htail_iff1.mp ht1
      have hlt2 : T.fund1 (P s20 s21 s22) t0 < T.fund1 (P s20 s21 s22) t1 :=
        ih2 t0 t1 hlt hv02 hv12
      rw [fund1_P_tail s0 s1 t0 s20 s21 s22, fund1_P_tail s0 s1 t1 s20 s21 s22]
      exact T.Lt.p_tail s0 s1
        (T.fund1 (P s20 s21 s22) t0) (T.fund1 (P s20 s21 s22) t1) hlt2

def T.G1 (u : Nat) (s : T) : List T :=
  match s with
  | Z => []
  | P s0 s1 s2 =>
    let Gs2 := T.G1 u s2
    if u ≤ s0 then
      [s1] ++ T.G1 u s1 ++ Gs2
    else Gs2

inductive T.isNF1 : T → Prop where
| z : T.isNF1 Z
| p (s0 : Nat) (s1 s2 : T) (hs1 : T.isNF1 s1) (hs2 : T.isNF1 s2)
  (h1 : ∀ x : T, x ∈ T.G1 s0 s1 → x < s1)
  (h2 : T.head s2 ≤ P s0 s1 Z) :
  T.isNF1 (P s0 s1 s2)

def T.decidableBAllLt (l : List T) (y : T) : Decidable (∀ x ∈ l, x < y) :=
  match l with
  | [] => isTrue (fun _x hx => absurd hx List.not_mem_nil)
  | a :: as =>
    match (inferInstance : Decidable (a < y)) with
    | isFalse hna => isFalse (fun h => hna (h a List.mem_cons_self))
    | isTrue ha =>
      match T.decidableBAllLt as y with
      | isFalse hnas => isFalse (fun h => hnas (fun x hx => h x (List.mem_cons_of_mem a hx)))
      | isTrue has => isTrue (fun x hx =>
          (List.mem_cons.mp hx).elim (fun heq => heq ▸ ha) (fun hx' => has x hx'))

def T.decIsNF (s : T) : Decidable (T.isNF1 s) :=
  match s with
  | Z => isTrue T.isNF1.z
  | P s0 s1 s2 =>
    match T.decIsNF s1 with
    | isFalse hn1 => isFalse (fun h => by
        cases h with
        | p _ _ _ hs1 _ _ _ => exact hn1 hs1)
    | isTrue hs1 =>
      match T.decIsNF s2 with
      | isFalse hn2 => isFalse (fun h => by
          cases h with
          | p _ _ _ _ hs2 _ _ => exact hn2 hs2)
      | isTrue hs2 =>
        match T.decidableBAllLt (T.G1 s0 s1) s1 with
        | isFalse hn3 => isFalse (fun h => by
            cases h with
            | p _ _ _ _ _ h1 _ => exact hn3 h1)
        | isTrue h1 =>
          match (inferInstance : Decidable (T.head s2 ≤ P s0 s1 Z)) with
          | isFalse hn4 => isFalse (fun h => by
              cases h with
              | p _ _ _ _ _ _ h2 => exact hn4 h2)
          | isTrue h2 => isTrue (T.isNF1.p s0 s1 s2 hs1 hs2 h1 h2)

instance (s : T) : Decidable (T.isNF1 s) := T.decIsNF s

theorem T.isNF1_P_inv (s0 : Nat) (s1 s2 : T) (h : T.isNF1 (P s0 s1 s2)) :
    T.isNF1 s1 ∧ T.isNF1 s2 ∧ (∀ x : T, x ∈ T.G1 s0 s1 → x < s1) ∧ T.head s2 ≤ P s0 s1 Z := by
  cases h with
  | p _ _ _ hs1 hs2 h1 h2 =>
    exact ⟨hs1, hs2, h1, h2⟩

def T.GZ (u : Nat) (z : T) : List T := T.G1 u z ++ [Z]

def T.SDom (z b a : T) : Prop :=
  b < a ∧ ∀ (u : Nat) (c : T), b ≤ c → c ≤ a →
    T.listLe (T.G1 u b) (T.G1 u c ++ T.GZ u z)

theorem SDom_G1_lt_a (z b a : T) (u : Nat) (hb : T.SDom z b a)
    (hGa : ∀ x ∈ T.G1 u a, x < a) (hGz : ∀ x ∈ T.GZ u z, x < b) :
    ∀ y ∈ T.G1 u b, y < a := by
  intro y hy
  have hba : b ≤ a := Or.inl hb.1
  have haa : a ≤ a := partial_order.refl a
  obtain ⟨w, hw, hyw⟩ := hb.2 u a hba haa y hy
  rw [List.mem_append] at hw
  rcases hw with hw1 | hw2
  · have hwa : w < a := hGa w hw1
    exact lt_of_le_of_lt_thm T y w a hyw hwa
  · have hwb : w < b := hGz w hw2
    have hyb : y < b := lt_of_le_of_lt_thm T y w b hyw hwb
    exact lt_of_lt_of_le_thm T y b a hyb hba

theorem find_violating_source (u : Nat) (b : T) :
    ∀ c₀ : T, ∀ w : T, w ∈ T.G1 u c₀ → b ≤ w →
      ∃ c : T, c ∈ T.G1 u c₀ ∧ b ≤ c ∧ (∀ x ∈ T.G1 u c, x < b) := by
  intro c₀
  induction c₀ with
  | Z =>
    intro w hw _
    rw [T.G1.eq_1] at hw
    cases hw
  | P p0 p1 p2 ih1 ih2 =>
    intro w hw hbw
    apply Decidable.byCases (p := u ≤ p0)
    · intro hup
      rw [T.G1.eq_2, ite_eq_left hup] at hw
      rw [List.mem_append, List.mem_append] at hw
      rcases hw with (hw1 | hw2) | hw3
      · rw [List.mem_singleton] at hw1
        cases hw1
        apply Decidable.byCases (p := ∃ x ∈ T.G1 u p1, b ≤ x)
        · intro hviol
          obtain ⟨x, hx1, hx2⟩ := hviol
          obtain ⟨c, hc1, hc2, hc3⟩ := ih1 x hx1 hx2
          refine ⟨c, ?_, hc2, hc3⟩
          rw [T.G1.eq_2, ite_eq_left hup]
          rw [List.mem_append, List.mem_append]
          exact Or.inl (Or.inr hc1)
        · intro hviol
          refine ⟨p1, ?_, hbw, ?_⟩
          · rw [T.G1.eq_2, ite_eq_left hup]
            rw [List.mem_append, List.mem_append]
            exact Or.inl (Or.inl (List.mem_singleton_self p1))
          · intro x hx
            apply Decidable.byCases (p := b ≤ x)
            · intro hxb
              exact absurd ⟨x, hx, hxb⟩ hviol
            · intro hxb
              rcases linear_order.total x b with h1 | h1
              · rcases h1 with h1 | h1
                · exact h1
                · exact absurd (Or.inr h1.symm) hxb
              · exact absurd h1 hxb
      · obtain ⟨c, hc1, hc2, hc3⟩ := ih1 w hw2 hbw
        refine ⟨c, ?_, hc2, hc3⟩
        rw [T.G1.eq_2, ite_eq_left hup]
        rw [List.mem_append, List.mem_append]
        exact Or.inl (Or.inr hc1)
      · obtain ⟨c, hc1, hc2, hc3⟩ := ih2 w hw3 hbw
        refine ⟨c, ?_, hc2, hc3⟩
        rw [T.G1.eq_2, ite_eq_left hup]
        rw [List.mem_append, List.mem_append]
        exact Or.inr hc1
    · intro hup
      rw [T.G1.eq_2, ite_eq_right hup] at hw
      obtain ⟨c, hc1, hc2, hc3⟩ := ih2 w hw hbw
      refine ⟨c, ?_, hc2, hc3⟩
      rw [T.G1.eq_2, ite_eq_right hup]
      exact hc1

theorem lemma_3_4 (z b a : T) (u : Nat) (hSDom : T.SDom z b a)
    (hGa : ∀ x ∈ T.G1 u a, x < a) (hGz : ∀ x ∈ T.GZ u z, x < b) :
    ∀ y ∈ T.G1 u b, y < b := by
  intro y hy
  rcases linear_order.total y b with hcase | hcase
  · rcases hcase with hcase | hcase
    · exact hcase
    · exfalso
      have hby : b ≤ y := Or.inr hcase.symm
      obtain ⟨c, hcG, hbc, hcbound⟩ := find_violating_source u b b y hy hby
      have hca : c < a := SDom_G1_lt_a z b a u hSDom hGa hGz c hcG
      have hca' : c ≤ a := Or.inl hca
      have hlisteq := hSDom.2 u c hbc hca'
      obtain ⟨wit, hwit1, hwit2⟩ := hlisteq y hy
      rw [List.mem_append] at hwit1
      have hwitb : wit < b := by
        rcases hwit1 with hwit1 | hwit1
        · exact hcbound wit hwit1
        · exact hGz wit hwit1
      have hyb : y < b := lt_of_le_of_lt_thm T y wit b hwit2 hwitb
      exact lt_irrefl_thm y (hcase ▸ hyb)
  · exfalso
    have hby : b ≤ y := hcase
    obtain ⟨c, hcG, hbc, hcbound⟩ := find_violating_source u b b y hy hby
    have hca : c < a := SDom_G1_lt_a z b a u hSDom hGa hGz c hcG
    have hca' : c ≤ a := Or.inl hca
    have hlisteq := hSDom.2 u c hbc hca'
    obtain ⟨wit, hwit1, hwit2⟩ := hlisteq y hy
    rw [List.mem_append] at hwit1
    have hwitb : wit < b := by
      rcases hwit1 with hwit1 | hwit1
      · exact hcbound wit hwit1
      · exact hGz wit hwit1
    have hyb : y < b := lt_of_le_of_lt_thm T y wit b hwit2 hwitb
    exact lt_irrefl_thm y (lt_of_lt_of_le_thm T y b y hyb hcase)

theorem SDom_tail (z b0 b : T) (s0 : Nat) (s1 : T) (hb0 : T.SDom z b0 b) :
    T.SDom z (P s0 s1 b0) (P s0 s1 b) := by
  constructor
  · exact T.Lt.p_tail s0 s1 b0 b hb0.1
  · intro u c hc1 hc2
    rcases hc1 with hc1lt | hc1eq
    · rcases hc2 with hc2lt | hc2eq
      · obtain ⟨c0, hceq, hbc0, hc0b⟩ := sandwich_tail s0 s1 b0 c b hc1lt hc2lt
        rw [hceq]
        have hlisteq := hb0.2 u c0 (Or.inl hbc0) (Or.inl hc0b)
        apply Decidable.byCases (p := u ≤ s0)
        · intro hus
          rw [T.G1.eq_2, ite_eq_left hus, T.G1.eq_2, ite_eq_left hus, List.append_assoc, List.append_assoc]
          exact listLe_append_congr [s1] _ _ (listLe_append_congr (T.G1 u s1) _ _ hlisteq)
        · intro hus
          rw [T.G1.eq_2, ite_eq_right hus, T.G1.eq_2, ite_eq_right hus]
          exact hlisteq
      · rw [hc2eq]
        have hbb : b0 ≤ b := Or.inl hb0.1
        have hbbb : b ≤ b := partial_order.refl b
        have hlisteq := hb0.2 u b hbb hbbb
        apply Decidable.byCases (p := u ≤ s0)
        · intro hus
          rw [T.G1.eq_2, ite_eq_left hus, T.G1.eq_2, ite_eq_left hus, List.append_assoc, List.append_assoc]
          exact listLe_append_congr [s1] _ _ (listLe_append_congr (T.G1 u s1) _ _ hlisteq)
        · intro hus
          rw [T.G1.eq_2, ite_eq_right hus, T.G1.eq_2, ite_eq_right hus]
          exact hlisteq
    · rw [← hc1eq]
      exact listLe_self_append _ _

theorem G1_PZ_pos (u p0 : Nat) (p1 : T) (h : u ≤ p0) :
    T.G1 u (P p0 p1 Z) = [p1] ++ T.G1 u p1 := by
  rw [T.G1.eq_2, ite_eq_left h, T.G1.eq_1, List.append_nil]

theorem G1_PZ_neg (u p0 : Nat) (p1 : T) (h : ¬ u ≤ p0) :
    T.G1 u (P p0 p1 Z) = [] := by
  rw [T.G1.eq_2, ite_eq_right h, T.G1.eq_1]

theorem SDom_wrap (z b0 b : T) (s0 : Nat) (hb0 : T.SDom z b0 b) :
    T.SDom z (P s0 b0 Z) (P s0 b Z) := by
  constructor
  · exact T.Lt.p_mid s0 b0 b Z Z hb0.1
  · intro u c hc1 hc2
    rcases hc1 with hc1lt | hc1eq
    · rcases hc2 with hc2lt | hc2eq
      · obtain ⟨c1, c2, hceq, hbc1, hc1b⟩ := sandwich_mid s0 b0 b c hb0.1 hc1lt hc2lt
        rw [hceq]
        have hlisteq := hb0.2 u c1 hbc1 (Or.inl hc1b)
        apply Decidable.byCases (p := u ≤ s0)
        · intro hus
          rw [G1_PZ_pos u s0 b0 hus, T.G1.eq_2, ite_eq_left hus]
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · rw [List.mem_singleton] at hx
            cases hx
            refine ⟨c1, ?_, hbc1⟩
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self c1)))
          · obtain ⟨w, hw1, hw2⟩ := hlisteq x hx
            rw [List.mem_append] at hw1
            rcases hw1 with hw1 | hw1
            · refine ⟨w, ?_, hw2⟩
              exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hw1))
            · refine ⟨w, ?_, hw2⟩
              exact List.mem_append_right _ hw1
        · intro hus
          rw [G1_PZ_neg u s0 b0 hus]
          intro x hx
          cases hx
      · rw [hc2eq]
        have hbb : b0 ≤ b := Or.inl hb0.1
        have hbbb : b ≤ b := partial_order.refl b
        have hlisteq := hb0.2 u b hbb hbbb
        apply Decidable.byCases (p := u ≤ s0)
        · intro hus
          rw [G1_PZ_pos u s0 b0 hus, G1_PZ_pos u s0 b hus]
          intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · rw [List.mem_singleton] at hx
            cases hx
            refine ⟨b, ?_, Or.inl hb0.1⟩
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self b))
          · obtain ⟨w, hw1, hw2⟩ := hlisteq x hx
            rw [List.mem_append] at hw1
            rcases hw1 with hw1 | hw1
            · refine ⟨w, ?_, hw2⟩
              exact List.mem_append_left _ (List.mem_append_right _ hw1)
            · refine ⟨w, ?_, hw2⟩
              exact List.mem_append_right _ hw1
        · intro hus
          rw [G1_PZ_neg u s0 b0 hus]
          intro x hx
          cases hx
    · rw [← hc1eq]
      exact listLe_self_append _ _

theorem T.isNF1_tail_le : ∀ x : T, T.isNF1 x → ∀ x0 x1 x2, x = P x0 x1 x2 → x2 ≤ P x0 x1 x2 := by
  intro x
  induction x with
  | Z => intro _ x0 x1 x2 he; cases he
  | P a0 a1 a2 ih1 ih2 =>
    intro ha x0 x1 x2 he
    injection he with he0 he1 he2
    cases he0; cases he1; cases he2
    obtain ⟨_hs1, hs2, _h1, h2⟩ := T.isNF1_P_inv a0 a1 a2 ha
    cases a2 with
    | Z => exact T.Z_le _
    | P b0 b1 b2 =>
      have hheadeq : T.head (P b0 b1 b2) = P b0 b1 Z := rfl
      rw [hheadeq] at h2
      cases h2 with
      | inl hlt =>
        have hinv := lt_inv b0 b1 Z a0 a1 Z hlt
        cases hinv with
        | inl hh =>
          exact Or.inl (T.Lt.p_head b0 a0 b1 a1 b2 (P b0 b1 b2) hh)
        | inr hor =>
          cases hor with
          | inl hmid =>
            obtain ⟨heq0, hlt1⟩ := hmid
            cases heq0
            exact Or.inl (T.Lt.p_mid a0 b1 a1 b2 (P a0 b1 b2) hlt1)
          | inr htail =>
            obtain ⟨_heq0, _heq1, hZZ⟩ := htail
            exact absurd hZZ (lt_irrefl_thm Z)
      | inr heq =>
        injection heq with heq0 heq1
        cases heq0
        cases heq1
        have hrec : b2 ≤ P a0 a1 b2 := ih2 hs2 a0 a1 b2 rfl
        cases hrec with
        | inl hlt2 =>
          exact Or.inl (T.Lt.p_tail a0 a1 b2 (P a0 a1 b2) hlt2)
        | inr heq2 =>
          rw [← heq2]
          exact Or.inr heq2

theorem IsN_G1_eq_Z (t : T) (h : T.IsN t) (u : Nat) : ∀ x ∈ T.G1 u t, x = Z := by
  induction h with
  | zero =>
    intro x hx
    rw [T.G1.eq_1] at hx
    cases hx
  | succ t' h' ih =>
    intro x hx
    apply Decidable.byCases (p := u ≤ 0)
    · intro hu
      rw [T.G1.eq_2, ite_eq_left hu] at hx
      rw [List.mem_append, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · rw [List.mem_singleton] at hx; exact hx
      · rw [T.G1.eq_1] at hx; cases hx
      · exact ih x hx
    · intro hu
      rw [T.G1.eq_2, ite_eq_right hu] at hx
      exact ih x hx

theorem index_Prop1_G1_empty (l : Nat) (t : T) (h : T.index_Prop1 l t) (u : Nat) (hlu : l < u) :
    T.G1 u t = [] := by
  induction h with
  | z => exact T.G1.eq_1 u
  | p s0' s1' s2' hle hrec ih =>
    have hnle : ¬ u ≤ s0' := by
      intro hc
      have : u ≤ l := Nat.le_trans hc hle
      exact absurd (Nat.lt_of_lt_of_le hlu this) (Nat.lt_irrefl l)
    rw [T.G1.eq_2, ite_eq_right hnle]
    exact ih

theorem mul_isNF1_and_head (s0 : Nat) (c : T) (hc : T.isNF1 c) (h1c : ∀ x ∈ T.G1 s0 c, x < c) :
    ∀ n : Nat, T.isNF1 (T.mul (P s0 c Z) (T.ofNat n)) ∧
      T.head (T.mul (P s0 c Z) (T.ofNat n)) ≤ P s0 c Z := by
  intro n
  induction n with
  | zero =>
    rw [T.ofNat.eq_1, T.mul.eq_1]
    exact ⟨T.isNF1.z, T.Z_le (P s0 c Z)⟩
  | succ n ih =>
    rw [mul_succ_shape s0 c n]
    refine ⟨T.isNF1.p s0 c _ hc ih.1 h1c ?_, ?_⟩
    · exact ih.2
    · exact Or.inr rfl

theorem GZ_Z_mem (u : Nat) (w : T) : Z ∈ T.GZ u w := by
  unfold T.GZ
  exact List.mem_append_right _ (List.mem_singleton_self Z)

theorem GZ_Z_le (u : Nat) (w : T) : T.listLe (T.GZ u Z) (T.GZ u w) := by
  intro x hx
  unfold T.GZ at hx
  rw [T.G1.eq_1, List.nil_append, List.mem_singleton] at hx
  cases hx
  exact ⟨Z, GZ_Z_mem u w, Or.inr rfl⟩

theorem GZ_ofNat_le (u n : Nat) (w : T) : T.listLe (T.GZ u (T.ofNat n)) (T.GZ u w) := by
  intro x hx
  unfold T.GZ at hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · have hxZ : x = Z := IsN_G1_eq_Z (T.ofNat n) (ofNat_IsN n) u x hx
    exact ⟨Z, GZ_Z_mem u w, Or.inr hxZ⟩
  · rw [List.mem_singleton] at hx
    exact ⟨Z, GZ_Z_mem u w, Or.inr hx⟩

theorem G1_P_pos (u p0 : Nat) (p1 p2 : T) (h : u ≤ p0) :
    T.G1 u (P p0 p1 p2) = [p1] ++ T.G1 u p1 ++ T.G1 u p2 := by
  rw [T.G1.eq_2, ite_eq_left h]

theorem mul_SDom (s0 : Nat) (c s1 : T) (hSDc : T.SDom Z c s1) :
    ∀ n : Nat, T.SDom (T.ofNat n) (T.mul (P s0 c Z) (T.ofNat n)) (P s0 s1 Z) := by
  have hcs1 : c < s1 := hSDc.1
  intro n
  induction n with
  | zero =>
    rw [T.ofNat.eq_1, T.mul.eq_1]
    refine ⟨T.Lt.Z_lt_P s0 s1 Z, ?_⟩
    intro u c' _ _ x hx
    rw [T.G1.eq_1] at hx
    cases hx
  | succ n ih =>
    have hMlt : T.mul (P s0 c Z) (T.ofNat n) < P s0 c (T.mul (P s0 c Z) (T.ofNat n)) :=
      tail_lt_wrap s0 c n
    rw [mul_succ_shape s0 c n]
    refine ⟨T.Lt.p_mid s0 c s1 (T.mul (P s0 c Z) (T.ofNat n)) Z hcs1, ?_⟩
    intro u c' hc1 hc2
    rcases hc1 with hc1lt | hc1eq
    · rcases hc2 with hc2lt | hc2eq
      · obtain ⟨c1', c2', hceq, hcase⟩ :=
          sandwich_mid_tail s0 c (T.mul (P s0 c Z) (T.ofNat n)) s1 c' hc1lt hc2lt
        have hcc1 : c ≤ c1' := by
          exact match hcase with
          | Or.inl ⟨h1, _⟩ => by
            exact Or.inl h1
          | Or.inr ⟨h1, _⟩ => by
            exact Or.inr h1.symm
        have hc1s1 : c1' < s1 := by
          exact match hcase with
          | Or.inl ⟨_, h2⟩ => by
            exact h2
          | Or.inr ⟨h1, _⟩ => by
            rw [h1]; exact hcs1
        have hMc' : T.mul (P s0 c Z) (T.ofNat n) < c' :=
          lt_trans_thm (T.mul (P s0 c Z) (T.ofNat n)) (P s0 c (T.mul (P s0 c Z) (T.ofNat n))) c' hMlt hc1lt
        rw [hceq]
        apply Decidable.byCases (p := u ≤ s0)
        · intro hus
          rw [G1_P_pos u s0 c (T.mul (P s0 c Z) (T.ofNat n)) hus, G1_P_pos u s0 c1' c2' hus]
          have hSD2 := hSDc.2 u c1' hcc1 (Or.inl hc1s1)
          have hih2 := ih.2 u c' (Or.inl hMc') (Or.inl hc2lt)
          rw [hceq, G1_P_pos u s0 c1' c2' hus] at hih2
          intro x hx
          rw [List.mem_append, List.mem_append] at hx
          rcases hx with (hx | hx) | hx
          · rw [List.mem_singleton] at hx
            cases hx
            exact ⟨c1', List.mem_append_left (T.GZ u (T.ofNat (n+1))) (List.mem_append_left (T.G1 u c2') (List.mem_append_left (T.G1 u c1') (List.mem_singleton_self c1'))), hcc1⟩
          · obtain ⟨w, hw1, hw2⟩ := hSD2 x hx
            rw [List.mem_append] at hw1
            rcases hw1 with hw1 | hw1
            · exact ⟨w, List.mem_append_left (T.GZ u (T.ofNat (n+1))) (List.mem_append_left (T.G1 u c2') (List.mem_append_right ([c1']) hw1)), hw2⟩
            · have hwZ : w = Z := by
                unfold T.GZ at hw1
                rw [T.G1.eq_1, List.nil_append, List.mem_singleton] at hw1
                exact hw1
              exact ⟨Z, List.mem_append_right (([c1'] ++ T.G1 u c1') ++ T.G1 u c2') (hwZ ▸ GZ_Z_mem u (T.ofNat (n+1))), hwZ ▸ hw2⟩
          · obtain ⟨w, hw1, hw2⟩ := hih2 x hx
            rw [List.mem_append, List.mem_append, List.mem_append] at hw1
            rcases hw1 with ((hw1 | hw1) | hw1) | hw1
            · rw [List.mem_singleton] at hw1
              cases hw1
              exact ⟨c1', List.mem_append_left (T.GZ u (T.ofNat (n+1))) (List.mem_append_left (T.G1 u c2') (List.mem_append_left (T.G1 u c1') (List.mem_singleton_self c1'))), hw2⟩
            · exact ⟨w, List.mem_append_left (T.GZ u (T.ofNat (n+1))) (List.mem_append_left (T.G1 u c2') (List.mem_append_right ([c1']) hw1)), hw2⟩
            · exact ⟨w, List.mem_append_left (T.GZ u (T.ofNat (n+1))) (List.mem_append_right ([c1'] ++ T.G1 u c1') hw1), hw2⟩
            · obtain ⟨w', hw1', hw2'⟩ := GZ_ofNat_le u n (T.ofNat (n+1)) w hw1
              exact ⟨w', List.mem_append_right (([c1'] ++ T.G1 u c1') ++ T.G1 u c2') hw1', partial_order.trans x w w' hw2 hw2'⟩
        · intro hus
          rw [T.G1.eq_2, ite_eq_right hus, T.G1.eq_2, ite_eq_right hus]
          have hih2 := ih.2 u c' (Or.inl hMc') (Or.inl hc2lt)
          rw [hceq, T.G1.eq_2, ite_eq_right hus] at hih2
          intro x hx
          obtain ⟨w, hw1, hw2⟩ := hih2 x hx
          rw [List.mem_append] at hw1
          rcases hw1 with hw1 | hw1
          · exact ⟨w, List.mem_append_left (T.GZ u (T.ofNat (n+1))) hw1, hw2⟩
          · obtain ⟨w', hw1', hw2'⟩ := GZ_ofNat_le u n (T.ofNat (n+1)) w hw1
            exact ⟨w', List.mem_append_right (T.G1 u c2') hw1', partial_order.trans x w w' hw2 hw2'⟩
      · apply Decidable.byCases (p := u ≤ s0)
        · intro hus2
          have hgoal : T.listLe ([c] ++ T.G1 u c ++ T.G1 u (T.mul (P s0 c Z) (T.ofNat n)))
              (([s1] ++ T.G1 u s1) ++ T.GZ u (T.ofNat (n+1))) := by
            have hSD2 := hSDc.2 u s1 (Or.inl hcs1) (partial_order.refl s1)
            have hih2 := ih.2 u (P s0 s1 Z) (Or.inl ih.1) (partial_order.refl (P s0 s1 Z))
            rw [G1_PZ_pos u s0 s1 hus2] at hih2
            intro x hx
            rw [List.mem_append, List.mem_append] at hx
            rcases hx with (hx | hx) | hx
            · rw [List.mem_singleton] at hx
              cases hx
              exact ⟨s1, List.mem_append_left (T.GZ u (T.ofNat (n+1))) (List.mem_append_left (T.G1 u s1) (List.mem_singleton_self s1)), Or.inl hcs1⟩
            · obtain ⟨w, hw1, hw2⟩ := hSD2 x hx
              rw [List.mem_append] at hw1
              rcases hw1 with hw1 | hw1
              · exact ⟨w, List.mem_append_left (T.GZ u (T.ofNat (n+1))) (List.mem_append_right ([s1]) hw1), hw2⟩
              · have hwZ : w = Z := by
                  unfold T.GZ at hw1
                  rw [T.G1.eq_1, List.nil_append, List.mem_singleton] at hw1
                  exact hw1
                exact ⟨Z, List.mem_append_right ([s1] ++ T.G1 u s1) (hwZ ▸ GZ_Z_mem u (T.ofNat (n+1))), hwZ ▸ hw2⟩
            · obtain ⟨w, hw1, hw2⟩ := hih2 x hx
              rw [List.mem_append] at hw1
              rcases hw1 with hw1 | hw1
              · exact ⟨w, List.mem_append_left (T.GZ u (T.ofNat (n+1))) hw1, hw2⟩
              · obtain ⟨w', hw1', hw2'⟩ := GZ_ofNat_le u n (T.ofNat (n+1)) w hw1
                exact ⟨w', List.mem_append_right ([s1] ++ T.G1 u s1) hw1', partial_order.trans x w w' hw2 hw2'⟩
          rw [hc2eq, G1_P_pos u s0 c (T.mul (P s0 c Z) (T.ofNat n)) hus2, G1_PZ_pos u s0 s1 hus2]
          exact hgoal
        · intro hus2
          have hgoal : T.listLe (T.G1 u (T.mul (P s0 c Z) (T.ofNat n))) (([] : List T) ++ T.GZ u (T.ofNat (n+1))) := by
            have hih2 := ih.2 u (P s0 s1 Z) (Or.inl ih.1) (partial_order.refl (P s0 s1 Z))
            rw [G1_PZ_neg u s0 s1 hus2, List.nil_append] at hih2
            intro x hx
            obtain ⟨w, hw1, hw2⟩ := hih2 x hx
            obtain ⟨w', hw1', hw2'⟩ := GZ_ofNat_le u n (T.ofNat (n+1)) w hw1
            exact ⟨w', List.mem_append_right [] hw1', partial_order.trans x w w' hw2 hw2'⟩
          rw [hc2eq, T.G1.eq_2, ite_eq_right hus2, G1_PZ_neg u s0 s1 hus2]
          exact hgoal
    · rw [← hc1eq]
      exact listLe_self_append _ _

theorem GZ_z_sub_self (u : Nat) (z : T) : T.listLe (T.G1 u z) (T.GZ u z) := by
  intro x hx
  exact ⟨x, List.mem_append_left [Z] hx, Or.inr rfl⟩

theorem G1_antitone (u v : Nat) (huv : u ≤ v) (s : T) :
    ∀ x ∈ T.G1 v s, x ∈ T.G1 u s := by
  induction s with
  | Z => intro x hx; exact hx
  | P s0 s1 s2 ih1 ih2 =>
    intro x hx
    apply Decidable.byCases (p := v ≤ s0)
    · intro hv
      have hu := Nat.le_trans huv hv
      rw [T.G1.eq_2, ite_eq_left hv, List.mem_append, List.mem_append] at hx
      rw [T.G1.eq_2, ite_eq_left hu, List.mem_append, List.mem_append]
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inl hx)
      · exact Or.inl (Or.inr (ih1 x hx))
      · exact Or.inr (ih2 x hx)
    · intro hv
      rw [T.G1.eq_2, ite_eq_right hv] at hx
      apply Decidable.byCases (p := u ≤ s0)
      · intro hu
        rw [T.G1.eq_2, ite_eq_left hu]
        exact List.mem_append_right _ (ih2 x hx)
      · intro hu
        rw [T.G1.eq_2, ite_eq_right hu]
        exact ih2 x hx

theorem SDom_wrap_transfer (z w b a : T) (k : Nat) (h : T.SDom w b a)
    (hsupport : ∀ u, u ≤ k → ∀ c, P k b Z ≤ c → c ≤ P k a Z →
      T.listLe (T.GZ u w) (T.G1 u c ++ T.GZ u z)) :
    T.SDom z (P k b Z) (P k a Z) := by
  have hw := SDom_wrap w b a k h
  refine ⟨hw.1, ?_⟩
  intro u c hbc hca x hx
  apply Decidable.byCases (p := u ≤ k)
  · intro hu
    obtain ⟨y, hy, hxy⟩ := hw.2 u c hbc hca x hx
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact ⟨y, List.mem_append_left _ hy, hxy⟩
    · obtain ⟨v, hv, hyv⟩ := hsupport u hu c hbc hca y hy
      exact ⟨v, hv, partial_order.trans x y v hxy hyv⟩
  · intro hu
    rw [G1_PZ_neg u k b hu] at hx
    cases hx

theorem iteration_master (a : T) (k l : Nat) (hkl : k ≤ l)
    (hd : T.dom1 a = Dom1.Ω l)
    (hbound : ∀ x ∈ T.G1 k a, x < a)
    (ih : ∀ z, T.isNF1 z → T.ValidArg1 a z →
      T.isNF1 (T.fund1 a z) ∧ T.SDom z (T.fund1 a z) a) :
    ∀ n, let w := T.iter (fun x => P l (T.fund1 a x) Z) (T.ofNat n)
      T.isNF1 w ∧ T.isNF1 (T.fund1 a w) ∧
      (∀ x ∈ T.G1 k (T.fund1 a w), x < T.fund1 a w) ∧
      T.SDom (T.ofNat n) (P k (T.fund1 a w) Z) (P k a Z) := by
  intro n
  induction n with
  | zero =>
    change T.isNF1 Z ∧ T.isNF1 (T.fund1 a Z) ∧
      (∀ x ∈ T.G1 k (T.fund1 a Z), x < T.fund1 a Z) ∧
      T.SDom Z (P k (T.fund1 a Z) Z) (P k a Z)
    have hv := (ValidArg1_Ω_iff a Z l hd).mpr T.index_Prop1.z
    obtain ⟨hc, hs⟩ := ih Z T.isNF1.z hv
    refine ⟨T.isNF1.z, hc, ?_, SDom_wrap Z _ a k hs⟩
    apply Decidable.byCases (p := T.fund1 a Z = Z)
    · intro he
      rw [he]; intro x hx; cases hx
    · intro he
      apply lemma_3_4 Z _ a k hs hbound
      intro x hx
      unfold T.GZ at hx
      rw [T.G1.eq_1, List.nil_append, List.mem_singleton] at hx
      rw [hx]
      rcases T.Z_le (T.fund1 a Z) with hlt | heq
      · exact hlt
      · exact False.elim (he heq.symm)
  | succ n hn =>
    let w := T.iter (fun x => P l (T.fund1 a x) Z) (T.ofNat n)
    let b := T.fund1 a w
    change T.isNF1 (P l b Z) ∧ T.isNF1 (T.fund1 a (P l b Z)) ∧
      (∀ x ∈ T.G1 k (T.fund1 a (P l b Z)), x < T.fund1 a (P l b Z)) ∧
      T.SDom (T.ofNat (n+1)) (P k (T.fund1 a (P l b Z)) Z) (P k a Z)
    have hw : T.isNF1 (P l b Z) :=
      T.isNF1.p l b Z hn.2.1 T.isNF1.z
        (fun x hx => hn.2.2.1 x (G1_antitone k l hkl b x hx)) (T.Z_le _)
    have hv := (ValidArg1_Ω_iff a (P l b Z) l hd).mpr
      (T.index_Prop1.p l b Z (Nat.le_refl l) T.index_Prop1.z)
    obtain ⟨hc, hs⟩ := ih (P l b Z) hw hv
    have hb : b < T.fund1 a (P l b Z) := by
      apply T.fund1_strict_mono_dec a
      · exact iter_F_step_mono a l hd
          (fun t0 t1 h ht0 ht1 => T.fund1_strict_mono_dec a t0 t1 h ht0 ht1) n
      · exact (ValidArg1_Ω_iff a w l hd).mpr
          (iter_index_Prop1 l _ (fun x => ⟨T.fund1 a x, rfl⟩) (T.ofNat n))
      · exact hv
    refine ⟨hw, hc, ?_, ?_⟩
    · apply lemma_3_4 (P l b Z) _ a k hs hbound
      intro x hx
      unfold T.GZ at hx
      rw [G1_PZ_pos k l b hkl, List.mem_append, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · rw [List.mem_singleton] at hx
        rw [hx]; exact hb
      · exact lt_trans_thm x b _ (hn.2.2.1 x hx) hb
      · rw [List.mem_singleton] at hx
        rw [hx]; exact lt_of_le_of_lt_thm T Z b _ (T.Z_le b) hb
    · apply SDom_wrap_transfer (T.ofNat (n+1)) (P l b Z) _ a k hs
      intro u hu c hbc hca x hx
      unfold T.GZ at hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · rw [G1_PZ_pos u l b (Nat.le_trans hu hkl),
          ← G1_PZ_pos u k b hu] at hx
        have hprev : P k b Z ≤ c := Or.inl
          (lt_of_lt_of_le_thm T _ _ c (T.Lt.p_mid k b _ Z Z hb) hbc)
        obtain ⟨y, hy, hxy⟩ := hn.2.2.2.2 u c hprev hca x hx
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · exact ⟨y, List.mem_append_left _ hy, hxy⟩
        · obtain ⟨v, hv', hyv⟩ := GZ_ofNat_le u n (T.ofNat (n+1)) y hy
          exact ⟨v, List.mem_append_right _ hv', partial_order.trans x y v hxy hyv⟩
      · rw [List.mem_singleton] at hx
        exact ⟨Z, List.mem_append_right _ (GZ_Z_mem u (T.ofNat (n+1))), Or.inr hx⟩

theorem master (a : T) : ∀ z : T, T.isNF1 a → T.isNF1 z → T.ValidArg1 a z →
    T.isNF1 (T.fund1 a z) ∧ T.SDom z (T.fund1 a z) a := by
  induction a with
  | Z =>
    intro z ha hz hv
    exact absurd hv (fun h => (ValidArg1_Zero_iff Z z T.dom1.eq_1).mp h)
  | P a0 a1 a2 ih1 ih2 =>
    intro z ha hz hv
    cases a2 with
    | Z =>
      obtain ⟨has1, has2, h1, h2⟩ := T.isNF1_P_inv a0 a1 Z ha
      cases hd : T.dom1 a1 with
      | Zero =>
        have ha1Z : a1 = Z := dom1_Zero_imp_eq_Z a1 hd
        cases a0 with
        | zero =>
          rw [fund1_P0_of_Zero a1 z hd]
          constructor
          · exact T.isNF1.z
          · constructor
            · exact T.Lt.Z_lt_P 0 a1 Z
            · intro u c _ _ x hx
              rw [T.G1.eq_1] at hx
              cases hx
        | succ l0 =>
          have hzlt : z < P (l0+1) a1 Z := by
            have h := T.fund1_fall (P (l0+1) a1 Z) z hv
            rw [fund1_Psucc_of_Zero l0 a1 z hd] at h
            exact h
          rw [fund1_Psucc_of_Zero l0 a1 z hd]
          refine ⟨hz, hzlt, ?_⟩
          intro u c _hc1 _hc2 x hx
          obtain ⟨y, hy1, hy2⟩ := GZ_z_sub_self u z x hx
          exact ⟨y, List.mem_append_right (T.G1 u c) hy1, hy2⟩
      | One =>
        have hz1 : T.ValidArg1 a1 Z := (ValidArg1_One_iff a1 Z hd).mpr rfl
        obtain ⟨hc, hSDc⟩ := ih1 Z has1 T.isNF1.z hz1
        have hvz : T.IsN z := (ValidArg1_ω_iff (P a0 a1 Z) z (dom1_P_of_One a0 a1 hd)).mp hv
        obtain ⟨m, hm⟩ := IsN_exists_ofNat hvz
        have hcbound : ∀ x ∈ T.G1 a0 (T.fund1 a1 Z), x < T.fund1 a1 Z := by
          apply Decidable.byCases (p := T.fund1 a1 Z = Z)
          · intro hcZ
            rw [hcZ]; intro x hx; rw [T.G1.eq_1] at hx; cases hx
          · intro hcZ
            apply lemma_3_4 Z (T.fund1 a1 Z) a1 a0 hSDc h1
            intro x hx
            unfold T.GZ at hx
            rw [T.G1.eq_1, List.nil_append, List.mem_singleton] at hx
            rw [hx]
            rcases T.Z_le (T.fund1 a1 Z) with hh | hh
            · exact hh
            · exact absurd hh.symm hcZ
        rw [hm, fund1_P_of_One a0 a1 (T.ofNat m) hd]
        exact ⟨(mul_isNF1_and_head a0 (T.fund1 a1 Z) hc hcbound m).1, mul_SDom a0 (T.fund1 a1 Z) a1 hSDc m⟩
      | ω =>
        have hvz : T.IsN z := (ValidArg1_ω_iff (P a0 a1 Z) z (dom1_P_of_ω a0 a1 hd)).mp hv
        have hz1 : T.ValidArg1 a1 z := (ValidArg1_ω_iff a1 z hd).mpr hvz
        obtain ⟨hc, hSDc⟩ := ih1 z has1 hz hz1
        rw [fund1_P_of_ω a0 a1 z hd]
        have hcbound : ∀ x ∈ T.G1 a0 (T.fund1 a1 z), x < T.fund1 a1 z := by
          apply Decidable.byCases (p := T.fund1 a1 z = Z)
          · intro hcZ
            rw [hcZ]; intro x hx; rw [T.G1.eq_1] at hx; cases hx
          · intro hcZ
            apply lemma_3_4 z (T.fund1 a1 z) a1 a0 hSDc h1
            intro x hx
            unfold T.GZ at hx
            rw [List.mem_append] at hx
            rcases hx with hx | hx
            · have hxZ : x = Z := IsN_G1_eq_Z z hvz a0 x hx
              rw [hxZ]
              rcases T.Z_le (T.fund1 a1 z) with hh | hh
              · exact hh
              · exact absurd hh.symm hcZ
            · rw [List.mem_singleton] at hx
              rw [hx]
              rcases T.Z_le (T.fund1 a1 z) with hh | hh
              · exact hh
              · exact absurd hh.symm hcZ
        exact ⟨T.isNF1.p a0 (T.fund1 a1 z) Z hc T.isNF1.z hcbound (T.Z_le (P a0 (T.fund1 a1 z) Z)),
          SDom_wrap z (T.fund1 a1 z) a1 a0 hSDc⟩
      | Ω l =>
        apply Decidable.byCases (p := a0 ≤ l)
        · intro hle
          have hdom : T.dom1 (P a0 a1 Z) = Dom1.ω := by
            rw [dom1_P_of_Ω a0 a1 l hd, ite_eq_left hle]
          obtain ⟨n, hn⟩ := IsN_exists_ofNat ((ValidArg1_ω_iff _ z hdom).mp hv)
          rw [hn, fund1_P_of_Ω_le a0 a1 (T.ofNat n) l hd hle]
          have hi := iteration_master a1 a0 l hle hd h1
            (fun t ht hvt => ih1 t has1 ht hvt) n
          exact ⟨T.isNF1.p a0 _ Z hi.2.1 T.isNF1.z hi.2.2.1 (T.Z_le _), hi.2.2.2⟩
        · intro hle
          have hdomeq : T.dom1 (P a0 a1 Z) = Dom1.Ω l := by
            rw [dom1_P_of_Ω a0 a1 l hd, ite_eq_right hle]
          have hvz : T.index_Prop1 l z := (ValidArg1_Ω_iff (P a0 a1 Z) z l hdomeq).mp hv
          have hz1 : T.ValidArg1 a1 z := (ValidArg1_Ω_iff a1 z l hd).mpr hvz
          obtain ⟨hc, hSDc⟩ := ih1 z has1 hz hz1
          rw [fund1_P_of_Ω_gt a0 a1 z l hd hle]
          have hcbound : ∀ x ∈ T.G1 a0 (T.fund1 a1 z), x < T.fund1 a1 z := by
            apply Decidable.byCases (p := T.fund1 a1 z = Z)
            · intro hcZ
              rw [hcZ]; intro x hx; rw [T.G1.eq_1] at hx; cases hx
            · intro hcZ
              apply lemma_3_4 z (T.fund1 a1 z) a1 a0 hSDc h1
              intro x hx
              unfold T.GZ at hx
              rw [index_Prop1_G1_empty l z hvz a0 (Nat.lt_of_not_le hle), List.nil_append,
                  List.mem_singleton] at hx
              rw [hx]
              rcases T.Z_le (T.fund1 a1 z) with hh | hh
              · exact hh
              · exact absurd hh.symm hcZ
          exact ⟨T.isNF1.p a0 (T.fund1 a1 z) Z hc T.isNF1.z hcbound (T.Z_le (P a0 (T.fund1 a1 z) Z)),
            SDom_wrap z (T.fund1 a1 z) a1 a0 hSDc⟩
    | P a20 a21 a22 =>
      obtain ⟨has1, has2, h1, h2⟩ := T.isNF1_P_inv a0 a1 (P a20 a21 a22) ha
      have hv' : T.ValidArg1 (P a20 a21 a22) z := (T.ValidArg1_tail_iff a0 a1 a20 a21 a22 z).mp hv
      obtain ⟨hc, hSDc⟩ := ih2 z has2 hz hv'
      rw [fund1_P_tail a0 a1 z a20 a21 a22]
      have hfall : T.fund1 (P a20 a21 a22) z < P a20 a21 a22 :=
        T.fund1_fall (P a20 a21 a22) z hv'
      have hheadle : T.head (T.fund1 (P a20 a21 a22) z) ≤ P a0 a1 Z :=
        partial_order.trans (T.head (T.fund1 (P a20 a21 a22) z)) (T.head (P a20 a21 a22)) (P a0 a1 Z)
          (T.head_mono hfall) h2
      exact ⟨T.isNF1.p a0 a1 (T.fund1 (P a20 a21 a22) z) has1 hc h1 hheadle,
        SDom_tail z (T.fund1 (P a20 a21 a22) z) (P a20 a21 a22) a0 a1 hSDc⟩

theorem T.fund1_NF1_closed (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t) (hv : T.ValidArg1 s t) :
    T.isNF1 (T.fund1 s t) :=
  (master s t hs ht hv).1

def T.NF1 := { s : T // T.isNF1 s }

namespace Rank1Termination

def W : Nat → T → Prop
| u, a => ∀ X : T → Prop,
    (∀ b, T.index_Prop1 u b →
      (b = Z ∨
        ((T.dom1 b = .One ∨ T.dom1 b = .ω) ∧
          ∀ z, T.ValidArg1 b z → X (T.fund1 b z)) ∨
        (∃ m, ∃ _hm : m < u, T.dom1 b = .Ω m ∧
          ∀ z, T.ValidArg1 b z → W m z → X (T.fund1 b z))) → X b) → X a

def A (u : Nat) (X : T → Prop) (a : T) : Prop :=
  T.index_Prop1 u a ∧
    (a = Z ∨
      ((T.dom1 a = .One ∨ T.dom1 a = .ω) ∧
        ∀ z, T.ValidArg1 a z → X (T.fund1 a z)) ∨
      (∃ m, ∃ _hm : m < u, T.dom1 a = .Ω m ∧
        ∀ z, T.ValidArg1 a z → W m z → X (T.fund1 a z)))

theorem W_ind (u : Nat) (X : T → Prop) (h : ∀ a, A u X a → X a)
    (a : T) (ha : W u a) : X a := by
  unfold W at ha
  exact ha X (fun b hi hb => h b ⟨hi, hb⟩)

theorem A_mono (u : Nat) (X Y : T → Prop) (h : ∀ a, X a → Y a)
    (a : T) (ha : A u X a) : A u Y a := by
  refine ⟨ha.1, ?_⟩
  exact match ha.2 with
  | Or.inl he => by
    exact Or.inl he
  | Or.inr (Or.inl ⟨hd, hf⟩) => by
    exact Or.inr (Or.inl ⟨hd, fun z hz => h _ (hf z hz)⟩)
  | Or.inr (Or.inr ⟨m, hm, hd, hf⟩) => by
    exact Or.inr (Or.inr ⟨m, hm, hd, fun z hz hw => h _ (hf z hz hw)⟩)

theorem W_intro (u : Nat) (a : T) (ha : A u (W u) a) : W u a := by
  unfold W
  intro X hX
  have hm := A_mono u (W u) X (fun b hb => W_ind u X
    (fun c hc => hX c hc.1 hc.2) b hb) a ha
  exact hX a hm.1 hm.2

theorem W_index (u : Nat) (a : T) (ha : W u a) : T.index_Prop1 u a :=
  W_ind u (T.index_Prop1 u) (fun _ h => h.1) a ha

theorem W_zero (u : Nat) : W u Z := W_intro u Z ⟨.z, Or.inl rfl⟩

theorem index_mono {u v : Nat} (huv : u ≤ v) (a : T)
    (ha : T.index_Prop1 u a) : T.index_Prop1 v a := by
  induction ha with
  | z => exact .z
  | p a0 a1 a2 hi _ ih => exact .p a0 a1 a2 (Nat.le_trans hi huv) ih

theorem A_level {u v : Nat} (huv : u ≤ v) (X : T → Prop) (a : T)
    (ha : A u X a) : A v X a := by
  refine ⟨index_mono huv a ha.1, ?_⟩
  exact match ha.2 with
  | Or.inl he => by
    exact Or.inl he
  | Or.inr (Or.inl hn) => by
    exact Or.inr (Or.inl hn)
  | Or.inr (Or.inr ⟨m, hm, hd, hf⟩) => by
    exact Or.inr (Or.inr ⟨m, Nat.lt_of_lt_of_le hm huv, hd, hf⟩)

theorem W_mono {u v : Nat} (huv : u ≤ v) (a : T) (ha : W u a) : W v a :=
  W_ind u (W v) (fun b hb => W_intro v b (A_level huv (W v) b hb)) a ha

theorem W_nat (u : Nat) (a : T) (hi : T.index_Prop1 u a)
    (hd : T.dom1 a = .One ∨ T.dom1 a = .ω)
    (hf : ∀ z, T.ValidArg1 a z → W u (T.fund1 a z)) : W u a :=
  W_intro u a ⟨hi, Or.inr (Or.inl ⟨hd, hf⟩)⟩

theorem W_omega (u m : Nat) (hm : m < u) (a : T) (hi : T.index_Prop1 u a)
    (hd : T.dom1 a = .Ω m)
    (hf : ∀ z, T.ValidArg1 a z → W m z → W u (T.fund1 a z)) : W u a :=
  W_intro u a ⟨hi, Or.inr (Or.inr ⟨m, hm, hd, hf⟩)⟩

theorem index_add (u : Nat) (a b : T) (ha : T.index_Prop1 u a)
    (hb : T.index_Prop1 u b) : T.index_Prop1 u (T.add a b) := by
  induction ha with
  | z => exact hb
  | p a0 a1 a2 hi _ ih =>
    rw [T.P_add_eq]
    exact .p a0 a1 _ hi ih

theorem dom_add (a : T) (b0 : Nat) (b1 b2 : T) :
    T.dom1 (T.add a (P b0 b1 b2)) = T.dom1 (P b0 b1 b2) := by
  induction a with
  | Z => rfl
  | P a0 a1 a2 _ ih =>
    rw [T.P_add_eq]
    obtain ⟨c0, c1, c2, hc⟩ := T.exists_add_eq_P a2 b0 b1 b2
    rw [hc, dom1_P_tail, ← hc]
    exact ih

theorem fund_add (a : T) (b0 : Nat) (b1 b2 z : T) :
    T.fund1 (T.add a (P b0 b1 b2)) z = T.add a (T.fund1 (P b0 b1 b2) z) := by
  induction a with
  | Z => rfl
  | P a0 a1 a2 _ ih =>
    rw [T.P_add_eq, T.P_add_eq]
    obtain ⟨c0, c1, c2, hc⟩ := T.exists_add_eq_P a2 b0 b1 b2
    rw [hc, fund1_P_tail, ← hc, ih]

theorem A_add (u : Nat) (X : T → Prop) (a : T) (b0 : Nat) (b1 b2 : T)
    (ha : T.index_Prop1 u a) (hb : A u (fun b => X (T.add a b)) (P b0 b1 b2)) :
    A u X (T.add a (P b0 b1 b2)) := by
  refine ⟨index_add u a _ ha hb.1, ?_⟩
  have hv : ∀ z, T.ValidArg1 (T.add a (P b0 b1 b2)) z → T.ValidArg1 (P b0 b1 b2) z := by
    intro z hz
    unfold T.ValidArg1 at hz ⊢
    rw [dom_add] at hz
    exact hz
  exact match hb.2 with
  | Or.inl he => by
    cases he
  | Or.inr (Or.inl ⟨hd, hf⟩) => by
    refine Or.inr (Or.inl ⟨?_, ?_⟩)
    · rw [dom_add]; exact hd
    · intro z hz; rw [fund_add]; exact hf z (hv z hz)
  | Or.inr (Or.inr ⟨m, hm, hd, hf⟩) => by
    refine Or.inr (Or.inr ⟨m, hm, ?_, ?_⟩)
    · rw [dom_add]; exact hd
    · intro z hz hw; rw [fund_add]; exact hf z (hv z hz) hw

theorem add_closed (u : Nat) (X : T → Prop) (hX : ∀ b, A u X b → X b)
    (a : T) (hi : T.index_Prop1 u a) (ha : X a) :
    ∀ b, A u (fun b => X (T.add a b)) b → X (T.add a b) := by
  intro b hb
  cases b with
  | Z => rw [T.add_Z]; exact ha
  | P b0 b1 b2 => exact hX _ (A_add u X a b0 b1 b2 hi hb)

theorem W_add (u : Nat) (a b : T) (ha : W u a) (hb : W u b) : W u (T.add a b) :=
  W_ind u (fun b => W u (T.add a b))
    (add_closed u (W u) (W_intro u) a (W_index u a ha) ha) b hb

theorem W_mul (u : Nat) (a : T) (ha : W u a) (n : T) (hn : T.IsN n) :
    W u (T.mul a n) := by
  induction hn with
  | zero => exact W_zero u
  | succ n _ ih => exact W_add u _ a ih ha

theorem W_base (u : Nat) : W u (P u Z Z) := by
  cases u with
  | zero =>
    exact W_nat 0 _ (.p 0 Z Z (Nat.le_refl 0) .z) (Or.inl rfl)
      (fun _ _ => W_zero 0)
  | succ u =>
    exact W_omega (u+1) u (Nat.lt_succ_self u) _ (.p _ Z Z (Nat.le_refl _) .z) rfl
      (fun z _ hz => W_mono (Nat.le_succ u) z hz)

theorem collapse_closed (v : Nat) :
    ∀ b, A v (fun b => ∀ q, q < v → W q (P q b Z)) b →
      ∀ q, q < v → W q (P q b Z) := by
  intro b hb q hq
  exact match hb.2 with
  | Or.inl he => by
    rw [he]; exact W_base q
  | Or.inr (Or.inl ⟨hd, hf⟩) => by
    rcases hd with hd | hd
    · have hp := dom1_P_of_One q b hd
      apply W_nat q _ (.p _ _ _ (Nat.le_refl q) .z) (Or.inr hp)
      intro z hz
      rw [fund1_P_of_One q b z hd]
      exact W_mul q _ (hf Z ((ValidArg1_One_iff b Z hd).mpr rfl) q hq)
        z ((ValidArg1_ω_iff _ z hp).mp hz)
    · have hp := dom1_P_of_ω q b hd
      apply W_nat q _ (.p _ _ _ (Nat.le_refl q) .z) (Or.inr hp)
      intro z hz
      rw [fund1_P_of_ω q b z hd]
      exact hf z ((ValidArg1_ω_iff b z hd).mpr ((ValidArg1_ω_iff _ z hp).mp hz)) q hq
  | Or.inr (Or.inr ⟨m, hm, hd, hf⟩) => by
    apply Decidable.byCases (p := q ≤ m)
    · intro hqm
      have hp : T.dom1 (P q b Z) = .ω := by
        rw [dom1_P_of_Ω q b m hd, ite_eq_left hqm]
      apply W_nat q _ (.p _ _ _ (Nat.le_refl q) .z) (Or.inr hp)
      intro z hz
      have hn := (ValidArg1_ω_iff _ z hp).mp hz
      have hw : W m (T.iter (fun x => P m (T.fund1 b x) Z) z) := by
        clear hz
        induction hn with
        | zero => exact W_zero m
        | succ z _ ih =>
          exact hf _ ((ValidArg1_Ω_iff b _ m hd).mpr (W_index m _ ih)) ih m hm
      rw [fund1_P_of_Ω_le q b z m hd hqm]
      exact hf _ ((ValidArg1_Ω_iff b _ m hd).mpr (W_index m _ hw)) hw q hq
    · intro hqm
      have hp : T.dom1 (P q b Z) = .Ω m := by
        rw [dom1_P_of_Ω q b m hd, ite_eq_right hqm]
      apply W_omega q m (Nat.lt_of_not_le hqm) _ (.p _ _ _ (Nat.le_refl q) .z) hp
      intro z hz hw
      rw [fund1_P_of_Ω_gt q b z m hd hqm]
      exact hf z ((ValidArg1_Ω_iff b z m hd).mpr ((ValidArg1_Ω_iff _ z m hp).mp hz)) hw q hq

theorem add_assoc (a b c : T) : T.add (T.add a b) c = T.add a (T.add b c) := by
  induction a with
  | Z => rfl
  | P a0 a1 a2 _ ih => rw [T.P_add_eq, T.P_add_eq, T.P_add_eq, ih]

theorem append_collapse_closed (v : Nat) (X : T → Prop)
    (hi : ∀ a, X a → T.index_Prop1 v a) (hX : ∀ a, A v X a → X a) :
    ∀ b, A v (fun b => ∀ a, X a → X (T.add a (P v b Z))) b →
      ∀ a, X a → X (T.add a (P v b Z)) := by
  intro b hb a ha
  have hp : ∀ h : A v (fun b => X (T.add a b)) (P v b Z), X (T.add a (P v b Z)) :=
    fun h => hX _ (A_add v X a v b Z (hi a ha) h)
  have idx : T.index_Prop1 v (P v b Z) := .p _ _ _ (Nat.le_refl v) .z
  exact match hb.2 with
  | Or.inl he => by
    subst b
    cases v with
    | zero =>
      apply hp
      exact ⟨idx, Or.inr (Or.inl ⟨Or.inl rfl, fun _ _ => by
        change X (T.add a Z)
        rw [T.add_Z]; exact ha⟩)⟩
    | succ v =>
      apply hp
      refine ⟨idx, Or.inr (Or.inr ⟨v, Nat.lt_succ_self v, rfl, ?_⟩)⟩
      intro z _ hz
      exact W_ind (v+1) (fun z => X (T.add a z))
        (add_closed (v+1) X hX a (hi a ha) ha) z (W_mono (Nat.le_succ v) z hz)
  | Or.inr (Or.inl ⟨hd, hf⟩) => by
    rcases hd with hd | hd
    · have hdom := dom1_P_of_One v b hd
      apply hp
      refine ⟨idx, Or.inr (Or.inl ⟨Or.inr hdom, ?_⟩)⟩
      intro z hz
      rw [fund1_P_of_One v b z hd]
      have hn := (ValidArg1_ω_iff _ z hdom).mp hz
      have hstep := hf Z ((ValidArg1_One_iff b Z hd).mpr rfl)
      clear hz
      induction hn with
      | zero => rw [T.mul.eq_1, T.add_Z]; exact ha
      | succ z _ ih =>
        change X (T.add a (T.add (T.mul (P v (T.fund1 b Z) Z) z) (P v (T.fund1 b Z) Z)))
        rw [← add_assoc]
        exact hstep _ ih
    · have hdom := dom1_P_of_ω v b hd
      apply hp
      refine ⟨idx, Or.inr (Or.inl ⟨Or.inr hdom, ?_⟩)⟩
      intro z hz
      rw [fund1_P_of_ω v b z hd]
      exact hf z ((ValidArg1_ω_iff b z hd).mpr ((ValidArg1_ω_iff _ z hdom).mp hz)) a ha
  | Or.inr (Or.inr ⟨m, hm, hd, hf⟩) => by
    have hn : ¬ v ≤ m := Nat.not_le_of_gt hm
    have hdom : T.dom1 (P v b Z) = .Ω m := by
      rw [dom1_P_of_Ω v b m hd, ite_eq_right hn]
    apply hp
    refine ⟨idx, Or.inr (Or.inr ⟨m, hm, hdom, ?_⟩)⟩
    intro z hz hw
    rw [fund1_P_of_Ω_gt v b z m hd hn]
    exact hf z ((ValidArg1_Ω_iff b z m hd).mpr ((ValidArg1_Ω_iff _ z m hdom).mp hz)) hw a ha

theorem exists_level (a : T) : ∃ v, ∀ u, v ≤ u → W u a := by
  induction a with
  | Z => exact ⟨0, fun u _ => W_zero u⟩
  | P a0 a1 a2 ih1 ih2 =>
    obtain ⟨v1, hv1⟩ := ih1
    obtain ⟨v2, hv2⟩ := ih2
    refine ⟨a0 + v1 + v2, ?_⟩
    intro u hu
    have ha0 : a0 ≤ u := Nat.le_trans
      (Nat.le_trans (Nat.le_add_right a0 v1) (Nat.le_add_right (a0+v1) v2)) hu
    have hv1u : v1 ≤ u := Nat.le_trans
      (Nat.le_trans (Nat.le_add_left v1 a0) (Nat.le_add_right (a0+v1) v2)) hu
    have hv2u : v2 ≤ u := Nat.le_trans (Nat.le_add_left v2 (a0+v1)) hu
    have hp : W u (P a0 a1 Z) := by
      rcases Nat.lt_or_eq_of_le ha0 with hlt | heq
      · have hs := W_ind u (fun b => ∀ q, q < u → W q (P q b Z))
          (collapse_closed u) a1 (hv1 u hv1u)
        exact W_mono ha0 _ (hs a0 hlt)
      · rw [heq]
        let X := fun b => W u b ∧ T.index_Prop1 u b
        have hX : ∀ b, A u X b → X b :=
          fun b hb => ⟨W_intro u b (A_mono u X (W u) (fun _ h => h.1) b hb), hb.1⟩
        have hm := W_ind u (fun b => ∀ c, X c → X (T.add c (P u b Z)))
          (append_collapse_closed u X (fun _ h => h.2) hX) a1 (hv1 u hv1u)
        exact (hm Z ⟨W_zero u, .z⟩).1
    have hsum := W_add u _ a2 hp (hv2 u hv2u)
    rw [T.P_add_eq] at hsum
    exact hsum

theorem W_all (u : Nat) (a : T) (hi : T.index_Prop1 u a) : W u a := by
  induction hi with
  | z => exact W_zero u
  | p a0 a1 a2 h0 _ ih =>
    obtain ⟨v, hv⟩ := exists_level a1
    have hs := W_ind (v+a0+1) (fun b => ∀ q, q < v+a0+1 → W q (P q b Z))
      (collapse_closed (v+a0+1)) a1
      (hv (v+a0+1) (Nat.le_trans (Nat.le_add_right v a0) (Nat.le_succ (v+a0))))
    have hlt : a0 < v+a0+1 := Nat.lt_succ_of_le (Nat.le_add_left a0 v)
    have hsum := W_add u _ a2 (W_mono h0 _ (hs a0 hlt)) ih
    rw [T.P_add_eq] at hsum
    exact hsum

end Rank1Termination

theorem dom1_Ω_head (a : T) (ha : T.isNF1 a) (l : Nat) (hd : T.dom1 a = .Ω l) :
    ∃ i s t, a = P i s t ∧ l < i := by
  induction a with
  | Z => cases hd
  | P i s t ihs iht =>
    obtain ⟨hs, ht, _, hh⟩ := T.isNF1_P_inv i s t ha
    refine ⟨i, s, t, rfl, ?_⟩
    cases t with
    | Z =>
      cases he : T.dom1 s with
      | Zero =>
        cases i with
        | zero => rw [dom1_P0_of_Zero s he] at hd; cases hd
        | succ i =>
          rw [dom1_Psucc_of_Zero i s he] at hd
          cases hd
          exact Nat.lt_succ_self l
      | One => rw [dom1_P_of_One i s he] at hd; cases hd
      | ω => rw [dom1_P_of_ω i s he] at hd; cases hd
      | Ω m =>
        rw [dom1_P_of_Ω i s m he] at hd
        apply Decidable.byCases (p := i ≤ m)
        · intro him
          rw [ite_eq_left him] at hd; cases hd
        · intro him
          rw [ite_eq_right him] at hd
          cases hd
          exact Nat.lt_of_not_le him
    | P j b c =>
      rw [dom1_P_tail] at hd
      obtain ⟨j', b', c', he, hj⟩ := iht ht hd
      cases he
      change P j b Z ≤ P i s Z at hh
      rcases hh with hh | hh
      · exact match lt_inv j b Z i s Z hh with
        | Or.inl hij => by
          exact Nat.lt_trans hj hij
        | Or.inr (Or.inl ⟨hij, _⟩) => by
          rw [← hij]; exact hj
        | Or.inr (Or.inr ⟨hij, _, _⟩) => by
          rw [← hij]; exact hj
      · cases hh
        exact hj

theorem fund1_Ω_arg_le (a : T) (ha : T.isNF1 a) (l : Nat) (hd : T.dom1 a = .Ω l)
    (z : T) (hz : T.index_Prop1 l z) : z ≤ T.fund1 a z := by
  obtain ⟨i, s, t, he, hi⟩ := dom1_Ω_head a ha l hd
  subst a
  have hsmall : ∀ b c, z < P i b c := by
    intro b c
    cases hz with
    | z => exact .Z_lt_P i b c
    | p j x y hj _ => exact .p_head j i x b y c (Nat.lt_of_le_of_lt hj hi)
  cases t with
  | P j b c => rw [fund1_P_tail]; exact Or.inl (hsmall _ _)
  | Z =>
    cases hs : T.dom1 s with
    | Zero =>
      cases i with
      | zero => exact False.elim (Nat.not_lt_zero l hi)
      | succ i => rw [fund1_Psucc_of_Zero i s z hs]; exact Or.inr rfl
    | One => rw [dom1_P_of_One i s hs] at hd; cases hd
    | ω => rw [dom1_P_of_ω i s hs] at hd; cases hd
    | Ω m =>
      apply Decidable.byCases (p := i ≤ m)
      · intro him
        rw [dom1_P_of_Ω i s m hs, ite_eq_left him] at hd; cases hd
      · intro him
        rw [fund1_P_of_Ω_gt i s z m hs him]; exact Or.inl (hsmall _ _)

def cutBound (l : Nat) (z : T) : T → Prop
| Z => Z < z
| P i s t => if i ≤ l then P i s t < z else cutBound l z s ∧ cutBound l z t

theorem cutBound_mono (l : Nat) (z w b : T) (hzw : z ≤ w) (hb : cutBound l z b) :
    cutBound l w b := by
  induction b with
  | Z => exact lt_of_lt_of_le_thm T Z z w hb hzw
  | P i s t ihs iht =>
    unfold cutBound at hb ⊢
    apply Decidable.byCases (p := i ≤ l)
    · intro hi
      rw [ite_eq_left hi] at hb ⊢
      exact lt_of_lt_of_le_thm T _ z w hb hzw
    · intro hi
      rw [ite_eq_right hi] at hb ⊢
      exact ⟨ihs hb.1, iht hb.2⟩

theorem fund1_Ω_above (a : T) (ha : T.isNF1 a) (l : Nat) (hd : T.dom1 a = .Ω l)
    (z : T) (hz : T.index_Prop1 l z) :
    ∀ b, T.isNF1 b → b < a → cutBound l z b → b < T.fund1 a z := by
  induction a with
  | Z => cases hd
  | P i s t ihs iht =>
    intro b hb hba hcut
    obtain ⟨hs, ht, _, _⟩ := T.isNF1_P_inv i s t ha
    cases b with
    | Z => exact lt_of_lt_of_le_thm T Z z _ hcut (fund1_Ω_arg_le _ ha l hd z hz)
    | P j x y =>
      apply Decidable.byCases (p := j ≤ l)
      · intro hj
        change (if j ≤ l then P j x y < z else _) at hcut
        rw [ite_eq_left hj] at hcut
        exact lt_of_lt_of_le_thm T _ z _ hcut (fund1_Ω_arg_le _ ha l hd z hz)
      · intro hj
        change (if j ≤ l then _ else cutBound l z x ∧ cutBound l z y) at hcut
        rw [ite_eq_right hj] at hcut
        obtain ⟨hx, hy, _, _⟩ := T.isNF1_P_inv j x y hb
        cases t with
        | P t0 t1 t2 =>
          rw [fund1_P_tail]
          rw [dom1_P_tail] at hd
          exact match lt_inv j x y i s (P t0 t1 t2) hba with
          | Or.inl h => by
            exact .p_head j i x s y _ h
          | Or.inr (Or.inl ⟨h, hxs⟩) => by
            subst j; exact .p_mid i x s y _ hxs
          | Or.inr (Or.inr ⟨h, hxs, hyt⟩) => by
            subst j; subst x
            exact .p_tail i s y _ (iht ht hd y hy hyt hcut.2)
        | Z =>
          cases he : T.dom1 s with
          | Zero =>
            cases i with
            | zero => rw [dom1_P0_of_Zero s he] at hd; cases hd
            | succ i =>
              rw [dom1_Psucc_of_Zero i s he] at hd
              cases hd
              have hsz := dom1_Zero_imp_eq_Z s he
              subst s
              exact match lt_inv j x y (l+1) Z Z hba with
              | Or.inl h => by
                exact False.elim (hj (Nat.le_of_lt_succ h))
              | Or.inr (Or.inl ⟨_, h⟩) => by
                exact False.elim (lt_Z_inv h)
              | Or.inr (Or.inr ⟨_, _, h⟩) => by
                exact False.elim (lt_Z_inv h)
          | One => rw [dom1_P_of_One i s he] at hd; cases hd
          | ω => rw [dom1_P_of_ω i s he] at hd; cases hd
          | Ω m =>
            apply Decidable.byCases (p := i ≤ m)
            · intro him
              rw [dom1_P_of_Ω i s m he, ite_eq_left him] at hd; cases hd
            · intro him
              rw [dom1_P_of_Ω i s m he, ite_eq_right him] at hd
              cases hd
              rw [fund1_P_of_Ω_gt i s z l he him]
              exact match lt_inv j x y i s Z hba with
              | Or.inl h => by
                exact .p_head j i x _ y Z h
              | Or.inr (Or.inl ⟨h, hxs⟩) => by
                subst j
                exact .p_mid i x _ y Z (ihs hs he x hx hxs hcut.1)
              | Or.inr (Or.inr ⟨_, _, h⟩) => by
                exact False.elim (lt_Z_inv h)

theorem G1_size_lt (l : Nat) (b : T) : ∀ x ∈ T.G1 l b, x.size < b.size := by
  induction b with
  | Z => intro x hx; cases hx
  | P i s t ihs iht =>
    intro x hx
    have hs : s.size < (P i s t).size :=
      Nat.lt_succ_of_le (Nat.le_add_right s.size t.size)
    have ht : t.size < (P i s t).size :=
      Nat.lt_succ_of_le (Nat.le_add_left t.size s.size)
    apply Decidable.byCases (p := l ≤ i)
    · intro hi
      rw [T.G1.eq_2, ite_eq_left hi, List.mem_append, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · rw [List.mem_singleton] at hx; rw [hx]; exact hs
      · exact Nat.lt_trans (ihs x hx) hs
      · exact Nat.lt_trans (iht x hx) ht
    · intro hi
      rw [T.G1.eq_2, ite_eq_right hi] at hx
      exact Nat.lt_trans (iht x hx) ht

theorem iter_cutBound (a : T) (l : Nat) (hd : T.dom1 a = .Ω l)
    (b : T) (hb : T.isNF1 b)
    (happrox : ∀ x ∈ T.G1 l b, T.isNF1 x → (∀ y ∈ T.G1 l x, y < x) →
      ∃ n, x < T.fund1 a (T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat n))) :
    ∃ n, cutBound l (T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat n)) b := by
  have hmono : ∀ n m, n < m →
      T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat n) <
      T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat m) :=
    fun n m h => iter_F_strict_mono_ofNat a l hd
      (fun t0 t1 h ht0 ht1 => T.fund1_strict_mono_dec a t0 t1 h ht0 ht1) m n h
  induction b with
  | Z => exact ⟨1, T.Lt.Z_lt_P l _ Z⟩
  | P i s t ihs iht =>
    obtain ⟨hs, ht, hgs, _⟩ := T.isNF1_P_inv i s t hb
    apply Decidable.byCases (p := i < l)
    · intro hil
      refine ⟨1, ?_⟩
      unfold cutBound
      rw [ite_eq_left (Nat.le_of_lt hil)]
      exact .p_head i l s _ t Z hil
    · intro hil
      have hli := Nat.le_of_not_lt hil
      have hmem : ∀ x, x ∈ T.G1 l s → x ∈ T.G1 l (P i s t) := by
        intro x hx
        rw [T.G1.eq_2, ite_eq_left hli]
        exact List.mem_append_left _ (List.mem_append_right _ hx)
      apply Decidable.byCases (p := i = l)
      · intro hei
        subst i
        have hsmem : s ∈ T.G1 l (P l s t) := by
          rw [T.G1.eq_2, ite_eq_left (Nat.le_refl l)]
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self s))
        obtain ⟨n, hn⟩ := happrox s hsmem hs hgs
        refine ⟨n+1, ?_⟩
        unfold cutBound
        rw [ite_eq_left (Nat.le_refl l)]
        exact .p_mid l s _ t Z hn
      · intro hei
        have hin : ¬ i ≤ l := fun h => hei (Nat.le_antisymm h hli)
        obtain ⟨n, hn⟩ := ihs hs (fun x hx => happrox x (hmem x hx))
        have hmemt : ∀ x, x ∈ T.G1 l t → x ∈ T.G1 l (P i s t) := by
          intro x hx
          rw [T.G1.eq_2, ite_eq_left hli]
          exact List.mem_append_right _ hx
        obtain ⟨m, hm⟩ := iht ht (fun x hx => happrox x (hmemt x hx))
        refine ⟨n+m+1, ?_⟩
        unfold cutBound
        rw [ite_eq_right hin]
        exact ⟨cutBound_mono l _ _ s (Or.inl (hmono n _
          (Nat.lt_succ_of_le (Nat.le_add_right n m)))) hn,
          cutBound_mono l _ _ t (Or.inl (hmono m _
          (Nat.lt_succ_of_le (Nat.le_add_left m n)))) hm⟩

theorem iteration_cofinal (a : T) (ha : T.isNF1 a) (l : Nat) (hd : T.dom1 a = .Ω l) :
    ∀ b, T.isNF1 b → b < a → (∀ x ∈ T.G1 l b, x < b) →
      ∃ n, b < T.fund1 a (T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat n)) := by
  intro b
  have main : ∀ n, ∀ b, b.size = n → T.isNF1 b → b < a →
      (∀ x ∈ T.G1 l b, x < b) →
      ∃ n, b < T.fund1 a (T.iter (fun z => P l (T.fund1 a z) Z) (T.ofNat n)) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro b he hb hba hgb
      obtain ⟨m, hm⟩ := iter_cutBound a l hd b hb (by
        intro x hx hnx hgx
        have hsize := G1_size_lt l b x hx
        rw [he] at hsize
        exact ih x.size hsize x rfl hnx (lt_trans_thm x b a (hgb x hx) hba) hgx)
      exact ⟨m, fund1_Ω_above a ha l hd _
        (iter_index_Prop1 l _ (fun z => ⟨T.fund1 a z, rfl⟩) (T.ofNat m)) b hb hba hm⟩
  exact main b.size b rfl

theorem dom1_One_PZ (i : Nat) (s : T) (hd : T.dom1 (P i s Z) = .One) :
    i = 0 ∧ s = Z := by
  cases hs : T.dom1 s with
  | Zero =>
    have he := dom1_Zero_imp_eq_Z s hs
    cases i with
    | zero => exact ⟨rfl, he⟩
    | succ i => rw [dom1_Psucc_of_Zero i s hs] at hd; cases hd
  | One => rw [dom1_P_of_One i s hs] at hd; cases hd
  | ω => rw [dom1_P_of_ω i s hs] at hd; cases hd
  | Ω l =>
    rw [dom1_P_of_Ω i s l hs] at hd
    apply Decidable.byCases (p := i ≤ l)
    · intro hi
      rw [ite_eq_left hi] at hd; cases hd
    · intro hi
      rw [ite_eq_right hi] at hd; cases hd

theorem fund1_One_const (a : T) (hd : T.dom1 a = .One) (z : T) :
    T.fund1 a z = T.fund1 a Z := by
  induction a with
  | Z => cases hd
  | P i s t _ iht =>
    cases t with
    | Z =>
      obtain ⟨hi, hs⟩ := dom1_One_PZ i s hd
      rw [hi, hs]
      rfl
    | P j b c =>
      rw [dom1_P_tail] at hd
      rw [fund1_P_tail, fund1_P_tail, iht hd]

theorem fund1_One_upper (a : T) (hd : T.dom1 a = .One) :
    ∀ b, b < a → b ≤ T.fund1 a Z := by
  induction a with
  | Z => cases hd
  | P i s t _ iht =>
    intro b hba
    cases t with
    | Z =>
      obtain ⟨hi, hs⟩ := dom1_One_PZ i s hd
      subst i; subst s
      cases b with
      | Z => exact Or.inr rfl
      | P j x y =>
        exact match lt_inv j x y 0 Z Z hba with
        | Or.inl h => by
          exact False.elim (Nat.not_lt_zero j h)
        | Or.inr (Or.inl ⟨_, h⟩) => by
          exact False.elim (lt_Z_inv h)
        | Or.inr (Or.inr ⟨_, _, h⟩) => by
          exact False.elim (lt_Z_inv h)
    | P j x y =>
      rw [dom1_P_tail] at hd
      rw [fund1_P_tail]
      cases b with
      | Z => exact T.Z_le _
      | P k c d =>
        exact match lt_inv k c d i s (P j x y) hba with
        | Or.inl h => by
          exact Or.inl (.p_head k i c s d _ h)
        | Or.inr (Or.inl ⟨h, hcs⟩) => by
          subst k; exact Or.inl (.p_mid i c s d _ hcs)
        | Or.inr (Or.inr ⟨h, hcs, hdt⟩) => by
          subst k; subst c
          rcases iht hd d hdt with h | h
          · exact Or.inl (.p_tail i s d _ h)
          · rw [h]; exact Or.inr rfl

theorem head_le_index (i j : Nat) (s t : T) (h : P i s Z ≤ P j t Z) : i ≤ j := by
  rcases h with h | h
  · exact match lt_inv i s Z j t Z h with
    | Or.inl h => by
      exact Nat.le_of_lt h
    | Or.inr (Or.inl ⟨h, _⟩) => by
      rw [h]; exact Nat.le_refl j
    | Or.inr (Or.inr ⟨h, _, _⟩) => by
      rw [h]; exact Nat.le_refl j
  · cases h; exact Nat.le_refl i

theorem isNF1_index (l i : Nat) (s t : T) (ha : T.isNF1 (P i s t)) (hi : i ≤ l) :
    T.index_Prop1 l (P i s t) := by
  induction t generalizing i s with
  | Z => exact .p i s Z hi .z
  | P j b c _ ih =>
    obtain ⟨_, ht, _, hh⟩ := T.isNF1_P_inv i s (P j b c) ha
    have hj := Nat.le_trans (head_le_index j i b s hh) hi
    exact .p i s _ hi (ih j b ht hj)

theorem one_le_P (i : Nat) (s : T) : P 0 Z Z ≤ P i s Z := by
  cases i with
  | zero =>
    cases s with
    | Z => exact Or.inr rfl
    | P j x y => exact Or.inl (.p_mid 0 Z _ Z Z (.Z_lt_P j x y))
  | succ i => exact Or.inl (.p_head 0 (i+1) Z s Z Z (Nat.zero_lt_succ i))

theorem isNF1_succ (a : T) (ha : T.isNF1 a) : T.isNF1 (T.add a (P 0 Z Z)) := by
  induction a with
  | Z => exact .p 0 Z Z .z .z (fun _ h => by cases h) (T.Z_le _)
  | P i s t _ iht =>
    obtain ⟨hs, ht, hg, hh⟩ := T.isNF1_P_inv i s t ha
    rw [T.P_add_eq]
    refine .p i s _ hs (iht ht) hg ?_
    cases t with
    | Z => exact one_le_P i s
    | P j x y => rw [T.P_add_eq]; exact hh

theorem cutBound_exists (l : Nat) (b : T) (hb : T.isNF1 b) :
    ∃ z, T.isNF1 z ∧ T.index_Prop1 l z ∧ cutBound l z b := by
  induction b with
  | Z => exact ⟨P 0 Z Z, isNF1_succ Z .z,
      .p 0 Z Z (Nat.zero_le l) .z, .Z_lt_P 0 Z Z⟩
  | P i s t ihs iht =>
    obtain ⟨hs, ht, _, _⟩ := T.isNF1_P_inv i s t hb
    apply Decidable.byCases (p := i ≤ l)
    · intro hi
      refine ⟨T.add (P i s t) (P 0 Z Z), isNF1_succ _ hb,
        Rank1Termination.index_add l _ _ (isNF1_index l i s t hb hi)
          (.p 0 Z Z (Nat.zero_le l) .z), ?_⟩
      unfold cutBound
      rw [ite_eq_left hi]
      exact add_lt_add_of_ne_Z _ _ (fun h => by cases h)
    · intro hi
      obtain ⟨z, hz, hiz, hsz⟩ := ihs hs
      obtain ⟨w, hw, hiw, htw⟩ := iht ht
      rcases linear_order.total z w with hzw | hwz
      · refine ⟨w, hw, hiw, ?_⟩
        unfold cutBound
        rw [ite_eq_right hi]
        exact ⟨cutBound_mono l z w s hzw hsz, htw⟩
      · refine ⟨z, hz, hiz, ?_⟩
        unfold cutBound
        rw [ite_eq_right hi]
        exact ⟨hsz, cutBound_mono l w z t hwz htw⟩

theorem mul_cofinal (i : Nat) (s : T) (b : T) (hb : T.isNF1 b)
    (hh : T.head b ≤ P i s Z) : ∃ n, b < T.mul (P i s Z) (T.ofNat n) := by
  induction b with
  | Z => exact ⟨1, T.Lt.Z_lt_P i s Z⟩
  | P j x y _ ih =>
    obtain ⟨_, hy, _, hhy⟩ := T.isNF1_P_inv j x y hb
    change P j x Z ≤ P i s Z at hh
    rcases hh with hh | hh
    · exact match lt_inv j x Z i s Z hh with
      | Or.inl h => by
        exact ⟨1, .p_head j i x s y Z h⟩
      | Or.inr (Or.inl ⟨h, hxs⟩) => by
        subst j; exact ⟨1, .p_mid i x s y Z hxs⟩
      | Or.inr (Or.inr ⟨_, _, h⟩) => by
        exact False.elim (lt_Z_inv h)
    · cases hh
      obtain ⟨n, hn⟩ := ih hy hhy
      refine ⟨n+1, ?_⟩
      rw [mul_succ_shape]
      exact .p_tail i s y _ hn

theorem fund1_ω_cofinal (a : T) (ha : T.isNF1 a) (hd : T.dom1 a = .ω) :
    ∀ b, T.isNF1 b → b < a → ∃ n, b < T.fund1 a (T.ofNat n) := by
  induction a with
  | Z => cases hd
  | P i s t ihs iht =>
    intro b hb hba
    obtain ⟨hs, ht, _, _⟩ := T.isNF1_P_inv i s t ha
    cases b with
    | Z =>
      refine ⟨1, lt_of_le_of_lt_thm T Z (T.fund1 (P i s t) Z) _ (T.Z_le _) ?_⟩
      exact T.fund1_strict_mono_dec _ Z (T.ofNat 1) (.Z_lt_P 0 Z Z)
        ((ValidArg1_ω_iff _ Z hd).mpr .zero)
        ((ValidArg1_ω_iff _ (T.ofNat 1) hd).mpr (ofNat_IsN 1))
    | P j x y =>
      obtain ⟨hx, hy, hgx, _⟩ := T.isNF1_P_inv j x y hb
      cases t with
      | P k c d =>
        rw [dom1_P_tail] at hd
        exact match lt_inv j x y i s (P k c d) hba with
        | Or.inl h => by
          refine ⟨0, ?_⟩; rw [fund1_P_tail]; exact .p_head j i x s y _ h
        | Or.inr (Or.inl ⟨h, hxs⟩) => by
          subst j
          refine ⟨0, ?_⟩; rw [fund1_P_tail]; exact .p_mid i x s y _ hxs
        | Or.inr (Or.inr ⟨h, hxs, hyt⟩) => by
          subst j; subst x
          obtain ⟨n, hn⟩ := iht ht hd y hy hyt
          refine ⟨n, ?_⟩; rw [fund1_P_tail]; exact .p_tail i s y _ hn
      | Z =>
        cases he : T.dom1 s with
        | Zero =>
          cases i with
          | zero => rw [dom1_P0_of_Zero s he] at hd; cases hd
          | succ i => rw [dom1_Psucc_of_Zero i s he] at hd; cases hd
        | One =>
          exact match lt_inv j x y i s Z hba with
          | Or.inl h => by
            refine ⟨1, ?_⟩
            rw [fund1_P_of_One i s (T.ofNat 1) he]
            exact .p_head j i x _ y Z h
          | Or.inr (Or.inl ⟨h, hxs⟩) => by
            subst j
            rcases fund1_One_upper s he x hxs with hxp | hxp
            · refine ⟨1, ?_⟩
              rw [fund1_P_of_One i s (T.ofNat 1) he]
              exact .p_mid i x _ y Z hxp
            · have hh : T.head (P i x y) ≤ P i (T.fund1 s Z) Z := by
                rw [hxp]; exact Or.inr rfl
              obtain ⟨n, hn⟩ := mul_cofinal i (T.fund1 s Z) (P i x y) hb hh
              refine ⟨n, ?_⟩
              rw [fund1_P_of_One i s (T.ofNat n) he]; exact hn
          | Or.inr (Or.inr ⟨_, _, h⟩) => by
            exact False.elim (lt_Z_inv h)
        | ω =>
          exact match lt_inv j x y i s Z hba with
          | Or.inl h => by
            refine ⟨0, ?_⟩
            rw [fund1_P_of_ω i s (T.ofNat 0) he]; exact .p_head j i x _ y Z h
          | Or.inr (Or.inl ⟨h, hxs⟩) => by
            subst j
            obtain ⟨n, hn⟩ := ihs hs he x hx hxs
            refine ⟨n, ?_⟩
            rw [fund1_P_of_ω i s (T.ofNat n) he]; exact .p_mid i x _ y Z hn
          | Or.inr (Or.inr ⟨_, _, h⟩) => by
            exact False.elim (lt_Z_inv h)
        | Ω l =>
          have hil : i ≤ l := by
            apply Decidable.byCases (p := i ≤ l)
            · intro h
              exact h
            · intro h
              rw [dom1_P_of_Ω i s l he, ite_eq_right h] at hd; cases hd
          exact match lt_inv j x y i s Z hba with
          | Or.inl h => by
            refine ⟨0, ?_⟩
            rw [fund1_P_of_Ω_le i s (T.ofNat 0) l he hil]; exact .p_head j i x _ y Z h
          | Or.inr (Or.inl ⟨h, hxs⟩) => by
            subst j
            have hgl : ∀ z ∈ T.G1 l x, z < x :=
              fun z hz => hgx z (G1_antitone i l hil x z hz)
            obtain ⟨n, hn⟩ := iteration_cofinal s hs l he x hx hxs hgl
            refine ⟨n, ?_⟩
            rw [fund1_P_of_Ω_le i s (T.ofNat n) l he hil]; exact .p_mid i x _ y Z hn
          | Or.inr (Or.inr ⟨_, _, h⟩) => by
            exact False.elim (lt_Z_inv h)

theorem IsN_isNF1 (a : T) (ha : T.IsN a) : T.isNF1 a := by
  induction ha with
  | zero => exact .z
  | succ a hn ih =>
    refine .p 0 Z a .z ih (fun _ h => by cases h) ?_
    cases hn with
    | zero => exact T.Z_le _
    | succ a _ => exact Or.inr rfl

theorem fund1_cofinal (a b : T) (ha : T.isNF1 a) (hb : T.isNF1 b) (hba : b < a) :
    ∃ z, T.isNF1 z ∧ T.ValidArg1 a z ∧ b ≤ T.fund1 a z := by
  cases hd : T.dom1 a with
  | Zero =>
    have he := dom1_Zero_imp_eq_Z a hd
    rw [he] at hba
    exact False.elim (lt_Z_inv hba)
  | One => exact ⟨Z, .z, (ValidArg1_One_iff a Z hd).mpr rfl, fund1_One_upper a hd b hba⟩
  | ω =>
    obtain ⟨n, hn⟩ := fund1_ω_cofinal a ha hd b hb hba
    exact ⟨T.ofNat n, IsN_isNF1 _ (ofNat_IsN n),
      (ValidArg1_ω_iff a _ hd).mpr (ofNat_IsN n), Or.inl hn⟩
  | Ω l =>
    obtain ⟨z, hz, hi, hc⟩ := cutBound_exists l b hb
    exact ⟨z, hz, (ValidArg1_Ω_iff a z l hd).mpr hi,
      Or.inl (fund1_Ω_above a ha l hd z hi b hb hba hc)⟩

theorem NF1_acc_of_le (a b : T.NF1)
    (ha : Acc (fun x y : T.NF1 => x.1 < y.1) a) (hba : b.1 ≤ a.1) :
    Acc (fun x y : T.NF1 => x.1 < y.1) b := by
  rcases hba with h | h
  · exact ha.inv h
  · have he : b = a := Subtype.ext h
    rw [he]
    exact ha

theorem T.well_founded_NF1 : WellFounded (fun s t : T.NF1 => s.1 < t.1) := by
  constructor
  intro a
  obtain ⟨u, hu⟩ := Rank1Termination.exists_level a.1
  have hw := hu u (Nat.le_refl u)
  apply Rank1Termination.W_ind u
    (fun b => ∀ hb : T.isNF1 b, Acc (fun s t : T.NF1 => s.1 < t.1) ⟨b, hb⟩)
    ?_ a.1 hw a.2
  intro b hg hb
  constructor
  intro c hcb
  change c.1 < b at hcb
  obtain ⟨z, hz, hv, hle⟩ := fund1_cofinal b c.1 hb c.2 hcb
  have hnf := T.fund1_NF1_closed b z hb hz hv
  have hacc : Acc (fun s t : T.NF1 => s.1 < t.1) ⟨T.fund1 b z, hnf⟩ := by
    exact match hg.2 with
    | Or.inl he => by
      rw [he] at hcb
      exact False.elim (lt_Z_inv hcb)
    | Or.inr (Or.inl ⟨_, hf⟩) => by
      exact hf z hv hnf
    | Or.inr (Or.inr ⟨m, _, hd, hf⟩) => by
      exact hf z hv (Rank1Termination.W_all m z ((ValidArg1_Ω_iff b z m hd).mp hv)) hnf
  exact NF1_acc_of_le _ c hacc hle

def T.LF1 (n : Nat) := P 0 (P n Z Z) Z

inductive T.isOT1 : T → Prop where
| base (n : Nat) : T.isOT1 (T.LF1 n)
| step (s : T) (hs : T.isOT1 s) (n : Nat) : T.isOT1 (T.fund1 s (T.ofNat n))

theorem dom1_Ω_not_countable (a : T) (ha : T.isNF1 a) (hc : a < P 1 Z Z)
    (l : Nat) : T.dom1 a ≠ .Ω l := by
  intro hd
  obtain ⟨i, s, t, he, hi⟩ := dom1_Ω_head a ha l hd
  rw [he] at hc
  exact match lt_inv i s t 1 Z Z hc with
  | Or.inl h => by
    have hz : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
    rw [hz] at hi
    exact Nat.not_lt_zero l hi
  | Or.inr (Or.inl ⟨_, h⟩) => by
    exact lt_Z_inv h
  | Or.inr (Or.inr ⟨_, _, h⟩) => by
    exact lt_Z_inv h

theorem LF1_isNF1 (n : Nat) : T.isNF1 (T.LF1 n) := by
  have hn : T.isNF1 (P n Z Z) :=
    .p n Z Z .z .z (fun _ h => by cases h) (T.Z_le _)
  refine .p 0 (P n Z Z) Z hn .z ?_ (T.Z_le _)
  intro x hx
  rw [G1_PZ_pos 0 n Z (Nat.zero_le n), T.G1.eq_1,
    List.append_nil, List.mem_singleton] at hx
  rw [hx]
  exact .Z_lt_P n Z Z

theorem isOT1_sound (a : T) (ha : T.isOT1 a) : T.isNF1 a ∧ a < P 1 Z Z := by
  induction ha with
  | base n => exact ⟨LF1_isNF1 n, .p_head 0 1 _ Z Z Z (Nat.zero_lt_succ 0)⟩
  | step a _ n ih =>
    cases hd : T.dom1 a with
    | Zero =>
      have he := dom1_Zero_imp_eq_Z a hd
      rw [he, T.fund1.eq_1]
      exact ⟨.z, .Z_lt_P 1 Z Z⟩
    | One =>
      rw [fund1_One_const a hd (T.ofNat n)]
      have hv := (ValidArg1_One_iff a Z hd).mpr rfl
      exact ⟨T.fund1_NF1_closed a Z ih.1 .z hv,
        lt_trans_thm _ a _ (T.fund1_fall a Z hv) ih.2⟩
    | ω =>
      have hv := (ValidArg1_ω_iff a (T.ofNat n) hd).mpr (ofNat_IsN n)
      exact ⟨T.fund1_NF1_closed a _ ih.1 (IsN_isNF1 _ (ofNat_IsN n)) hv,
        lt_trans_thm _ a _ (T.fund1_fall a _ hv) ih.2⟩
    | Ω l => exact False.elim (dom1_Ω_not_countable a ih.1 ih.2 l hd)

theorem fund1_countable_cofinal (a b : T) (ha : T.isNF1 a) (hb : T.isNF1 b)
    (hc : a < P 1 Z Z) (hba : b < a) :
    ∃ n, T.fund1 a (T.ofNat n) < a ∧ b ≤ T.fund1 a (T.ofNat n) := by
  cases hd : T.dom1 a with
  | Zero =>
    rw [dom1_Zero_imp_eq_Z a hd] at hba
    exact False.elim (lt_Z_inv hba)
  | One =>
    exact ⟨0, T.fund1_fall a Z ((ValidArg1_One_iff a Z hd).mpr rfl),
      fund1_One_upper a hd b hba⟩
  | ω =>
    obtain ⟨n, hn⟩ := fund1_ω_cofinal a ha hd b hb hba
    exact ⟨n, T.fund1_fall a _ ((ValidArg1_ω_iff a _ hd).mpr (ofNat_IsN n)), Or.inl hn⟩
  | Ω l => exact False.elim (dom1_Ω_not_countable a ha hc l hd)

theorem isOT1_downward (a b : T) (ha : T.isOT1 a) (hb : T.isNF1 b) (hba : b ≤ a) :
    T.isOT1 b := by
  have main : ∀ a : T.NF1, T.isOT1 a.1 → ∀ b, T.isNF1 b → b ≤ a.1 → T.isOT1 b := by
    intro a
    induction a using T.well_founded_NF1.induction with
    | h a ih =>
      intro ha b hb hba
      rcases hba with hba | hba
      · obtain ⟨n, hfall, hbound⟩ := fund1_countable_cofinal a.1 b a.2 hb
          (isOT1_sound a.1 ha).2 hba
        have hn := T.isOT1.step a.1 ha n
        exact ih ⟨T.fund1 a.1 (T.ofNat n), (isOT1_sound _ hn).1⟩ hfall hn b hb hbound
      · rw [hba]; exact ha
  exact main ⟨a, (isOT1_sound a ha).1⟩ ha b hb hba

theorem LF1_cofinal (a : T) (hc : a < P 1 Z Z) : ∃ n, a < T.LF1 n := by
  cases a with
  | Z => exact ⟨0, .Z_lt_P 0 _ Z⟩
  | P i s t =>
    have hi : i = 0 := by
      exact match lt_inv i s t 1 Z Z hc with
      | Or.inl h => by
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h)
      | Or.inr (Or.inl ⟨_, h⟩) => by
        exact False.elim (lt_Z_inv h)
      | Or.inr (Or.inr ⟨_, _, h⟩) => by
        exact False.elim (lt_Z_inv h)
    subst i
    cases s with
    | Z => exact ⟨0, .p_mid 0 Z _ t Z (.Z_lt_P 0 Z Z)⟩
    | P j x y =>
      exact ⟨j+1, .p_mid 0 _ _ t Z (.p_head j (j+1) x Z y Z (Nat.lt_succ_self j))⟩

theorem T.isOT1_iff_isNF1 (s : T) : T.isOT1 s ↔ (T.isNF1 s ∧ s < P 1 Z Z) := by
  constructor
  · exact isOT1_sound s
  · intro hs
    obtain ⟨n, hn⟩ := LF1_cofinal s hs.2
    exact isOT1_downward (T.LF1 n) s (.base n) hs.1 (Or.inl hn)

def T.OT1 := { s : T // T.isOT1 s }

theorem T.well_founded_OT1 : WellFounded (fun s t : T.OT1 => s.1 < t.1) := by
  have hacc : ∀ s : T.NF1, ∀ hs : T.isOT1 s.1,
      Acc (fun s t : T.OT1 => s.1 < t.1) ⟨s.1, hs⟩ := by
    intro s
    induction s using T.well_founded_NF1.induction with
    | h s ih =>
      intro hs
      constructor
      intro t ht
      exact ih ⟨t.1, ((T.isOT1_iff_isNF1 t.1).mp t.2).1⟩ ht t.2
  constructor
  intro s
  exact hacc ⟨s.1, ((T.isOT1_iff_isNF1 s.1).mp s.2).1⟩ s.2

#print axioms T.well_founded_OT1
