import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans

open T

theorem bridge_stand_eq_self_of_NF1 (s : T) (hs : T.isNF1 s) : T.stand s = s := by
  induction hs with
  | z => rw [T.stand]
  | p s0 s1 s2 hs1 hs2 hG hhead ih1 ih2 =>
    rw [T.stand, ih2, ite_eq_left hhead]

theorem bridge_lt_add_left_of_size_lt (a b x : T)
    (ha : a ≠ T.Z) (hsize : T.size x < T.size a)
    (h : x < T.add a b) : x < a := by
  induction a generalizing x with
  | Z => exact False.elim (ha rfl)
  | P a0 a1 a2 ih1 ih2 =>
    rw [T.P_add_eq] at h
    cases x with
    | Z => exact T.Lt.Z_lt_P a0 a1 a2
    | P x0 x1 x2 =>
      cases lt_inv x0 x1 x2 a0 a1 (T.add a2 b) h with
      | inl hh =>
        exact T.Lt.p_head x0 a0 x1 a1 x2 a2 hh
      | inr hr =>
        cases hr with
        | inl hh =>
          cases hh.1
          exact T.Lt.p_mid a0 x1 a1 x2 a2 hh.2
        | inr hh =>
          have hx0 : x0 = a0 := hh.1
          have hx1 : x1 = a1 := hh.2.1
          cases hx0
          cases hx1
          have htailSize : T.size x2 < T.size a2 := by
            change T.size a1 + T.size x2 + 1 < T.size a1 + T.size a2 + 1 at hsize
            have hcancel1 : T.size a1 + T.size x2 < T.size a1 + T.size a2 :=
              Nat.lt_of_succ_lt_succ hsize
            exact Nat.add_lt_add_iff_left.mp hcancel1
          by_cases ha2 : a2 = T.Z
          · rw [ha2] at htailSize
            exact False.elim (Nat.not_lt_zero _ htailSize)
          · have htail : x2 < a2 := ih2 x2 ha2 htailSize hh.2.2
            exact T.Lt.p_tail a0 a1 x2 a2 htail

 theorem bridge_G1_add_left {u : Nat} (a b x : T) (hx : x ∈ T.G1 u a) :
    x ∈ T.G1 u (T.add a b) := by
  induction a with
  | Z =>
    rw [T.G1.eq_1] at hx
    cases hx
  | P a0 a1 a2 ih1 ih2 =>
    rw [T.P_add_eq]
    by_cases hu : u ≤ a0
    · rw [T.G1.eq_2, ite_eq_left hu] at hx
      rw [T.G1.eq_2, ite_eq_left hu]
      cases List.mem_append.mp hx with
      | inl hleft =>
        exact List.mem_append_left _ hleft
      | inr htail =>
        exact List.mem_append_right _ (ih2 htail)
    · rw [T.G1.eq_2, ite_eq_right hu] at hx
      rw [T.G1.eq_2, ite_eq_right hu]
      exact ih2 hx

 theorem bridge_isNF1_add_inv_right (a b : T) (h : T.isNF1 (T.add a b)) : T.isNF1 b := by
  induction a with
  | Z =>
    rw [T.add] at h
    exact h
  | P a0 a1 a2 ih1 ih2 =>
    rw [T.P_add_eq] at h
    have ht := (T.isNF1_P_inv a0 a1 (T.add a2 b) h).2.1
    exact ih2 ht

 theorem bridge_isNF1_add_inv_left (a b : T) (h : T.isNF1 (T.add a b)) : T.isNF1 a := by
  induction a with
  | Z => exact T.isNF1.z
  | P a0 a1 a2 ih1 ih2 =>
    rw [T.P_add_eq] at h
    obtain ⟨ha1, htail, hg, hhead⟩ := T.isNF1_P_inv a0 a1 (T.add a2 b) h
    have ha2 : T.isNF1 a2 := ih2 htail
    apply T.isNF1.p a0 a1 a2 ha1 ha2 hg
    cases a2 with
    | Z => exact T.Z_le (T.P a0 a1 T.Z)
    | P c0 c1 c2 =>
      have heq : T.head (T.add (T.P c0 c1 c2) b) = T.head (T.P c0 c1 c2) :=
        T.head_add_ne_Z c0 c1 c2 b
      rw [heq] at hhead
      exact hhead

 theorem bridge_strong_add_prefix (a b : T)
    (ha : a ≠ T.Z)
    (hnf : T.isNF1 (T.add a b))
    (hg : ∀ x : T, x ∈ T.G1 0 (T.add a b) → x < T.add a b) :
    T.isNF1 a ∧ ∀ x : T, x ∈ T.G1 0 a → x < a := by
  constructor
  · exact bridge_isNF1_add_inv_left a b hnf
  · intro x hx
    have hxfull : x ∈ T.G1 0 (T.add a b) := bridge_G1_add_left a b x hx
    have hxlt : x < T.add a b := hg x hxfull
    have hsz : T.size x < T.size a := G1_size_lt 0 a x hx
    exact bridge_lt_add_left_of_size_lt a b x ha hsz hxlt

 theorem bridge_part_add (s : T) : T.add (T.part s).1 (T.part s).2 = s := by
  induction s with
  | Z => rfl
  | P s0 s1 s2 ih1 ih2 =>
    rw [T.part]
    by_cases h0 : s0 = 0
    · rw [ite_eq_left h0]
      rfl
    · rw [ite_eq_right h0]
      cases hp : T.part s2 with
      | mk a b =>
        change T.add (T.P s0 s1 a) b = T.P s0 s1 s2
        rw [T.P_add_eq]
        have hi := ih2
        rw [hp] at hi
        change T.add a b = s2 at hi
        rw [hi]

#print axioms bridge_lt_add_left_of_size_lt
#print axioms bridge_strong_add_prefix
#print axioms bridge_part_add

theorem bridge_stand_P_NF1 (n : Nat) (a b : T)
    (ha : T.isNF1 a)
    (hga : ∀ x : T, x ∈ T.G1 n a → x < a)
    (hb : T.isNF1 b) :
    T.isNF1 (T.stand (T.P n a b)) := by
  rw [T.stand, bridge_stand_eq_self_of_NF1 b hb]
  by_cases hhead : T.head b ≤ T.P n a T.Z
  · rw [ite_eq_left hhead]
    exact T.isNF1.p n a b ha hb hga hhead
  · rw [ite_eq_right hhead]
    exact hb

theorem bridge_part_second_shape (s a b : T) (hp : T.part s = (a, b)) :
    b = T.Z ∨ ∃ c d : T, b = T.P 0 c d := by
  induction s generalizing a b with
  | Z =>
    rw [T.part] at hp
    injection hp with ha hb
    exact Or.inl hb.symm
  | P s0 s1 s2 ih1 ih2 =>
    rw [T.part] at hp
    by_cases h0 : s0 = 0
    · rw [ite_eq_left h0] at hp
      injection hp with ha hb
      subst s0
      exact Or.inr ⟨s1, s2, hb.symm⟩
    · rw [ite_eq_right h0] at hp
      cases htail : T.part s2 with
      | mk p q =>
        rw [htail] at hp
        injection hp with ha hb
        have hq := ih2 p q htail
        cases hq with
        | inl hz =>
          apply Or.inl
          rw [← hb]
          exact hz
        | inr hP =>
          obtain ⟨c, d, heq⟩ := hP
          apply Or.inr
          exact ⟨c, d, by rw [← hb]; exact heq⟩

theorem bridge_part_second_index0 (s a b : T)
    (hs : T.isNF1 s) (hp : T.part s = (a, b)) :
    T.index_Prop1 0 b := by
  have hsum : T.add a b = s := by
    have h := bridge_part_add s
    rw [hp] at h
    exact h
  have hb : T.isNF1 b := by
    rw [← hsum] at hs
    exact bridge_isNF1_add_inv_right a b hs
  cases bridge_part_second_shape s a b hp with
  | inl hz =>
    rw [hz]
    exact T.index_Prop1.z
  | inr hP =>
    obtain ⟨c, d, heq⟩ := hP
    rw [heq] at hb ⊢
    exact isNF1_index 0 0 c d hb (Nat.le_refl 0)

theorem bridge_stand_ne_Z (s : T) (hs : s ≠ T.Z) :
    T.stand s ≠ T.Z := by
  induction s with
  | Z => exact False.elim (hs rfl)
  | P p a b iha ihb =>
    rw [T.stand]
    by_cases hle : T.head (T.stand b) ≤ T.P p a T.Z
    · rw [ite_eq_left hle]
      intro h
      cases h
    · rw [ite_eq_right hle]
      have hb : b ≠ T.Z := by
        intro heq
        rw [heq, T.stand] at hle
        exact hle (T.Z_le (T.P p a T.Z))
      exact ihb hb

theorem bridge_early_collapse_ne_Z (s : T) (hs : s ≠ T.Z) :
    T.early_collapse s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P p a b =>
    rw [T.early_collapse]
    cases hp : T.part (T.P p a b) with
    | mk x y =>
      by_cases hx : x = T.Z
      · rw [ite_eq_left hx]
        intro h
        cases h
      · rw [ite_eq_right hx]
        exact bridge_stand_ne_Z (T.P 0 x y) (by
          intro h
          cases h)

#print axioms bridge_early_collapse_ne_Z

theorem bridge_card_times_ne_Z (n : Nat) (s : T) (hs : s ≠ T.Z) :
    T.card_times n s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P p a b =>
    cases n with
    | zero =>
      rw [T.card_times]
      intro h
      cases h
    | succ n =>
      rw [T.card_times]
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        cases hc : T.card_times (n + 1) b with
        | Z =>
          intro h
          cases h
        | P q c d =>
          intro h
          cases h
      · rw [ite_eq_right hp]
        cases hc : T.card_times (n + 1) b with
        | Z =>
          intro h
          cases h
        | P q c d =>
          intro h
          cases h

#print axioms bridge_card_times_ne_Z
