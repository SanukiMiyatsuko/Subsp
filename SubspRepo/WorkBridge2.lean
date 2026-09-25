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

theorem bridge_early_collapse_closed (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    T.isNF1 (T.early_collapse s) ∧
      T.index_Prop1 0 (T.early_collapse s) ∧
      (∀ x : T, x ∈ T.G1 1 (T.early_collapse s) → x < T.early_collapse s) := by
  cases s with
  | Z =>
    have hec : T.early_collapse T.Z = T.Z := by rfl
    rw [hec]
    constructor
    · exact T.isNF1.z
    · constructor
      · exact T.index_Prop1.z
      · intro x hx
        rw [T.G1.eq_1] at hx
        cases hx
  | P s0 s1 s2 =>
    by_cases hs0 : s0 = 0
    · have hec : T.early_collapse (T.P s0 s1 s2) = T.P s0 s1 s2 := by
        rw [T.early_collapse, T.part, ite_eq_left hs0]
        rfl
      rw [hec]
      subst s0
      have hindex : T.index_Prop1 0 (T.P 0 s1 s2) :=
        isNF1_index 0 0 s1 s2 hs (Nat.le_refl 0)
      constructor
      · exact hs
      · constructor
        · exact hindex
        · intro x hx
          have hempty := index_Prop1_G1_empty 0 (T.P 0 s1 s2) hindex 1 (Nat.zero_lt_succ 0)
          rw [hempty] at hx
          cases hx
    · cases hp : T.part s2 with
      | mk a b =>
        have hpne : T.P s0 s1 a ≠ T.Z := by
          intro h
          cases h
        have hec : T.early_collapse (T.P s0 s1 s2) =
            T.stand (T.P 0 (T.P s0 s1 a) b) := by
          rw [T.early_collapse, T.part, ite_eq_right hs0, hp]
          change (if T.P s0 s1 a = T.Z then T.P s0 s1 s2
            else T.stand (T.P 0 (T.P s0 s1 a) b)) =
            T.stand (T.P 0 (T.P s0 s1 a) b)
          rw [ite_eq_right hpne]
        rw [hec]
        let p : T := T.P s0 s1 a
        have hsumTail : T.add a b = s2 := by
          have hh := bridge_part_add s2
          rw [hp] at hh
          exact hh
        have hwhole : T.add p b = T.P s0 s1 s2 := by
          unfold p
          rw [T.P_add_eq, hsumTail]
        have hnfFull : T.isNF1 (T.add p b) := by
          rw [hwhole]
          exact hs
        have hgFull : ∀ x : T, x ∈ T.G1 0 (T.add p b) → x < T.add p b := by
          intro x hx
          rw [hwhole] at hx ⊢
          exact hg x hx
        have hpStrong := bridge_strong_add_prefix p b (by
          unfold p
          intro h
          cases h) hnfFull hgFull
        have hbNF : T.isNF1 b := bridge_isNF1_add_inv_right p b hnfFull
        have hbIndex : T.index_Prop1 0 b :=
          bridge_part_second_index0 s2 a b
            (T.isNF1_P_inv s0 s1 s2 hs).2.1 hp
        change
          T.isNF1 (T.stand (T.P 0 p b)) ∧
          T.index_Prop1 0 (T.stand (T.P 0 p b)) ∧
          (∀ x : T, x ∈ T.G1 1 (T.stand (T.P 0 p b)) →
            x < T.stand (T.P 0 p b))
        rw [T.stand, bridge_stand_eq_self_of_NF1 b hbNF]
        by_cases hhead : T.head b ≤ T.P 0 p T.Z
        · rw [ite_eq_left hhead]
          have hkeep : T.isNF1 (T.P 0 p b) :=
            T.isNF1.p 0 p b hpStrong.1 hbNF hpStrong.2 hhead
          have hindex : T.index_Prop1 0 (T.P 0 p b) :=
            isNF1_index 0 0 p b hkeep (Nat.le_refl 0)
          constructor
          · exact hkeep
          · constructor
            · exact hindex
            · intro x hx
              have hempty := index_Prop1_G1_empty 0 (T.P 0 p b) hindex 1 (Nat.zero_lt_succ 0)
              rw [hempty] at hx
              cases hx
        · rw [ite_eq_right hhead]
          constructor
          · exact hbNF
          · constructor
            · exact hbIndex
            · intro x hx
              have hempty := index_Prop1_G1_empty 0 b hbIndex 1 (Nat.zero_lt_succ 0)
              rw [hempty] at hx
              cases hx

#print axioms bridge_early_collapse_closed

theorem bridge_add_left_lt (p a b : T) (h : a < b) :
    T.add p a < T.add p b := by
  induction p with
  | Z =>
    rw [T.add, T.add]
    exact h
  | P p0 p1 p2 ih1 ih2 =>
    rw [T.P_add_eq, T.P_add_eq]
    exact T.Lt.p_tail p0 p1 (T.add p2 a) (T.add p2 b) ih2

#print axioms bridge_add_left_lt

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

theorem bridge_nat1_NF (k : Nat) :
    T.isNF1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) := by
  have h := mul_isNF1_and_head 1 T.Z T.isNF1.z
    (fun x hx => by
      rw [T.G1.eq_1] at hx
      cases hx) k
  exact h.1

theorem bridge_nat1_index (k : Nat) :
    T.index_Prop1 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) := by
  induction k with
  | zero =>
    rw [T.ofNat, T.mul]
    exact T.index_Prop1.z
  | succ k ih =>
    rw [mul_succ_shape 1 T.Z k]
    exact T.index_Prop1.p 1 T.Z _ (Nat.le_refl 1) ih

theorem bridge_shift_index (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    T.index_Prop1 1
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  apply Rank1Termination.index_add 1
  · exact bridge_nat1_index k
  · exact Rank1Termination.index_mono (Nat.zero_le 1) c hc

theorem bridge_shift_head_le (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    T.head (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) ≤
      T.P 1 T.Z T.Z := by
  cases k with
  | zero =>
    rw [T.ofNat, T.mul, T.add]
    cases c with
    | Z => exact T.Z_le (T.P 1 T.Z T.Z)
    | P p a b =>
      cases hc with
      | p _ _ _ hp htail =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        exact Or.inl (T.Lt.p_head 0 1 a T.Z T.Z T.Z (Nat.zero_lt_succ 0))
  | succ k =>
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
    exact Or.inr rfl

theorem bridge_shift_NF (k : Nat) (c : T)
    (hnf : T.isNF1 c) (hc : T.index_Prop1 0 c) :
    T.isNF1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  induction k with
  | zero =>
    rw [T.ofNat, T.mul, T.add]
    exact hnf
  | succ k ih =>
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
    exact T.isNF1.p 1 T.Z
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c)
      T.isNF1.z ih
      (fun x hx => by
        rw [T.G1.eq_1] at hx
        cases hx)
      (bridge_shift_head_le k c hc)

#print axioms bridge_shift_NF

theorem bridge_shift_lt_wrap (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.P 1 T.Z
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) := by
  induction k with
  | zero =>
    rw [T.ofNat, T.mul, T.add]
    cases c with
    | Z => exact T.Lt.Z_lt_P 1 T.Z T.Z
    | P p a b =>
      cases hc with
      | p _ _ _ hp htail =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        exact T.Lt.p_head 0 1 a T.Z b (T.P 0 a b) (Nat.zero_lt_succ 0)
  | succ k ih =>
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
    exact T.Lt.p_tail 1 T.Z
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c)
      (T.P 1 T.Z (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c))
      ih

theorem bridge_shift_strong1 (k : Nat) (c : T)
    (hc : T.index_Prop1 0 c) :
    ∀ x : T,
      x ∈ T.G1 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) →
      x < T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c := by
  induction k with
  | zero =>
    intro x hx
    rw [T.ofNat, T.mul, T.add] at hx ⊢
    have hempty := index_Prop1_G1_empty 0 c hc 1 (Nat.zero_lt_succ 0)
    rw [hempty] at hx
    cases hx
  | succ k ih =>
    intro x hx
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq] at hx ⊢
    rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1), List.mem_append, List.mem_append] at hx
    cases hx with
    | inl hleft =>
      cases hleft with
      | inl hz =>
        have heq : x = T.Z := List.mem_singleton.mp hz
        rw [heq]
        exact T.Lt.Z_lt_P 1 T.Z _
      | inr hzG =>
        rw [T.G1.eq_1] at hzG
        cases hzG
    | inr htail =>
      have hxtail := ih x htail
      have htailwrap := bridge_shift_lt_wrap k c hc
      exact lt_trans_thm x _ _ hxtail htailwrap

#print axioms bridge_shift_strong1

theorem part_lt_cases : ∀ s t : T, s < t →
    (T.part s).1 < (T.part t).1 ∨
      ((T.part s).1 = (T.part t).1 ∧ (T.part s).2 < (T.part t).2) := by
  intro s
  induction s with
  | Z =>
    intro t h
    cases t with
    | Z => cases h
    | P q u v =>
      rw [T.part]
      rw [T.part]
      by_cases hq : q = 0
      · rw [ite_eq_left hq]
        exact Or.inr ⟨rfl, T.Lt.Z_lt_P q u v⟩
      · rw [ite_eq_right hq]
        cases hp : T.part v with
        | mk c d =>
          exact Or.inl (T.Lt.Z_lt_P q u c)
  | P p x y ihx ihy =>
    intro t h
    cases t with
    | Z => cases h
    | P q u v =>
      rw [T.part]
      rw [T.part]
      by_cases hp0 : p = 0
      · rw [ite_eq_left hp0]
        by_cases hq0 : q = 0
        · rw [ite_eq_left hq0]
          exact Or.inr ⟨rfl, h⟩
        · rw [ite_eq_right hq0]
          cases hvp : T.part v with
          | mk c d =>
            exact Or.inl (T.Lt.Z_lt_P q u c)
      · rw [ite_eq_right hp0]
        cases hyp : T.part y with
        | mk a b =>
          by_cases hq0 : q = 0
          · rw [ite_eq_left hq0]
            have hinv := lt_inv p x y q u v h
            cases hinv with
            | inl hpq =>
              have hpzero : p < 0 := by rw [hq0] at hpq; exact hpq
              exact False.elim (Nat.not_lt_zero p hpzero)
            | inr hor =>
              cases hor with
              | inl hm =>
                have hpq : p = 0 := by rw [hq0] at hm; exact hm.1
                exact False.elim (hp0 hpq)
              | inr ht =>
                have hpq : p = 0 := by rw [hq0] at ht; exact ht.1
                exact False.elim (hp0 hpq)
          · rw [ite_eq_right hq0]
            cases hvp : T.part v with
            | mk c d =>
              have hinv := lt_inv p x y q u v h
              cases hinv with
              | inl hpq =>
                exact Or.inl (T.Lt.p_head p q x u a c hpq)
              | inr hor =>
                cases hor with
                | inl hm =>
                  cases hm.1
                  exact Or.inl (T.Lt.p_mid p x u a c hm.2)
                | inr ht =>
                  cases ht.1
                  cases ht.2.1
                  have hrec := ihy v ht.2.2
                  rw [hyp, hvp] at hrec
                  cases hrec with
                  | inl hac =>
                    exact Or.inl (T.Lt.p_tail p x a c hac)
                  | inr heq =>
                    apply Or.inr
                    constructor
                    · have hac : a = c := heq.1
                      rw [hac]
                    · exact heq.2

#print axioms part_lt_cases

theorem bridge_early_collapse_part (s a b : T)
    (hp : T.part s = (a, b)) (hb : T.isNF1 b) :
    T.early_collapse s =
      if a = T.Z then b
      else if T.head b ≤ T.P 0 a T.Z then T.P 0 a b else b := by
  rw [T.early_collapse, hp]
  by_cases ha : a = T.Z
  · rw [ite_eq_left ha]
    have hadd := bridge_part_add s
    rw [hp, ha, T.add] at hadd
    have hbs : b = s := hadd
    rw [ite_eq_left ha]
    exact hbs.symm
  · rw [ite_eq_right ha]
    rw [T.stand, bridge_stand_eq_self_of_NF1 b hb]
    rw [ite_eq_right ha]

#print axioms bridge_early_collapse_part

theorem bridge_part_fst_fixed (s : T) :
    T.part (T.part s).1 = ((T.part s).1, T.Z) := by
  induction s with
  | Z => rfl
  | P p a b iha ihb =>
    rw [T.part]
    by_cases hp : p = 0
    · rw [ite_eq_left hp]
      rfl
    · rw [ite_eq_right hp]
      cases hpb : T.part b with
      | mk c d =>
        have ih := ihb
        rw [hpb] at ih
        change T.part (T.P p a c) = (T.P p a c, T.Z)
        rw [T.part, ite_eq_right hp, ih]

theorem bridge_part_snd_fixed (s : T) :
    T.part (T.part s).2 = (T.Z, (T.part s).2) := by
  induction s with
  | Z => rfl
  | P p a b iha ihb =>
    rw [T.part]
    by_cases hp : p = 0
    · rw [ite_eq_left hp]
      rw [T.part, ite_eq_left hp]
    · rw [ite_eq_right hp]
      cases hpb : T.part b with
      | mk c d =>
        have ih := ihb
        rw [hpb] at ih
        exact ih

#print axioms bridge_part_fst_fixed
#print axioms bridge_part_snd_fixed

theorem bridge_part_lt_of_cases (s t : T)
    (h : (T.part s).1 < (T.part t).1 ∨
      ((T.part s).1 = (T.part t).1 ∧ (T.part s).2 < (T.part t).2)) :
    s < t := by
  cases lt_total_thm s t with
  | inl hst => exact hst
  | inr hor =>
    cases hor with
    | inl hts =>
      have hr := part_lt_cases t s hts
      cases h with
      | inl hfst =>
        cases hr with
        | inl hrev =>
          exact False.elim (lt_asymm_thm hfst hrev)
        | inr hrev =>
          rw [hrev.1] at hfst
          exact False.elim (lt_irrefl_thm _ hfst)
      | inr heq =>
        cases hr with
        | inl hrev =>
          rw [heq.1] at hrev
          exact False.elim (lt_irrefl_thm (T.part t).1 hrev)
        | inr hrev =>
          exact False.elim (lt_asymm_thm heq.2 hrev.2)
    | inr heqst =>
      have hp : T.part s = T.part t := congrArg T.part heqst
      cases h with
      | inl hfst =>
        rw [hp] at hfst
        exact False.elim (lt_irrefl_thm (T.part t).1 hfst)
      | inr hsnd =>
        rw [hp] at hsnd
        exact False.elim (lt_irrefl_thm (T.part t).2 hsnd.2)

#print axioms bridge_part_lt_of_cases

theorem bridge_lt_of_not_le (a b : T) (h : ¬ a ≤ b) : b < a := by
  cases lt_total_thm a b with
  | inl hab => exact False.elim (h (Or.inl hab))
  | inr hor =>
    cases hor with
    | inl hba => exact hba
    | inr heq => exact False.elim (h (Or.inr heq))

theorem bridge_part_prefix_upper (s t : T)
    (h : (T.part s).1 < (T.part t).1) :
    s < (T.part t).1 := by
  apply bridge_part_lt_of_cases s (T.part t).1
  have hfix := bridge_part_fst_fixed t
  rw [hfix]
  exact Or.inl h

theorem bridge_insert_lt (a b d : T)
    (hb : T.isNF1 b) (hd : T.isNF1 d)
    (hpb : T.part b = (T.Z, b))
    (hpd : T.part d = (T.Z, d))
    (hbd : b < d) :
    T.stand (T.P 0 a b) < T.stand (T.P 0 a d) := by
  rw [T.stand, bridge_stand_eq_self_of_NF1 b hb]
  rw [T.stand, bridge_stand_eq_self_of_NF1 d hd]
  have hbshape := bridge_part_second_shape b T.Z b hpb
  have hdshape := bridge_part_second_shape d T.Z d hpd
  cases hbshape with
  | inl hbz =>
    subst b
    cases hdshape with
    | inl hdz =>
      subst d
      exact False.elim (lt_irrefl_thm T.Z hbd)
    | inr hdp =>
      obtain ⟨f, g, hdeq⟩ := hdp
      rw [hdeq] at hbd ⊢
      have hleft : T.head T.Z ≤ T.P 0 a T.Z := T.Z_le _
      rw [ite_eq_left hleft]
      change
        T.P 0 a T.Z <
          (if T.P 0 f T.Z ≤ T.P 0 a T.Z then
            T.P 0 a (T.P 0 f g) else T.P 0 f g)
      by_cases hfa : T.P 0 f T.Z ≤ T.P 0 a T.Z
      · rw [ite_eq_left hfa]
        exact T.Lt.p_tail 0 a T.Z (T.P 0 f g)
          (T.Lt.Z_lt_P 0 f g)
      · rw [ite_eq_right hfa]
        have haf : T.P 0 a T.Z < T.P 0 f T.Z :=
          bridge_lt_of_not_le (T.P 0 f T.Z) (T.P 0 a T.Z) hfa
        cases lt_inv 0 a T.Z 0 f T.Z haf with
        | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
        | inr hor =>
          cases hor with
          | inl hm => exact T.Lt.p_mid 0 a f T.Z g hm.2
          | inr ht => exact False.elim (lt_Z_inv ht.2.2)
  | inr hbp =>
    obtain ⟨c, e, hbeq⟩ := hbp
    subst b
    cases hdshape with
    | inl hdz =>
      subst d
      exact False.elim (lt_Z_inv hbd)
    | inr hdp =>
      obtain ⟨f, g, hdeq⟩ := hdp
      subst d
      change
        (if T.P 0 c T.Z ≤ T.P 0 a T.Z then
          T.P 0 a (T.P 0 c e) else T.P 0 c e) <
        (if T.P 0 f T.Z ≤ T.P 0 a T.Z then
          T.P 0 a (T.P 0 f g) else T.P 0 f g)
      by_cases hca : T.P 0 c T.Z ≤ T.P 0 a T.Z
      · rw [ite_eq_left hca]
        by_cases hfa : T.P 0 f T.Z ≤ T.P 0 a T.Z
        · rw [ite_eq_left hfa]
          exact T.Lt.p_tail 0 a (T.P 0 c e) (T.P 0 f g) hbd
        · rw [ite_eq_right hfa]
          have haf : T.P 0 a T.Z < T.P 0 f T.Z :=
            bridge_lt_of_not_le (T.P 0 f T.Z) (T.P 0 a T.Z) hfa
          cases lt_inv 0 a T.Z 0 f T.Z haf with
          | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
          | inr hor =>
            cases hor with
            | inl hm => exact T.Lt.p_mid 0 a f (T.P 0 c e) g hm.2
            | inr ht => exact False.elim (lt_Z_inv ht.2.2)
      · rw [ite_eq_right hca]
        by_cases hfa : T.P 0 f T.Z ≤ T.P 0 a T.Z
        · rw [ite_eq_left hfa]
          have hcf : c < f ∨ (c = f ∧ e < g) := by
            cases lt_inv 0 c e 0 f g hbd with
            | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
            | inr hor =>
              cases hor with
              | inl hm => exact Or.inl hm.2
              | inr ht => exact Or.inr ⟨ht.2.1, ht.2.2⟩
          cases hcf with
          | inl hcf =>
            have hclef : c ≤ f := Or.inl hcf
            have hflea : f ≤ a := by
              cases hfa with
              | inl hlt =>
                cases lt_inv 0 f T.Z 0 a T.Z hlt with
                | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
                | inr hor =>
                  cases hor with
                  | inl hm => exact Or.inl hm.2
                  | inr ht => exact Or.inr ht.2.1
              | inr heq =>
                injection heq with _ hmid
                exact Or.inr hmid
            have hcla : c ≤ a := partial_order.trans c f a hclef hflea
            have hheadca : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
              cases hcla with
              | inl hlt => exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z hlt)
              | inr heq => rw [heq]; exact Or.inr rfl
            exact False.elim (hca hheadca)
          | inr heq =>
            have hcfEq : c = f := heq.1
            subst f
            have hclea : c ≤ a := by
              cases hfa with
              | inl hlt =>
                cases lt_inv 0 c T.Z 0 a T.Z hlt with
                | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
                | inr hor =>
                  cases hor with
                  | inl hm => exact Or.inl hm.2
                  | inr ht => exact Or.inr ht.2.1
              | inr heqca =>
                injection heqca with _ hmid
                exact Or.inr hmid
            have hheadca : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
              cases hclea with
              | inl hlt => exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z hlt)
              | inr heqca => rw [heqca]; exact Or.inr rfl
            exact False.elim (hca hheadca)
        · rw [ite_eq_right hfa]
          exact hbd

#print axioms bridge_insert_lt

theorem bridge_G1_add_eq (u : Nat) (a b : T) :
    T.G1 u (T.add a b) = T.G1 u a ++ T.G1 u b := by
  induction a with
  | Z =>
    rw [T.add]
    rw [T.G1.eq_1]
    rw [List.nil_append]
  | P p x y ihx ihy =>
    cases b with
    | Z =>
      rw [T.add_Z]
      rw [T.G1.eq_1]
      rw [List.append_nil]
    | P q c d =>
      rw [T.P_add_eq]
      rw [T.G1.eq_2, T.G1.eq_2]
      by_cases hup : u ≤ p
      · rw [ite_eq_left hup, ite_eq_left hup]
        rw [ihy]
        rw [← List.append_assoc]
      · rw [ite_eq_right hup, ite_eq_right hup]
        exact ihy

theorem bridge_head_le_self (s : T) : T.head s ≤ s := by
  cases s with
  | Z => exact Or.inr rfl
  | P p a b =>
    cases b with
    | Z => exact Or.inr rfl
    | P q c d =>
      exact Or.inl (T.Lt.p_tail p a T.Z (T.P q c d)
        (T.Lt.Z_lt_P q c d))

theorem bridge_part_fst_le_self (s : T) : (T.part s).1 ≤ s := by
  by_cases hb : (T.part s).2 = T.Z
  · have hadd := bridge_part_add s
    rw [hb, T.add_Z] at hadd
    exact Or.inr hadd
  · apply Or.inl
    apply bridge_part_lt_of_cases (T.part s).1 s
    have hfix := bridge_part_fst_fixed s
    rw [hfix]
    have hzb : T.Z < (T.part s).2 := by
      cases T.Z_le (T.part s).2 with
      | inl hlt => exact hlt
      | inr heq => exact False.elim (hb heq.symm)
    exact Or.inr ⟨rfl, hzb⟩

#print axioms bridge_part_fst_le_self

theorem bridge_mid_mem_G1_zero (a b : T) :
    a ∈ T.G1 0 (T.P 0 a b) := by
  rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
  exact List.mem_append_left _
    (List.mem_append_left _ (List.mem_singleton_self a))

theorem bridge_remainder_member_lt (s a c d : T)
    (hp : T.part s = (a, T.P 0 c d))
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    c < s := by
  have hadd := bridge_part_add s
  rw [hp] at hadd
  have hmemTail : c ∈ T.G1 0 (T.P 0 c d) :=
    bridge_mid_mem_G1_zero c d
  have hmemAdd : c ∈ T.G1 0 (T.add a (T.P 0 c d)) := by
    rw [bridge_G1_add_eq]
    exact List.mem_append_right _ hmemTail
  rw [hadd] at hmemAdd
  exact hg c hmemAdd

theorem bridge_early_collapse_upper (s c : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (hsc : s < c) :
    T.early_collapse s < T.P 0 c T.Z := by
  cases hp : T.part s with
  | mk a b =>
    have hadd := bridge_part_add s
    rw [hp] at hadd
    have hnfAdd : T.isNF1 (T.add a b) := by
      rw [hadd]
      exact hs
    have hbNF : T.isNF1 b := bridge_isNF1_add_inv_right a b hnfAdd
    have hec := bridge_early_collapse_part s a b hp hbNF
    by_cases ha : a = T.Z
    · rw [hec, ite_eq_left ha]
      have hbEq : b = s := by
        rw [ha, T.add] at hadd
        exact hadd
      have hbshape := bridge_part_second_shape s a b hp
      cases hbshape with
      | inl hbz =>
        rw [hbz]
        exact T.Lt.Z_lt_P 0 c T.Z
      | inr hbp =>
        obtain ⟨e, f, hbeq⟩ := hbp
        rw [hbeq]
        have hes : e < s := bridge_remainder_member_lt s a e f (by
          rw [hbeq] at hp
          exact hp) hg
        have hecLt : e < c := lt_trans_thm e s c hes hsc
        exact T.Lt.p_mid 0 e c f T.Z hecLt
    · rw [hec, ite_eq_right ha]
      by_cases hhead : T.head b ≤ T.P 0 a T.Z
      · rw [ite_eq_left hhead]
        have has0 := bridge_part_fst_le_self s
        have has : a ≤ s := by
          rw [hp] at has0
          exact has0
        have hac : a < c := lt_of_le_of_lt_thm T a s c has hsc
        exact T.Lt.p_mid 0 a c b T.Z hac
      · rw [ite_eq_right hhead]
        have hbshape := bridge_part_second_shape s a b hp
        cases hbshape with
        | inl hbz =>
          rw [hbz]
          exact T.Lt.Z_lt_P 0 c T.Z
        | inr hbp =>
          obtain ⟨e, f, hbeq⟩ := hbp
          rw [hbeq]
          have hes : e < s := bridge_remainder_member_lt s a e f (by
            rw [hbeq] at hp
            exact hp) hg
          have hecLt : e < c := lt_trans_thm e s c hes hsc
          exact T.Lt.p_mid 0 e c f T.Z hecLt

#print axioms bridge_early_collapse_upper

theorem bridge_part_base_le_early_collapse (t : T)
    (ht : T.isNF1 t) (hc : (T.part t).1 ≠ T.Z) :
    T.P 0 (T.part t).1 T.Z ≤ T.early_collapse t := by
  cases hp : T.part t with
  | mk c d =>
    have hadd := bridge_part_add t
    rw [hp] at hadd
    have hnfAdd : T.isNF1 (T.add c d) := by
      rw [hadd]
      exact ht
    have hdNF : T.isNF1 d := bridge_isNF1_add_inv_right c d hnfAdd
    have hc' : c ≠ T.Z := by
      intro hcz
      apply hc
      rw [hp]
      exact hcz
    have hec := bridge_early_collapse_part t c d hp hdNF
    change T.P 0 c T.Z ≤ T.early_collapse t
    rw [hec, ite_eq_right hc']
    by_cases hhead : T.head d ≤ T.P 0 c T.Z
    · rw [ite_eq_left hhead]
      cases T.Z_le d with
      | inl hzd =>
        exact Or.inl (T.Lt.p_tail 0 c T.Z d hzd)
      | inr hzd =>
        have hdZ : d = T.Z := hzd.symm
        rw [hdZ]
        exact Or.inr rfl
    · rw [ite_eq_right hhead]
      have hbaseHead : T.P 0 c T.Z < T.head d :=
        bridge_lt_of_not_le (T.head d) (T.P 0 c T.Z) hhead
      have hheadD : T.head d ≤ d := bridge_head_le_self d
      exact Or.inl (lt_of_lt_of_le_thm T (T.P 0 c T.Z) (T.head d) d
        hbaseHead hheadD)

#print axioms bridge_part_base_le_early_collapse

theorem bridge_early_collapse_lt (s t : T)
    (hs : T.isNF1 s)
    (hsg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t)
    (htg : ∀ x : T, x ∈ T.G1 0 t → x < t)
    (hst : s < t) :
    T.early_collapse s < T.early_collapse t := by
  cases hps : T.part s with
  | mk a b =>
    cases hpt : T.part t with
    | mk c d =>
      have hsadd := bridge_part_add s
      rw [hps] at hsadd
      have htadd := bridge_part_add t
      rw [hpt] at htadd
      have hsnfadd : T.isNF1 (T.add a b) := by
        rw [hsadd]
        exact hs
      have htnfadd : T.isNF1 (T.add c d) := by
        rw [htadd]
        exact ht
      have hbNF : T.isNF1 b := bridge_isNF1_add_inv_right a b hsnfadd
      have hdNF : T.isNF1 d := bridge_isNF1_add_inv_right c d htnfadd
      have hbfix0 := bridge_part_snd_fixed s
      have hdfix0 := bridge_part_snd_fixed t
      rw [hps] at hbfix0
      rw [hpt] at hdfix0
      have hbfix : T.part b = (T.Z, b) := hbfix0
      have hdfix : T.part d = (T.Z, d) := hdfix0
      have hparts := part_lt_cases s t hst
      rw [hps, hpt] at hparts
      cases hparts with
      | inl hac =>
        have hsc0 := bridge_part_prefix_upper s t
          (by
            rw [hps, hpt]
            exact hac)
        have hsc : s < c := by
          rw [hpt] at hsc0
          exact hsc0
        have hupper := bridge_early_collapse_upper s c hs hsg hsc
        have hcne : c ≠ T.Z := by
          intro hcz
          rw [hcz] at hac
          exact lt_Z_inv hac
        have hlower0 := bridge_part_base_le_early_collapse t ht (by
          rw [hpt]
          exact hcne)
        have hlower : T.P 0 c T.Z ≤ T.early_collapse t := by
          rw [hpt] at hlower0
          exact hlower0
        exact lt_of_lt_of_le_thm T (T.early_collapse s)
          (T.P 0 c T.Z) (T.early_collapse t) hupper hlower
      | inr heq =>
        have hacEq : a = c := heq.1
        have hbd : b < d := heq.2
        subst c
        by_cases ha : a = T.Z
        · have hecs := bridge_early_collapse_part s a b hps hbNF
          have hect := bridge_early_collapse_part t a d hpt hdNF
          rw [hecs, hect, ite_eq_left ha, ite_eq_left ha]
          exact hbd
        · rw [T.early_collapse, hps, ite_eq_right ha]
          rw [T.early_collapse, hpt, ite_eq_right ha]
          exact bridge_insert_lt a b d hbNF hdNF hbfix hdfix hbd

#print axioms bridge_early_collapse_lt

theorem bridge_card_times_lt_same (n : Nat) :
    ∀ c d : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 d → T.index_Prop1 0 d →
      c < d → T.card_times n c < T.card_times n d := by
  intro c
  induction c with
  | Z =>
    intro d hcNF hcIdx hdNF hdIdx hcd
    have hdne : d ≠ T.Z := by
      intro heq
      rw [heq] at hcd
      exact lt_Z_inv hcd
    have hctne : T.card_times n d ≠ T.Z := bridge_card_times_ne_Z n d hdne
    cases T.Z_le (T.card_times n d) with
    | inl hlt =>
      rw [T.card_times]
      exact hlt
    | inr heq =>
      exact False.elim (hctne heq.symm)
  | P p a b iha ihb =>
    intro d hcNF hcIdx hdNF hdIdx hcd
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      cases d with
      | Z => exact False.elim (lt_Z_inv hcd)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq0 hfIdx =>
          have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f hdNF
          cases n with
          | zero =>
            rw [T.card_times, T.card_times]
            exact hcd
          | succ k =>
            rw [T.card_times, T.card_times]
            rw [ite_eq_left rfl, ite_eq_left rfl]
            rw [← add_eq_hAdd
              (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
              (T.card_times (k + 1) b),
              T.P_add_eq]
            rw [← add_eq_hAdd
              (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse e) T.Z)
              (T.card_times (k + 1) f),
              T.P_add_eq]
            change
              T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a))
                (T.card_times (k + 1) b) <
              T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse e))
                (T.card_times (k + 1) f)
            cases lt_inv 0 a b 0 e f hcd with
            | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
            | inr hor =>
              cases hor with
              | inl hmid =>
                have hae : a < e := hmid.2
                have hec : T.early_collapse a < T.early_collapse e :=
                  bridge_early_collapse_lt a e haNF haG heNF heG hae
                have hshift := bridge_add_left_lt
                  (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a) (T.early_collapse e) hec
                exact T.Lt.p_mid 1 _ _ _ _ hshift
              | inr htail =>
                have hae : a = e := htail.2.1
                subst e
                have hbf : b < f := htail.2.2
                have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
                exact T.Lt.p_tail 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                    (T.early_collapse a))
                  (T.card_times (k + 1) b)
                  (T.card_times (k + 1) f) hrec

#print axioms bridge_card_times_lt_same

theorem bridge_shift_level_lt : ∀ k l : Nat, k < l →
    ∀ x y : T, T.index_Prop1 0 x → T.index_Prop1 0 y →
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) x <
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) y := by
  intro k
  induction k with
  | zero =>
    intro l hkl x y hx hy
    cases l with
    | zero => exact False.elim (Nat.lt_irrefl 0 hkl)
    | succ l =>
      rw [T.ofNat, T.mul, T.add]
      rw [mul_succ_shape 1 T.Z l, T.P_add_eq]
      cases x with
      | Z => exact T.Lt.Z_lt_P 1 T.Z _
      | P p a b =>
        cases hx with
        | p _ _ _ hp htail =>
          have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
          subst p
          exact T.Lt.p_head 0 1 a T.Z b _ (Nat.zero_lt_succ 0)
  | succ k ih =>
    intro l hkl x y hx hy
    cases l with
    | zero => exact False.elim (Nat.not_lt_zero (k + 1) hkl)
    | succ l =>
      have hkl' : k < l := Nat.lt_of_succ_lt_succ hkl
      rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
      rw [mul_succ_shape 1 T.Z l, T.P_add_eq]
      exact T.Lt.p_tail 1 T.Z _ _ (ih l hkl' x y hx hy)

#print axioms bridge_shift_level_lt

theorem bridge_card_times_level_lt (m n : Nat) (c d : T)
    (hmn : m < n)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) (hcne : c ≠ T.Z)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d) (hdne : d ≠ T.Z) :
    T.card_times m c < T.card_times n d := by
  cases c with
  | Z => exact False.elim (hcne rfl)
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      cases d with
      | Z => exact False.elim (hdne rfl)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq0 hfIdx =>
          have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
          subst q
          obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f hdNF
          have haEC := bridge_early_collapse_closed a haNF haG
          have heEC := bridge_early_collapse_closed e heNF heG
          cases m with
          | zero =>
            cases n with
            | zero => exact False.elim (Nat.lt_irrefl 0 hmn)
            | succ l =>
              rw [T.card_times]
              rw [T.card_times, ite_eq_left rfl]
              rw [← add_eq_hAdd
                (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat l) + T.early_collapse e) T.Z)
                (T.card_times (l + 1) f), T.P_add_eq]
              exact T.Lt.p_head 0 1 a
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) (T.early_collapse e))
                b (T.card_times (l + 1) f) (Nat.zero_lt_succ 0)
          | succ k =>
            cases n with
            | zero => exact False.elim (Nat.not_lt_zero (k + 1) hmn)
            | succ l =>
              have hkl : k < l := Nat.lt_of_succ_lt_succ hmn
              rw [T.card_times, T.card_times]
              rw [ite_eq_left rfl, ite_eq_left rfl]
              rw [← add_eq_hAdd
                (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                (T.card_times (k + 1) b), T.P_add_eq]
              rw [← add_eq_hAdd
                (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat l) + T.early_collapse e) T.Z)
                (T.card_times (l + 1) f), T.P_add_eq]
              have hshift := bridge_shift_level_lt k l hkl
                (T.early_collapse a) (T.early_collapse e) haEC.2.1 heEC.2.1
              exact T.Lt.p_mid 1 _ _ _ _ hshift

#print axioms bridge_card_times_level_lt


theorem bridge_head_NF1 (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.head s) := by
  cases s with
  | Z => exact T.isNF1.z
  | P p a b =>
    obtain ⟨ha, hb, hg, hh⟩ := T.isNF1_P_inv p a b hs
    exact T.isNF1.p p a T.Z ha T.isNF1.z hg (T.Z_le _)

theorem bridge_head_index0 (s : T) (hs : T.index_Prop1 0 s) :
    T.index_Prop1 0 (T.head s) := by
  cases s with
  | Z => exact T.index_Prop1.z
  | P p a b =>
    cases hs with
    | p _ _ _ hp hb =>
      exact T.index_Prop1.p p a T.Z hp T.index_Prop1.z

theorem bridge_card_times_head (n : Nat) (s : T) :
    T.head (T.card_times n s) = T.card_times n (T.head s) := by
  cases s with
  | Z =>
    cases n with
    | zero => rfl
    | succ k => rfl
  | P p a b =>
    cases n with
    | zero => rfl
    | succ k =>
      by_cases hp : p = 0
      · subst p
        rw [T.card_times, ite_eq_left rfl]
        rw [← add_eq_hAdd, T.P_add_eq, T.add]
        change T.P 1 _ T.Z = T.card_times (k + 1) (T.P 0 a T.Z)
        rw [T.card_times, ite_eq_left rfl]
        rw [T.card_times]
        let A : T := T.P 1
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
            (T.early_collapse a)) T.Z
        change A = A + T.Z
        exact (T.add_Z A).symm.trans (add_eq_hAdd A T.Z)
      · rw [T.card_times, ite_eq_right hp]
        rw [← add_eq_hAdd, T.P_add_eq, T.add]
        change T.P 1 _ T.Z = T.card_times (k + 1) (T.P p a T.Z)
        rw [T.card_times, ite_eq_right hp]
        rw [T.card_times]
        let A : T := T.P 1
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) T.Z
        change A = A + T.Z
        exact (T.add_Z A).symm.trans (add_eq_hAdd A T.Z)

theorem bridge_P0Z_NF1 (a b : T) (h : T.isNF1 (T.P 0 a b)) :
    T.isNF1 (T.P 0 a T.Z) := by
  obtain ⟨ha, hb, hg, hh⟩ := T.isNF1_P_inv 0 a b h
  exact T.isNF1.p 0 a T.Z ha T.isNF1.z hg (T.Z_le _)

theorem bridge_card_times_le_same (n : Nat) (c d : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d)
    (hcd : c ≤ d) :
    T.card_times n c ≤ T.card_times n d := by
  cases hcd with
  | inl hlt =>
    exact Or.inl (bridge_card_times_lt_same n c d hcNF hcIdx hdNF hdIdx hlt)
  | inr heq =>
    have hEq : c = d := heq
    rw [hEq]
    exact Or.inr rfl

theorem bridge_shift_lt_outer (k : Nat) (c tail : T)
    (hc : T.index_Prop1 0 c) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail := by
  let sh := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c
  change sh < T.P 1 sh tail
  by_cases hz : sh = T.Z
  · rw [hz]
    exact T.Lt.Z_lt_P 1 T.Z tail
  · have h1 : sh < T.P 1 T.Z sh := by
      unfold sh
      exact bridge_shift_lt_wrap k c hc
    have hzs : T.Z < sh := by
      cases hs : sh with
      | Z => exact False.elim (hz hs)
      | P p a b => exact T.Lt.Z_lt_P p a b
    have h2 : T.P 1 T.Z sh < T.P 1 sh tail :=
      T.Lt.p_mid 1 T.Z sh sh tail hzs
    exact lt_trans_thm sh (T.P 1 T.Z sh) (T.P 1 sh tail) h1 h2

theorem bridge_card_times_closed (n : Nat) :
    ∀ c : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 (T.card_times n c) ∧
        T.index_Prop1 1 (T.card_times n c) ∧
        (∀ x : T, x ∈ T.G1 1 (T.card_times n c) →
          x < T.card_times n c) := by
  intro c
  induction c with
  | Z =>
    intro hcNF hcIdx
    rw [T.card_times]
    exact ⟨T.isNF1.z, T.index_Prop1.z, fun x hx => by
      rw [T.G1.eq_1] at hx
      cases hx⟩
  | P p a b iha ihb =>
    intro hcNF hcIdx
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      subst p
      obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
      cases n with
      | zero =>
        rw [T.card_times]
        have hidx1 : T.index_Prop1 1 (T.P 0 a b) :=
          Rank1Termination.index_mono (Nat.zero_le 1) (T.P 0 a b)
            (T.index_Prop1.p 0 a b (Nat.le_refl 0) hbIdx)
        have hempty := index_Prop1_G1_empty 0 (T.P 0 a b)
          (T.index_Prop1.p 0 a b (Nat.le_refl 0) hbIdx) 1 (Nat.zero_lt_succ 0)
        constructor
        · exact hcNF
        · constructor
          · exact hidx1
          · intro x hx
            rw [hempty] at hx
            cases hx
      | succ k =>
        rw [T.card_times, ite_eq_left rfl]
        rw [← add_eq_hAdd, T.P_add_eq, T.add]
        change
          T.isNF1 (T.P 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse a))
            (T.card_times (k + 1) b)) ∧
          T.index_Prop1 1 (T.P 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse a))
            (T.card_times (k + 1) b)) ∧
          ∀ x : T, x ∈ T.G1 1 (T.P 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse a))
            (T.card_times (k + 1) b)) →
            x < T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                (T.early_collapse a))
              (T.card_times (k + 1) b)
        have hec := bridge_early_collapse_closed a haNF haG
        have hshiftNF := bridge_shift_NF k (T.early_collapse a) hec.1 hec.2.1
        have htail := ihb hbNF hbIdx
        have hbaseNF : T.isNF1 (T.P 0 a T.Z) :=
          T.isNF1.p 0 a T.Z haNF T.isNF1.z haG (T.Z_le _)
        have hbaseIdx : T.index_Prop1 0 (T.P 0 a T.Z) :=
          T.index_Prop1.p 0 a T.Z (Nat.le_refl 0) T.index_Prop1.z
        have hheadNF : T.isNF1 (T.head b) := bridge_head_NF1 b hbNF
        have hheadIdx : T.index_Prop1 0 (T.head b) := bridge_head_index0 b hbIdx
        have htailHead :
            T.head (T.card_times (k + 1) b) ≤
              T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a)) T.Z := by
          rw [bridge_card_times_head]
          have hmono := bridge_card_times_le_same (k + 1)
            (T.head b) (T.P 0 a T.Z)
            hheadNF hheadIdx hbaseNF hbaseIdx hheadb
          change T.card_times (k + 1) (T.head b) ≤
            T.card_times (k + 1) (T.P 0 a T.Z)
          exact hmono
        have hcurNF :
            T.isNF1
              (T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a))
                (T.card_times (k + 1) b)) :=
          T.isNF1.p 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse a))
            (T.card_times (k + 1) b)
            hshiftNF htail.1
            (bridge_shift_strong1 k (T.early_collapse a) hec.2.1)
            htailHead
        have hcurIdx :
            T.index_Prop1 1
              (T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a))
                (T.card_times (k + 1) b)) :=
          T.index_Prop1.p 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse a))
            (T.card_times (k + 1) b)
            (Nat.le_refl 1) htail.2.1
        constructor
        · exact hcurNF
        · constructor
          · exact hcurIdx
          · intro x hx
            rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
              List.mem_append, List.mem_append] at hx
            cases hx with
            | inl hleft =>
              cases hleft with
              | inl hmid =>
                have hmidEq : x =
                    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a) := List.mem_singleton.mp hmid
                rw [hmidEq]
                exact bridge_shift_lt_outer k (T.early_collapse a)
                  (T.card_times (k + 1) b) hec.2.1
              | inr hG =>
                have hxmid := bridge_shift_strong1 k (T.early_collapse a) hec.2.1 x hG
                have houter := bridge_shift_lt_outer k (T.early_collapse a)
                  (T.card_times (k + 1) b) hec.2.1
                exact lt_trans_thm x
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                    (T.early_collapse a))
                  (T.P 1
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a))
                    (T.card_times (k + 1) b))
                  hxmid houter
            | inr htailG =>
              have hxtail := htail.2.2 x htailG
              have htailLe : T.card_times (k + 1) b ≤
                  T.P 1
                    (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                      (T.early_collapse a))
                    (T.card_times (k + 1) b) :=
                T.isNF1_tail_le _ hcurNF 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                    (T.early_collapse a))
                  (T.card_times (k + 1) b) rfl
              exact lt_of_lt_of_le_thm T x
                (T.card_times (k + 1) b)
                (T.P 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                    (T.early_collapse a))
                  (T.card_times (k + 1) b))
                hxtail htailLe

#print axioms bridge_card_times_closed
