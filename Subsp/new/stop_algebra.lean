import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans

/-! Algebraic lemmas for collapse, cardinal operations, and translation vectors. -/

/-! Basic normal-form and support properties. -/

section BasicOperations

open T

/-- A term with index and support bounded at level `k` lies below its `k`-wrapper. -/
theorem bridge_good_index_lt_wrap (k : Nat) (a b : T) (hi : T.index_Prop1 k a)
    (hg : ∀ x : T, x ∈ T.G1 k a → x < a) : a < T.P k a b := by
  cases a with
  | Z => exact T.Lt.Z_lt_P k T.Z b
  | P p c d =>
      cases hi with
      | p _ _ _ hp _ =>
          rcases Nat.eq_or_lt_of_le hp with hpk | hpk
          · cases hpk
            apply T.Lt.p_mid k c (T.P k c d) d b
            apply hg c
            rw [T.G1.eq_2, ite_eq_left (Nat.le_refl k)]
            exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self c))
          · exact T.Lt.p_head p k c (T.P p c d) d b hpk

theorem bridge_stand_eq_self_of_NF1 (s : T) (hs : T.isNF1 s) : T.stand s = s := by
  induction hs with
  | z => rw [T.stand]
  | p s0 s1 s2 hs1 hs2 hG hhead _ ih2 =>
    rw [T.stand, ih2, ite_eq_left hhead]

theorem bridge_lt_add_left_of_size_lt (a b x : T)
    (ha : a ≠ T.Z) (hsize : T.size x < T.size a)
    (h : x < T.add a b) : x < a := by
  induction a generalizing x with
  | Z => exact False.elim (ha rfl)
  | P a0 a1 a2 _ ih2 =>
    rw [T.P_add_eq] at h
    cases x with
    | Z => exact T.Lt.Z_lt_P a0 a1 a2
    | P x0 x1 x2 =>
      rcases lt_inv x0 x1 x2 a0 a1 (T.add a2 b) h with hh | (hh | hh)
      · exact T.Lt.p_head x0 a0 x1 a1 x2 a2 hh
      · cases hh.1
        exact T.Lt.p_mid a0 x1 a1 x2 a2 hh.2
      · have hx0 : x0 = a0 := hh.1
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
  | P a0 a1 a2 _ ih2 =>
    rw [T.P_add_eq]
    by_cases hu : u ≤ a0
    · rw [T.G1.eq_2, ite_eq_left hu] at hx
      rw [T.G1.eq_2, ite_eq_left hu]
      rcases List.mem_append.mp hx with hleft | htail
      · exact List.mem_append_left _ hleft
      · exact List.mem_append_right _ (ih2 htail)
    · rw [T.G1.eq_2, ite_eq_right hu] at hx
      rw [T.G1.eq_2, ite_eq_right hu]
      exact ih2 hx

 theorem bridge_isNF1_add_inv_right (a b : T) (h : T.isNF1 (T.add a b)) : T.isNF1 b := by
  induction a with
  | Z =>
    rw [T.add] at h
    exact h
  | P a0 a1 a2 _ ih2 =>
    rw [T.P_add_eq] at h
    have ht := (T.isNF1_P_inv a0 a1 (T.add a2 b) h).2.1
    exact ih2 ht

 theorem bridge_isNF1_add_inv_left (a b : T) (h : T.isNF1 (T.add a b)) : T.isNF1 a := by
  induction a with
  | Z => exact T.isNF1.z
  | P a0 a1 a2 _ ih2 =>
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
  | P s0 s1 s2 _ ih2 =>
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

theorem bridge_part_second_shape (s a b : T) (hp : T.part s = (a, b)) :
    b = T.Z ∨ ∃ c d : T, b = T.P 0 c d := by
  induction s generalizing a b with
  | Z =>
    rw [T.part] at hp
    cases hp
    exact Or.inl rfl
  | P s0 s1 s2 _ ih2 =>
    rw [T.part] at hp
    by_cases h0 : s0 = 0
    · rw [ite_eq_left h0] at hp
      cases hp
      cases h0
      exact Or.inr ⟨s1, s2, rfl⟩
    · rw [ite_eq_right h0] at hp
      cases htail : T.part s2 with
      | mk p q =>
        rw [htail] at hp
        cases hp
        have hq := ih2 p q htail
        rcases hq with hz | hP
        · exact Or.inl hz
        · obtain ⟨c, d, heq⟩ := hP
          exact Or.inr ⟨c, d, heq⟩

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
  rcases bridge_part_second_shape s a b hp with hz | hP
  · rw [hz]
    exact T.index_Prop1.z
  · obtain ⟨c, d, heq⟩ := hP
    rw [heq] at hb ⊢
    exact isNF1_index 0 0 c d hb (Nat.le_refl 0)

theorem bridge_stand_ne_Z (s : T) (hs : s ≠ T.Z) :
    T.stand s ≠ T.Z := by
  induction s with
  | Z => exact False.elim (hs rfl)
  | P p a b _ ihb =>
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

end BasicOperations

/-! Collapse, cardinal arithmetic, and lexicographic translation. -/

section TranslationAlgebra

open T

theorem bridge_early_collapse_closed (s : T)
    (hs : T.isNF1 s)
    (hg : ∀ x : T, x ∈ T.G1 0 s → x < s) :
    T.isNF1 (T.early_collapse s) ∧
      T.index_Prop1 0 (T.early_collapse s) ∧
      (∀ x : T, x ∈ T.G1 1 (T.early_collapse s) → x < T.early_collapse s) := by
  cases s with
  | Z =>
    change T.isNF1 T.Z ∧ T.index_Prop1 0 T.Z ∧
      (∀ x : T, x ∈ T.G1 1 T.Z → x < T.Z)
    exact ⟨T.isNF1.z, T.index_Prop1.z, by
      intro x hx
      rw [T.G1.eq_1] at hx
      cases hx⟩
  | P s0 s1 s2 =>
    by_cases hs0 : s0 = 0
    · have hec : T.early_collapse (T.P s0 s1 s2) = T.P s0 s1 s2 := by
        rw [T.early_collapse, T.part, ite_eq_left hs0]
        rfl
      rw [hec]
      cases hs0
      have hindex : T.index_Prop1 0 (T.P 0 s1 s2) :=
        isNF1_index 0 0 s1 s2 hs (Nat.le_refl 0)
      exact ⟨hs, hindex, by
        intro x hx
        have hempty := index_Prop1_G1_empty 0 (T.P 0 s1 s2) hindex 1 (Nat.zero_lt_succ 0)
        rw [hempty] at hx
        cases hx⟩
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
          exact ⟨hkeep, hindex, by
            intro x hx
            have hempty := index_Prop1_G1_empty 0 (T.P 0 p b) hindex 1 (Nat.zero_lt_succ 0)
            rw [hempty] at hx
            cases hx⟩
        · rw [ite_eq_right hhead]
          exact ⟨hbNF, hbIndex, by
            intro x hx
            have hempty := index_Prop1_G1_empty 0 b hbIndex 1 (Nat.zero_lt_succ 0)
            rw [hempty] at hx
            cases hx⟩

theorem bridge_add_left_lt (p a b : T) (h : a < b) :
    T.add p a < T.add p b := by
  induction p with
  | Z =>
    rw [T.add, T.add]
    exact h
  | P p0 p1 p2 _ ih2 =>
    rw [T.P_add_eq, T.P_add_eq]
    exact T.Lt.p_tail p0 p1 (T.add p2 a) (T.add p2 b) ih2

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
        cases hp0
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
        cases hp0
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
    rcases hx with (hz | hzG) | htail
    · have heq : x = T.Z := List.mem_singleton.mp hz
      rw [heq]
      exact T.Lt.Z_lt_P 1 T.Z _
    · rw [T.G1.eq_1] at hzG
      cases hzG
    · have hxtail := ih x htail
      have htailwrap := bridge_shift_lt_wrap k c hc
      exact lt_trans_thm x _ _ hxtail htailwrap

theorem bridge_part_fst_head_le (s : T) :
    T.head (T.part s).1 ≤ T.head s := by
  cases s with
  | Z =>
      change T.Z ≤ T.Z
      exact Or.inr rfl
  | P p a b =>
      rw [T.part]
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        exact T.Z_le (T.head (T.P p a b))
      · rw [ite_eq_right hp]
        cases hpart : T.part b with
        | mk c d =>
            change T.P p a T.Z ≤ T.P p a T.Z
            exact Or.inr rfl

theorem bridge_part_NF1 (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.part s).1 ∧ T.isNF1 (T.part s).2 := by
  induction hs with
  | z => exact ⟨T.isNF1.z, T.isNF1.z⟩
  | p p a b ha hb hg hh _ ihb =>
      rw [T.part]
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        exact ⟨T.isNF1.z, T.isNF1.p p a b ha hb hg hh⟩
      · rw [ite_eq_right hp]
        cases hpart : T.part b with
        | mk c d =>
            have hcnf : T.isNF1 c := by
              have h := ihb.1
              rw [hpart] at h
              exact h
            have hdnf : T.isNF1 d := by
              have h := ihb.2
              rw [hpart] at h
              exact h
            have hcle : T.head c ≤ T.head b := by
              have h := bridge_part_fst_head_le b
              rw [hpart] at h
              exact h
            have hhead : T.head c ≤ T.P p a T.Z :=
              partial_order.trans (T.head c) (T.head b) (T.P p a T.Z) hcle hh
            exact ⟨T.isNF1.p p a c ha hcnf hg hhead, hdnf⟩

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
  | P p x y _ ihy =>
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
            rcases hinv with hpq | (hm | ht)
            · have hpzero : p < 0 := by rw [hq0] at hpq; exact hpq
              exact False.elim (Nat.not_lt_zero p hpzero)
            · have hpq : p = 0 := by rw [hq0] at hm; exact hm.1
              exact False.elim (hp0 hpq)
            · have hpq : p = 0 := by rw [hq0] at ht; exact ht.1
              exact False.elim (hp0 hpq)
          · rw [ite_eq_right hq0]
            cases hvp : T.part v with
            | mk c d =>
              have hinv := lt_inv p x y q u v h
              rcases hinv with hpq | (hm | ht)
              · exact Or.inl (T.Lt.p_head p q x u a c hpq)
              · cases hm.1
                exact Or.inl (T.Lt.p_mid p x u a c hm.2)
              · cases ht.1
                cases ht.2.1
                have hrec := ihy v ht.2.2
                rw [hyp, hvp] at hrec
                rcases hrec with hac | heq
                · exact Or.inl (T.Lt.p_tail p x a c hac)
                · apply Or.inr
                  constructor
                  · have hac : a = c := heq.1
                    rw [hac]
                  · exact heq.2

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

theorem bridge_part_fst_fixed (s : T) :
    T.part (T.part s).1 = ((T.part s).1, T.Z) := by
  induction s with
  | Z => rfl
  | P p a b _ ihb =>
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
  | P p a b _ ihb =>
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

theorem bridge_part_lt_of_cases (s t : T)
    (h : (T.part s).1 < (T.part t).1 ∨
      ((T.part s).1 = (T.part t).1 ∧ (T.part s).2 < (T.part t).2)) :
    s < t := by
  rcases lt_total_thm s t with hst | (hts | heqst)
  · exact hst
  · have hr := part_lt_cases t s hts
    rcases h with hfst | heq
    · cases hr with
      | inl hrev =>
        exact False.elim (lt_asymm_thm hfst hrev)
      | inr hrev =>
        rw [hrev.1] at hfst
        exact False.elim (lt_irrefl_thm _ hfst)
    · cases hr with
      | inl hrev =>
        rw [heq.1] at hrev
        exact False.elim (lt_irrefl_thm (T.part t).1 hrev)
      | inr hrev =>
        exact False.elim (lt_asymm_thm heq.2 hrev.2)
  · have hp : T.part s = T.part t := congrArg T.part heqst
    rcases h with hfst | hsnd
    · rw [hp] at hfst
      exact False.elim (lt_irrefl_thm (T.part t).1 hfst)
    · rw [hp] at hsnd
      exact False.elim (lt_irrefl_thm (T.part t).2 hsnd.2)

theorem bridge_lt_of_not_le (a b : T) (h : ¬ a ≤ b) : b < a := by
  rcases lt_total_thm a b with hab | (hba | heq)
  · exact False.elim (h (Or.inl hab))
  · exact hba
  · exact False.elim (h (Or.inr heq))

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
  rcases hbshape with hbz | hbp
  · cases hbz
    rcases hdshape with hdz | hdp
    · cases hdz
      exact False.elim (lt_irrefl_thm T.Z hbd)
    · obtain ⟨f, g, hdeq⟩ := hdp
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
        rcases lt_inv 0 a T.Z 0 f T.Z haf with hzero | (hm | ht)
        · exact False.elim (Nat.lt_irrefl 0 hzero)
        · exact T.Lt.p_mid 0 a f T.Z g hm.2
        · exact False.elim (lt_Z_inv ht.2.2)
  · obtain ⟨c, e, hbeq⟩ := hbp
    cases hbeq
    rcases hdshape with hdz | hdp
    · cases hdz
      exact False.elim (lt_Z_inv hbd)
    · obtain ⟨f, g, hdeq⟩ := hdp
      cases hdeq
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
          rcases lt_inv 0 a T.Z 0 f T.Z haf with hzero | (hm | ht)
          · exact False.elim (Nat.lt_irrefl 0 hzero)
          · exact T.Lt.p_mid 0 a f (T.P 0 c e) g hm.2
          · exact False.elim (lt_Z_inv ht.2.2)
      · rw [ite_eq_right hca]
        by_cases hfa : T.P 0 f T.Z ≤ T.P 0 a T.Z
        · rw [ite_eq_left hfa]
          have hcf : c < f ∨ (c = f ∧ e < g) := by
            rcases lt_inv 0 c e 0 f g hbd with hzero | (hm | ht)
            · exact False.elim (Nat.lt_irrefl 0 hzero)
            · exact Or.inl hm.2
            · exact Or.inr ⟨ht.2.1, ht.2.2⟩
          rcases hcf with hcf | heq
          · have hclef : c ≤ f := Or.inl hcf
            have hflea : f ≤ a := by
              rcases hfa with hlt | heq
              · cases lt_inv 0 f T.Z 0 a T.Z hlt with
                | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
                | inr hor =>
                  rcases hor with hm | ht
                  · exact Or.inl hm.2
                  · exact Or.inr ht.2.1
              · cases heq
                exact Or.inr rfl
            have hcla : c ≤ a := partial_order.trans c f a hclef hflea
            have hheadca : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
              rcases hcla with hlt | heq
              · exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z hlt)
              · rw [heq]; exact Or.inr rfl
            exact False.elim (hca hheadca)
          · have hcfEq : c = f := heq.1
            cases hcfEq
            have hclea : c ≤ a := by
              rcases hfa with hlt | heqca
              · cases lt_inv 0 c T.Z 0 a T.Z hlt with
                | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
                | inr hor =>
                  rcases hor with hm | ht
                  · exact Or.inl hm.2
                  · exact Or.inr ht.2.1
              · cases heqca
                exact Or.inr rfl
            have hheadca : T.P 0 c T.Z ≤ T.P 0 a T.Z := by
              rcases hclea with hlt | heqca
              · exact Or.inl (T.Lt.p_mid 0 c a T.Z T.Z hlt)
              · rw [heqca]; exact Or.inr rfl
            exact False.elim (hca hheadca)
        · rw [ite_eq_right hfa]
          exact hbd

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
      rcases T.Z_le (T.part s).2 with hlt | heq
      · exact hlt
      · exact False.elim (hb heq.symm)
    exact Or.inr ⟨rfl, hzb⟩

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
      have hbshape := bridge_part_second_shape s a b hp
      rcases hbshape with hbz | hbp
      · rw [hbz]
        exact T.Lt.Z_lt_P 0 c T.Z
      · obtain ⟨e, f, hbeq⟩ := hbp
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
        rcases hbshape with hbz | hbp
        · rw [hbz]
          exact T.Lt.Z_lt_P 0 c T.Z
        · obtain ⟨e, f, hbeq⟩ := hbp
          rw [hbeq]
          have hes : e < s := bridge_remainder_member_lt s a e f (by
            rw [hbeq] at hp
            exact hp) hg
          have hecLt : e < c := lt_trans_thm e s c hes hsc
          exact T.Lt.p_mid 0 e c f T.Z hecLt

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
      rcases T.Z_le d with hzd | hzd
      · exact Or.inl (T.Lt.p_tail 0 c T.Z d hzd)
      · have hdZ : d = T.Z := hzd.symm
        rw [hdZ]
        exact Or.inr rfl
    · rw [ite_eq_right hhead]
      have hbaseHead : T.P 0 c T.Z < T.head d :=
        bridge_lt_of_not_le (T.head d) (T.P 0 c T.Z) hhead
      have hheadD : T.head d ≤ d := bridge_head_le_self d
      exact Or.inl (lt_of_lt_of_le_thm T (T.P 0 c T.Z) (T.head d) d
        hbaseHead hheadD)

theorem bridge_early_collapse_lt (s t : T)
    (hs : T.isNF1 s)
    (hsg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t)
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
      rcases hparts with hac | heq
      · have hsc0 := bridge_part_prefix_upper s t
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
      · have hacEq : a = c := heq.1
        have hbd : b < d := heq.2
        cases hacEq
        by_cases ha : a = T.Z
        · have hecs := bridge_early_collapse_part s a b hps hbNF
          have hect := bridge_early_collapse_part t a d hpt hdNF
          rw [hecs, hect, ite_eq_left ha, ite_eq_left ha]
          exact hbd
        · rw [T.early_collapse, hps, ite_eq_right ha]
          rw [T.early_collapse, hpt, ite_eq_right ha]
          exact bridge_insert_lt a b d hbNF hdNF hbfix hdfix hbd

theorem bridge_card_times_lt_same (n : Nat) :
    ∀ c d : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 d → T.index_Prop1 0 d →
      c < d → T.card_times n c < T.card_times n d := by
  intro c
  induction c with
  | Z =>
    intro d _ _ _ _ hcd
    have hdne : d ≠ T.Z := by
      intro heq
      rw [heq] at hcd
      exact lt_Z_inv hcd
    have hctne : T.card_times n d ≠ T.Z := bridge_card_times_ne_Z n d hdne
    rcases T.Z_le (T.card_times n d) with hlt | heq
    · rw [T.card_times]
      exact hlt
    · exact False.elim (hctne heq.symm)
  | P p a b iha ihb =>
    intro d hcNF hcIdx hdNF hdIdx hcd
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      cases hp
      cases d with
      | Z => exact False.elim (lt_Z_inv hcd)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq0 hfIdx =>
          have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
          cases hq
          obtain ⟨haNF, hbNF, haG, _⟩ := T.isNF1_P_inv 0 a b hcNF
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
            rcases lt_inv 0 a b 0 e f hcd with hz | (hmid | htail)
            · exact False.elim (Nat.lt_irrefl 0 hz)
            · have hae : a < e := hmid.2
              have hec : T.early_collapse a < T.early_collapse e :=
                bridge_early_collapse_lt a e haNF haG heNF hae
              have hshift := bridge_add_left_lt
                (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                (T.early_collapse a) (T.early_collapse e) hec
              exact T.Lt.p_mid 1 _ _ _ _ hshift
            · have hae : a = e := htail.2.1
              cases hae
              have hbf : b < f := htail.2.2
              have hrec := ihb f hbNF hbIdx hfNF hfIdx hbf
              exact T.Lt.p_tail 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a))
                (T.card_times (k + 1) b)
                (T.card_times (k + 1) f) hrec

theorem bridge_shift_level_lt : ∀ k l : Nat, k < l →
    ∀ x y : T, T.index_Prop1 0 x → T.index_Prop1 0 y →
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) x <
      T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) y := by
  intro k
  induction k with
  | zero =>
    intro l hkl x y hx _
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
          cases hp0
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
      cases hp
      cases d with
      | Z => exact False.elim (hdne rfl)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq0 hfIdx =>
          have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
          cases hq
          obtain ⟨haNF, _, haG, _⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, _, heG, _⟩ := T.isNF1_P_inv 0 e f hdNF
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

theorem bridge_add_left_le (p a b : T) (h : a ≤ b) :
    T.add p a ≤ T.add p b := by
  rcases h with hlt | heq
  · exact Or.inl (bridge_add_left_lt p a b hlt)
  · rw [heq]; exact Or.inr rfl

theorem bridge_shift_lt_outer (k : Nat) (c tail : T)
    (hc : T.index_Prop1 0 c) :
    T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c <
      T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail := by
  cases k with
  | zero =>
    rw [T.ofNat, T.mul, T.add]
    cases c with
    | Z => exact T.Lt.Z_lt_P 1 T.Z tail
    | P p a b =>
      cases hc with
      | p _ _ _ hp hidx =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        cases hp0
        exact T.Lt.p_head 0 1 a (T.P 0 a b) b tail (Nat.zero_lt_succ 0)
  | succ k =>
    rw [mul_succ_shape 1 T.Z k, T.P_add_eq]
    exact T.Lt.p_mid 1 T.Z
      (T.P 1 T.Z (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c))
      (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) c) tail
      (T.Lt.Z_lt_P 1 T.Z _)

theorem bridge_early_collapse_le (s t : T)
    (hs : T.isNF1 s) (hsg : ∀ x : T, x ∈ T.G1 0 s → x < s)
    (ht : T.isNF1 t)
    (hst : s ≤ t) : T.early_collapse s ≤ T.early_collapse t := by
  rcases hst with hlt | heq
  · exact Or.inl (bridge_early_collapse_lt s t hs hsg ht hlt)
  · rw [heq]; exact Or.inr rfl

theorem bridge_P0_head_mid_le (a e f : T)
    (h : T.head (T.P 0 e f) ≤ T.P 0 a T.Z) : e ≤ a := by
  change T.P 0 e T.Z ≤ T.P 0 a T.Z at h
  rcases h with hlt | heq
  · cases lt_inv 0 e T.Z 0 a T.Z hlt with
    | inl hz => exact False.elim (Nat.lt_irrefl 0 hz)
    | inr hor =>
      rcases hor with hm | ht
      · exact Or.inl hm.2
      · exact Or.inr ht.2.1
  · cases heq
    exact Or.inr rfl

theorem bridge_lift_P1_le (a b : T) (h : a ≤ b) :
    T.P 1 a T.Z ≤ T.P 1 b T.Z := by
  rcases h with hlt | heq
  · exact Or.inl (T.Lt.p_mid 1 a b T.Z T.Z hlt)
  · rw [heq]; exact Or.inr rfl

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
    intro _ _
    rw [T.card_times]
    exact ⟨T.isNF1.z, T.index_Prop1.z, by
      intro x hx
      rw [T.G1.eq_1] at hx
      cases hx⟩
  | P p a b iha ihb =>
    intro hcNF hcIdx
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      cases hp
      obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
      cases n with
      | zero =>
        rw [T.card_times]
        have hidx0 : T.index_Prop1 0 (T.P 0 a b) :=
          T.index_Prop1.p 0 a b (Nat.le_refl 0) hbIdx
        have hidx1 : T.index_Prop1 1 (T.P 0 a b) :=
          Rank1Termination.index_mono (Nat.zero_le 1) (T.P 0 a b) hidx0
        have hempty := index_Prop1_G1_empty 0 (T.P 0 a b) hidx0 1
          (Nat.zero_lt_succ 0)
        constructor
        · exact hcNF
        · constructor
          · exact hidx1
          · intro x hx
            rw [hempty] at hx
            cases hx
      | succ k =>
        rw [T.card_times, ite_eq_left rfl]
        rw [← add_eq_hAdd
              (T.P 1
                ((T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) +
                  (T.early_collapse a)) T.Z)
              (T.card_times (k + 1) b),
            T.P_add_eq, T.add.eq_1]
        let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
          (T.early_collapse a)
        let R := T.card_times (k + 1) b
        change
          T.isNF1 (T.P 1 M R) ∧
            T.index_Prop1 1 (T.P 1 M R) ∧
              (∀ x : T, x ∈ T.G1 1 (T.P 1 M R) → x < T.P 1 M R)
        have hec := bridge_early_collapse_closed a haNF haG
        have hMNF : T.isNF1 M := by
          unfold M
          exact bridge_shift_NF k (T.early_collapse a) hec.1 hec.2.1
        have hMG : ∀ x : T, x ∈ T.G1 1 M → x < M := by
          unfold M
          exact bridge_shift_strong1 k (T.early_collapse a) hec.2.1
        have htail := ihb hbNF hbIdx
        have hRhead : T.head R ≤ T.P 1 M T.Z := by
          cases b with
          | Z =>
            unfold R
            rw [T.card_times, T.head]
            exact T.Z_le (T.P 1 M T.Z)
          | P q e f =>
            cases hbIdx with
            | p _ _ _ hq0 hfIdx =>
              have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
              cases hq
              obtain ⟨heNF, _, heG, _⟩ := T.isNF1_P_inv 0 e f hbNF
              have hea : e ≤ a := bridge_P0_head_mid_le a e f hheadb
              have hecLe : T.early_collapse e ≤ T.early_collapse a :=
                bridge_early_collapse_le e a heNF heG haNF hea
              have hshiftLe :
                  T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                    (T.early_collapse e) ≤ M := by
                unfold M
                exact bridge_add_left_le
                  (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse e) (T.early_collapse a) hecLe
              unfold R
              rw [T.card_times, ite_eq_left rfl]
              rw [← add_eq_hAdd
                (T.P 1
                  ((T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) +
                    (T.early_collapse e)) T.Z)
                (T.card_times (k + 1) f), T.P_add_eq, T.add.eq_1]
              rw [T.head]
              exact bridge_lift_P1_le _ _ hshiftLe
        have hcurNF : T.isNF1 (T.P 1 M R) :=
          T.isNF1.p 1 M R hMNF htail.1 hMG hRhead
        have hcurIdx : T.index_Prop1 1 (T.P 1 M R) :=
          T.index_Prop1.p 1 M R (Nat.le_refl 1) htail.2.1
        constructor
        · exact hcurNF
        · constructor
          · exact hcurIdx
          · intro x hx
            rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
              List.mem_append, List.mem_append] at hx
            rcases hx with (hxm | hxG) | hxR
            · have hxEq : x = M := List.mem_singleton.mp hxm
              rw [hxEq]
              unfold M
              exact bridge_shift_lt_outer k (T.early_collapse a) R hec.2.1
            · have hxM : x < M := hMG x hxG
              have hMwhole : M < T.P 1 M R := by
                unfold M
                exact bridge_shift_lt_outer k (T.early_collapse a) R hec.2.1
              exact lt_trans_thm x M (T.P 1 M R) hxM hMwhole
            · have hxRt : x < R := htail.2.2 x hxR
              have hRle : R ≤ T.P 1 M R :=
                T.isNF1_tail_le (T.P 1 M R) hcurNF 1 M R rfl
              exact lt_of_lt_of_le_thm T x R (T.P 1 M R) hxRt hRle

theorem bridge_head_add_ne_Z (a b : T) (ha : a ≠ T.Z) :
    T.head (T.add a b) = T.head a := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P p c d => exact T.head_add_ne_Z p c d b

theorem bridge_card_times_succ_append (k : Nat) :
    ∀ c y : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 y → T.index_Prop1 1 y →
      (∀ x : T, x ∈ T.G1 1 y → x < y) →
      (∀ z : T, T.isNF1 z → T.index_Prop1 0 z → z ≠ T.Z →
        y < T.card_times (k + 1) z) →
      T.isNF1 (T.add (T.card_times (k + 1) c) y) ∧
        T.index_Prop1 1 (T.add (T.card_times (k + 1) c) y) ∧
        (∀ x : T,
          x ∈ T.G1 1 (T.add (T.card_times (k + 1) c) y) →
          x < T.add (T.card_times (k + 1) c) y) := by
  intro c
  induction c with
  | Z =>
    intro y _ _ hyNF hyIdx hyG _
    rw [T.card_times.eq_1, T.add.eq_1]
    exact ⟨hyNF, hyIdx, hyG⟩
  | P p a b _ ihb =>
    intro y hcNF hcIdx hyNF hyIdx hyG hbound
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      cases hp
      obtain ⟨haNF, hbNF, haG, hheadb⟩ := T.isNF1_P_inv 0 a b hcNF
      have hec := bridge_early_collapse_closed a haNF haG
      let M := T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
        (T.early_collapse a)
      have hMNF : T.isNF1 M := by
        unfold M
        exact bridge_shift_NF k (T.early_collapse a) hec.1 hec.2.1
      have hMG : ∀ x : T, x ∈ T.G1 1 M → x < M := by
        unfold M
        exact bridge_shift_strong1 k (T.early_collapse a) hec.2.1
      have htail := ihb y hbNF hbIdx hyNF hyIdx hyG hbound
      let R := T.add (T.card_times (k + 1) b) y
      have hRNF : T.isNF1 R := by
        unfold R
        exact htail.1
      have hRIdx : T.index_Prop1 1 R := by
        unfold R
        exact htail.2.1
      have hRG : ∀ x : T, x ∈ T.G1 1 R → x < R := by
        unfold R
        exact htail.2.2
      have hRhead : T.head R ≤ T.P 1 M T.Z := by
        cases b with
        | Z =>
          unfold R
          rw [T.card_times.eq_1, T.add.eq_1]
          have hzNF : T.isNF1 (T.P 0 a T.Z) :=
            T.isNF1.p 0 a T.Z haNF T.isNF1.z haG (T.Z_le _)
          have hzIdx : T.index_Prop1 0 (T.P 0 a T.Z) :=
            T.index_Prop1.p 0 a T.Z (Nat.le_refl 0) T.index_Prop1.z
          have hylt := hbound (T.P 0 a T.Z) hzNF hzIdx (by
            intro heq
            cases heq)
          rw [T.card_times.eq_3, ite_eq_left rfl] at hylt
          rw [← add_eq_hAdd
                (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                (T.card_times (k + 1) T.Z),
              T.card_times.eq_1, T.add_Z] at hylt
          have hheadle := T.head_mono hylt
          unfold M
          exact hheadle
        | P q e f =>
          have hbne : T.P q e f ≠ T.Z := by intro heq; cases heq
          unfold R
          rw [bridge_head_add_ne_Z (T.card_times (k + 1) (T.P q e f)) y
            (bridge_card_times_ne_Z (k + 1) (T.P q e f) hbne)]
          have hclosed := bridge_card_times_closed (k + 1) (T.P 0 a (T.P q e f)) hcNF
            (T.index_Prop1.p 0 a (T.P q e f) (Nat.le_refl 0) hbIdx)
          have hinv := T.isNF1_P_inv 1 M (T.card_times (k + 1) (T.P q e f)) (by
            -- identify the closed term with its unfolded card-times shape
            rw [T.card_times.eq_3, ite_eq_left rfl] at hclosed
            rw [← add_eq_hAdd
                  (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                  (T.card_times (k + 1) (T.P q e f)),
                T.P_add_eq, T.add.eq_1] at hclosed
            have hclosedNF := hclosed.1
            change T.isNF1 (T.P 1 M (T.card_times (k + 1) (T.P q e f))) at hclosedNF
            exact hclosedNF)
          exact hinv.2.2.2
      have hwholeNF : T.isNF1 (T.P 1 M R) :=
        T.isNF1.p 1 M R hMNF hRNF hMG hRhead
      have hwholeIdx : T.index_Prop1 1 (T.P 1 M R) :=
        T.index_Prop1.p 1 M R (Nat.le_refl 1) hRIdx
      have hwholeG : ∀ x : T, x ∈ T.G1 1 (T.P 1 M R) → x < T.P 1 M R := by
        intro x hx
        rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 1),
          List.mem_append, List.mem_append] at hx
        rcases hx with (hxm | hxG) | hxR
        · have hxEq : x = M := List.mem_singleton.mp hxm
          rw [hxEq]
          unfold M
          exact bridge_shift_lt_outer k (T.early_collapse a) R hec.2.1
        · have hxM : x < M := hMG x hxG
          have hMwhole : M < T.P 1 M R := by
            unfold M
            exact bridge_shift_lt_outer k (T.early_collapse a) R hec.2.1
          exact lt_trans_thm x M (T.P 1 M R) hxM hMwhole
        · have hxRt : x < R := hRG x hxR
          have hRle : R ≤ T.P 1 M R :=
            T.isNF1_tail_le (T.P 1 M R) hwholeNF 1 M R rfl
          exact lt_of_lt_of_le_thm T x R (T.P 1 M R) hxRt hRle
      rw [T.card_times.eq_3, ite_eq_left rfl]
      rw [← add_eq_hAdd
            (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
            (T.card_times (k + 1) b), T.P_add_eq, T.add.eq_1]
      rw [T.P_add_eq]
      change
        T.isNF1 (T.P 1 M R) ∧
          T.index_Prop1 1 (T.P 1 M R) ∧
            (∀ x : T, x ∈ T.G1 1 (T.P 1 M R) → x < T.P 1 M R)
      exact ⟨hwholeNF, hwholeIdx, hwholeG⟩

theorem bridge_card_times_add_level_lt (m n : Nat) (c d y : T)
    (hmn : m < n)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) (hcne : c ≠ T.Z)
    (hdNF : T.isNF1 d) (hdIdx : T.index_Prop1 0 d) (hdne : d ≠ T.Z) :
    T.add (T.card_times m c) y < T.card_times n d := by
  cases c with
  | Z => exact False.elim (hcne rfl)
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp0 hbIdx =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hp0
      cases hp
      cases d with
      | Z => exact False.elim (hdne rfl)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq0 hfIdx =>
          have hq : q = 0 := Nat.eq_zero_of_le_zero hq0
          cases hq
          obtain ⟨haNF, _, haG, _⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, _, heG, _⟩ := T.isNF1_P_inv 0 e f hdNF
          have haEC := bridge_early_collapse_closed a haNF haG
          have heEC := bridge_early_collapse_closed e heNF heG
          cases m with
          | zero =>
            cases n with
            | zero => exact False.elim (Nat.lt_irrefl 0 hmn)
            | succ l =>
              rw [T.card_times.eq_2, T.P_add_eq]
              rw [T.card_times.eq_3, ite_eq_left rfl]
              rw [← add_eq_hAdd
                    (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat l) + T.early_collapse e) T.Z)
                    (T.card_times (l + 1) f),
                  T.P_add_eq, T.add.eq_1]
              exact T.Lt.p_head 0 1 a
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat l)) (T.early_collapse e))
                (T.add b y) (T.card_times (l + 1) f) (Nat.zero_lt_succ 0)
          | succ k =>
            cases n with
            | zero => exact False.elim (Nat.not_lt_zero (k + 1) hmn)
            | succ l =>
              have hkl : k < l := Nat.lt_of_succ_lt_succ hmn
              rw [T.card_times.eq_3, ite_eq_left rfl]
              rw [← add_eq_hAdd
                    (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a) T.Z)
                    (T.card_times (k + 1) b),
                  T.P_add_eq, T.add.eq_1]
              rw [T.P_add_eq]
              rw [T.card_times.eq_3, ite_eq_left rfl]
              rw [← add_eq_hAdd
                    (T.P 1 ((T.P 1 T.Z T.Z).mul (T.ofNat l) + T.early_collapse e) T.Z)
                    (T.card_times (l + 1) f),
                  T.P_add_eq, T.add.eq_1]
              have hshift := bridge_shift_level_lt k l hkl
                (T.early_collapse a) (T.early_collapse e) haEC.2.1 heEC.2.1
              exact T.Lt.p_mid 1 _ _ _ _ hshift

theorem bridge_lt_P0ZZ_eq_Z (x : T) (h : x < T.P 0 T.Z T.Z) : x = T.Z := by
  cases x with
  | Z => rfl
  | P p a b =>
    rcases lt_inv p a b 0 T.Z T.Z h with hp | (hm | ht)
    · exact False.elim (Nat.not_lt_zero p hp)
    · exact False.elim (lt_Z_inv hm.2)
    · exact False.elim (lt_Z_inv ht.2.2)

-- From AuxBridge.lean

-- From TransCore.lean

theorem tc_trans_P_add {lam : Nat} (ls : new.Vec (new.T lam) lam) (a : new.T lam) :
    trans (new.T.P ls a) = T.add (trans (new.T.P ls new.T.Z)) (trans a) := by
  rw [_root_.trans.eq_2 ls a, _root_.trans.eq_2 ls new.T.Z, _root_.trans.eq_1]
  cases haux : transAux ls with
  | mk found rest =>
    obtain ⟨sum, a0⟩ := rest
    change
      (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans a)
       else if a0 = T.Z then T.P 0 T.Z (trans a) else T.P 0 a0 (trans a)) =
      T.add
        (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
         else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z)
        (trans a)
    by_cases hf : found = true
    · rw [ite_eq_left hf, ite_eq_left hf, T.P_add_eq, T.add]
    · rw [ite_eq_right hf, ite_eq_right hf]
      by_cases ha0 : a0 = T.Z
      · rw [ite_eq_left ha0, ite_eq_left ha0, T.P_add_eq, T.add]
      · rw [ite_eq_right ha0, ite_eq_right ha0, T.P_add_eq, T.add]

theorem tc_trans_head {lam : Nat} (s : new.T lam) :
    trans (new.T.head s) = T.head (trans s) := by
  cases s with
  | Z => rfl
  | P ls a =>
    rw [new.T.head, _root_.trans.eq_2 ls new.T.Z, _root_.trans.eq_1,
      _root_.trans.eq_2 ls a]
    cases haux : transAux ls with
    | mk found rest =>
      obtain ⟨sum, a0⟩ := rest
      change
        (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) T.Z
         else if a0 = T.Z then T.P 0 T.Z T.Z else T.P 0 a0 T.Z) =
        T.head
          (if found = true then T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans a)
           else if a0 = T.Z then T.P 0 T.Z (trans a) else T.P 0 a0 (trans a))
      by_cases hf : found = true
      · rw [ite_eq_left hf, ite_eq_left hf]
        rfl
      · rw [ite_eq_right hf, ite_eq_right hf]
        by_cases ha0 : a0 = T.Z
        · rw [ite_eq_left ha0, ite_eq_left ha0]
          rfl
        · rw [ite_eq_right ha0, ite_eq_right ha0]
          rfl

-- From AuxCore.lean

theorem tc_trans_ne_Z_of_ne_Z {lam : Nat} (s : new.T lam)
    (hs : s ≠ new.T.Z) : trans s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hs rfl)
  | P ls add =>
    rw [_root_.trans.eq_2]
    cases haux : transAux ls with
    | mk found rest =>
      obtain ⟨sum, a0⟩ := rest
      change
        (if found = true then
          T.P 1 (T.card_times 1 (T.one_del sum) + T.early_collapse a0) (trans add)
        else if a0 = T.Z then T.P 0 T.Z (trans add)
        else T.P 0 a0 (trans add)) ≠ T.Z
      split
      · intro h; cases h
      · split <;> intro h <;> cases h

theorem tc_Z_lt_of_ne (x : T) (hx : x ≠ T.Z) : T.Z < x := by
  rcases T.Z_le x with h | h
  · exact h
  · exact False.elim (hx h.symm)

theorem tc_add_ne_Z_left (a b : T) (ha : a ≠ T.Z) : a + b ≠ T.Z := by
  cases a with
  | Z => exact False.elim (ha rfl)
  | P p c d =>
    cases b <;> intro h <;> cases h

theorem tc_card_times_zero (c : T) : T.card_times 0 c = c := by
  cases c with
  | Z => rfl
  | P p a b => rfl

theorem tc_transAux_inv {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        T.isNF1 a0 ∧
          (∀ y : T, y ∈ T.G1 0 a0 → y < a0) ∧
          T.isNF1 sum ∧
          T.index_Prop1 1 sum ∧
          (∀ y : T, y ∈ T.G1 1 sum → y < sum) ∧
          (∀ c : T,
            T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
              sum < T.card_times k c) ∧
          (found = true → sum ≠ T.Z) ∧
          (found = false → sum = T.Z) := by
  intro k
  induction k with
  | zero =>
      intro v hcomp found sum a0 haux
      cases v with
      | snoc n xs a =>
        cases xs with
        | nil =>
          rw [transAux.eq_2] at haux
          cases haux
          have ha := hcomp a (List.mem_singleton.mpr rfl)
          refine ⟨ha.1, ha.2, T.isNF1.z, T.index_Prop1.z, ?_, ?_, ?_, ?_⟩
          · intro y hy
            rw [T.G1.eq_1] at hy
            cases hy
          · intro c _ _ hcne
            rw [tc_card_times_zero]
            exact tc_Z_lt_of_ne c hcne
          · intro h
            cases h
          · intro _
            rfl
  | succ m ih =>
      intro v hcomp found sum a0 haux
      cases v with
      | snoc n xs a =>
        have hrest :
            ∀ x : new.T lam, x ∈ new.Vec.toList xs →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
          intro x hx
          exact hcomp x (List.mem_append_left [a] hx)
        have ha :
            T.isNF1 (trans a) ∧
              (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
          apply hcomp a
          exact List.mem_append_right (new.Vec.toList xs)
            (List.mem_singleton.mpr rfl)
        cases hrestaux : transAux xs with
        | mk foundRest restpair =>
          obtain ⟨sumRest, a0Rest⟩ := restpair
          have ihr := ih xs hrest foundRest sumRest a0Rest hrestaux
          rw [transAux.eq_3, hrestaux] at haux
          cases a with
          | Z =>
            change
              (foundRest, T.card_times m (T.early_collapse (trans new.T.Z)) + sumRest, a0Rest) =
                (found, sum, a0) at haux
            rw [_root_.trans.eq_1] at haux
            change (foundRest, sumRest, a0Rest) = (found, sum, a0) at haux
            cases haux
            refine ⟨ihr.1, ihr.2.1, ihr.2.2.1, ihr.2.2.2.1,
              ihr.2.2.2.2.1, ?_, ihr.2.2.2.2.2.2.1, ihr.2.2.2.2.2.2.2⟩
            intro c hcNF hcIdx hcne
            have hold := ihr.2.2.2.2.2.1 c hcNF hcIdx hcne
            have hnext := bridge_card_times_level_lt m (m + 1) c c
              (Nat.lt_succ_self m) hcNF hcIdx hcne hcNF hcIdx hcne
            exact lt_trans_thm _ _ _ hold hnext
          | P als aadd =>
            have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
              intro h
              cases h
            have hatne : trans (new.T.P als aadd) ≠ T.Z :=
              tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
            have hec := bridge_early_collapse_closed
              (trans (new.T.P als aadd)) ha.1 ha.2
            have hecne : T.early_collapse (trans (new.T.P als aadd)) ≠ T.Z :=
              bridge_early_collapse_ne_Z (trans (new.T.P als aadd)) hatne
            change
              (true,
                T.card_times m (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                a0Rest) = (found, sum, a0) at haux
            cases haux
            have hboundnext :
                ∀ c : T,
                  T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
                  T.add
                      (T.card_times m
                        (T.early_collapse (trans (new.T.P als aadd))))
                      sumRest <
                    T.card_times (m + 1) c := by
              intro c hcNF hcIdx hcne
              exact bridge_card_times_add_level_lt m (m + 1)
                (T.early_collapse (trans (new.T.P als aadd))) c sumRest
                (Nat.lt_succ_self m) hec.1 hec.2.1 hecne
                hcNF hcIdx hcne
            cases m with
            | zero =>
              have hsumZ : sumRest = T.Z := by
                have hlt := ihr.2.2.2.2.2.1 (T.P 0 T.Z T.Z)
                  (T.isNF1.p 0 T.Z T.Z T.isNF1.z T.isNF1.z
                    (fun y hy => by rw [T.G1.eq_1] at hy; cases hy)
                    (T.Z_le (T.P 0 T.Z T.Z)))
                  (T.index_Prop1.p 0 T.Z T.Z (Nat.le_refl 0) T.index_Prop1.z)
                  (by intro h; cases h)
                rw [T.card_times.eq_2] at hlt
                exact bridge_lt_P0ZZ_eq_Z sumRest hlt
              rw [hsumZ]
              have haddz :
                  T.card_times 0
                      (T.early_collapse (trans (new.T.P als aadd))) + T.Z =
                    T.early_collapse (trans (new.T.P als aadd)) := by
                rw [tc_card_times_zero]
                let A := T.early_collapse (trans (new.T.P als aadd))
                change A + T.Z = A
                exact (add_eq_hAdd A T.Z).symm.trans (T.add_Z A)
              rw [haddz]
              have hidx1 :
                  T.index_Prop1 1
                    (T.early_collapse (trans (new.T.P als aadd))) :=
                Rank1Termination.index_mono (Nat.zero_le 1)
                  (T.early_collapse (trans (new.T.P als aadd))) hec.2.1
              refine ⟨ihr.1, ihr.2.1, hec.1, hidx1, hec.2.2,
                ?_, ?_, ?_⟩
              · intro c hcNF hcIdx hcne
                have hb := hboundnext c hcNF hcIdx hcne
                rw [hsumZ] at hb
                have hleft :
                    T.add
                        (T.card_times 0
                          (T.early_collapse (trans (new.T.P als aadd)))) T.Z =
                      T.early_collapse (trans (new.T.P als aadd)) := by
                  rw [T.add_Z, tc_card_times_zero]
                rw [hleft] at hb
                exact hb
              · intro _
                exact hecne
              · intro h
                cases h
            | succ j =>
              have happ := bridge_card_times_succ_append j
                (T.early_collapse (trans (new.T.P als aadd))) sumRest
                hec.1 hec.2.1 ihr.2.2.1 ihr.2.2.2.1
                ihr.2.2.2.2.1
                ihr.2.2.2.2.2.1
              refine ⟨ihr.1, ihr.2.1, happ.1, happ.2.1, happ.2.2,
                ?_, ?_, ?_⟩
              · intro c hcNF hcIdx hcne
                exact hboundnext c hcNF hcIdx hcne
              · intro _
                have hheadne := bridge_card_times_ne_Z (j + 1)
                  (T.early_collapse (trans (new.T.P als aadd))) hecne
                intro hz
                exact (tc_add_ne_Z_left
                  (T.card_times (j + 1)
                    (T.early_collapse (trans (new.T.P als aadd))))
                  sumRest hheadne) hz
              · intro h
                cases h

-- From CardAlg.lean

theorem ca_card_times_add (n : Nat) (a b : T) :
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  cases n with
  | zero => rw [tc_card_times_zero, tc_card_times_zero, tc_card_times_zero]
  | succ k =>
      induction a with
      | Z => rfl
      | P p x y _ ihy =>
          rw [T.P_add_eq, T.card_times.eq_3, T.card_times.eq_3, ihy]
          by_cases hp : p = 0
          · rw [ite_eq_left hp]
            exact (Rank1Termination.add_assoc _ _ _).symm
          · rw [ite_eq_right hp]
            exact (Rank1Termination.add_assoc _ _ _).symm

theorem ca_mul_P1_ofNat_succ (k : Nat) :
    T.add (T.P 1 T.Z T.Z)
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) =
    T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
  rw [T.ofNat.eq_2, T.mul.eq_2]
  rw [← add_eq_hAdd]
  rw [T.P_add_eq, T.add]
  exact (mul_add_shape 1 T.Z k).symm

theorem ca_PZ_add (p : Nat) (a b : T) :
    T.P p a T.Z + b = T.P p a b := by
  change T.add (T.P p a T.Z) b = T.P p a b
  rw [T.P_add_eq, T.add]

theorem ca_mul_P1_one :
    T.mul (T.P 1 T.Z T.Z) (T.ofNat 1) = T.P 1 T.Z T.Z := by
  rfl

theorem ca_card_times_one_comp (m : Nat) (c : T) :
    T.card_times 1 (T.card_times m c) = T.card_times (m + 1) c := by
  induction c with
  | Z =>
    rw [T.card_times.eq_1, T.card_times.eq_1, T.card_times.eq_1]
  | P p a b iha ihb =>
    cases m with
    | zero =>
      rw [tc_card_times_zero]
    | succ k =>
      rw [T.card_times.eq_3]
      let H :=
        if p = 0 then
          T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat k) + T.early_collapse a) T.Z
        else
          T.P 1 (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) + a) T.Z
      change T.card_times 1 (T.add H (T.card_times (k + 1) b)) =
        T.card_times (k + 1 + 1) (T.P p a b)
      rw [ca_card_times_add, ihb]
      unfold H
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        rw [T.card_times.eq_3, ite_eq_right Nat.one_ne_zero]
        rw [T.card_times.eq_1, ca_PZ_add]
        rw [T.card_times.eq_3, ite_eq_left hp]
        rw [T.P_add_eq, T.add, ca_PZ_add]
        congr 1
        change
          T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)) =
            T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)))
              (T.early_collapse a)
        rw [ca_mul_P1_one]
        rw [← Rank1Termination.add_assoc]
        rw [ca_mul_P1_ofNat_succ]
      · rw [ite_eq_right hp]
        rw [T.card_times.eq_3, ite_eq_right Nat.one_ne_zero]
        rw [T.card_times.eq_1, ca_PZ_add]
        rw [T.card_times.eq_3, ite_eq_right hp]
        rw [T.P_add_eq, T.add, ca_PZ_add]
        congr 1
        change
          T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) =
            T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1 + 1))) a
        rw [ca_mul_P1_one]
        rw [← Rank1Termination.add_assoc]
        rw [ca_mul_P1_ofNat_succ]

-- From Weighted.lean

theorem wt_add_self_le (a z : T) : a ≤ T.add a z := by
  induction a with
  | Z =>
    rw [T.add]
    exact T.Z_le z
  | P p x y ihx ihy =>
    cases z with
    | Z =>
      rw [T.add_Z]
      exact Or.inr rfl
    | P q c d =>
      rw [T.P_add_eq]
      rcases ihy with hlt | heq
      · exact Or.inl (T.Lt.p_tail p x y (T.add y (T.P q c d)) hlt)
      · exact Or.inr (congrArg (fun t => T.P p x t) heq)

theorem wt_expand_card_succ_add (k : Nat) (a b y : T) :
    T.add (T.card_times (k + 1) (T.P 0 a b)) y =
      T.P 1
        (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a))
        (T.add (T.card_times (k + 1) b) y) := by
  rw [T.card_times.eq_3, ite_eq_left rfl]
  rw [← add_eq_hAdd]
  rw [Rank1Termination.add_assoc]
  rw [T.P_add_eq, T.add]
  rfl

theorem wt_card_append_lt (n : Nat) :
    ∀ c d y z : T,
      T.isNF1 c → T.index_Prop1 0 c →
      T.isNF1 d → T.index_Prop1 0 d →
      c < d →
      (∀ q : T, T.isNF1 q → T.index_Prop1 0 q → q ≠ T.Z →
        y < T.card_times n q) →
      T.add (T.card_times n c) y < T.add (T.card_times n d) z := by
  intro c
  induction c with
  | Z =>
    intro d y z _ _ hdNF hdIdx hcd hy
    have hdNe : d ≠ T.Z := by
      intro heq
      rw [heq] at hcd
      exact lt_Z_inv hcd
    have hyD : y < T.card_times n d := hy d hdNF hdIdx hdNe
    have hle : T.card_times n d ≤ T.add (T.card_times n d) z :=
      wt_add_self_le (T.card_times n d) z
    rw [T.card_times.eq_1, T.add]
    exact lt_of_lt_of_le_thm T y (T.card_times n d)
      (T.add (T.card_times n d) z) hyD hle
  | P p a b iha ihb =>
    intro d y z hcNF hcIdx hdNF hdIdx hcd hy
    cases hcIdx with
    | p _ _ _ hp hbIdx =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      cases hp0
      cases d with
      | Z => exact False.elim (lt_Z_inv hcd)
      | P q e f =>
        cases hdIdx with
        | p _ _ _ hq hfIdx =>
          have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
          cases hq0
          obtain ⟨haNF, hbNF, haG, _⟩ := T.isNF1_P_inv 0 a b hcNF
          obtain ⟨heNF, hfNF, heG, hheadf⟩ := T.isNF1_P_inv 0 e f hdNF
          rcases lt_inv 0 a b 0 e f hcd with hz | hor
          · exact False.elim (Nat.lt_irrefl 0 hz)
          · cases n with
            | zero =>
              rw [tc_card_times_zero, tc_card_times_zero]
              rw [T.P_add_eq, T.P_add_eq]
              rcases hor with hm | ht
              · exact T.Lt.p_mid 0 a e (T.add b y) (T.add f z) hm.2
              · have hae : a = e := ht.2.1
                cases hae
                have hbf : b < f := ht.2.2
                have hrec := ihb f y z hbNF hbIdx hfNF hfIdx hbf hy
                rw [tc_card_times_zero, tc_card_times_zero] at hrec
                exact T.Lt.p_tail 0 a (T.add b y) (T.add f z) hrec
            | succ k =>
              rw [wt_expand_card_succ_add k a b y]
              rw [wt_expand_card_succ_add k e f z]
              rcases hor with hm | ht
              · have hec : T.early_collapse a < T.early_collapse e :=
                  bridge_early_collapse_lt a e haNF haG heNF hm.2
                have hmid := bridge_add_left_lt
                  (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse a) (T.early_collapse e) hec
                exact T.Lt.p_mid 1 _ _ _ _ hmid
              · have hae : a = e := ht.2.1
                cases hae
                have hbf : b < f := ht.2.2
                have hrec := ihb f y z hbNF hbIdx hfNF hfIdx hbf hy
                exact T.Lt.p_tail 1
                  (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                    (T.early_collapse a)) _ _ hrec

-- From AuxOrder.lean

theorem ao_transAux_lex {lam : Nat} :
    ∀ {k : Nat} (v w : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x : new.T lam, x ∈ new.Vec.toList w →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x y : new.T lam,
        x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
        x < y → trans x < trans y) →
      new.compareVec v w = Ordering.lt →
      ∀ fv fw : Bool, ∀ sv av sw aw : T,
        transAux v = (fv, sv, av) →
        transAux w = (fw, sw, aw) →
        sv < sw ∨ (sv = sw ∧ av < aw) := by
  intro k
  induction k with
  | zero =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | @snoc nv xv a =>
        cases xv with
        | nil =>
          cases w with
          | @snoc nw xw b =>
            cases xw with
            | nil =>
              rw [new.compareVec.eq_2] at hcmp
              cases hca : new.compareT a b with
              | lt =>
                rw [transAux.eq_2] at hav
                rw [transAux.eq_2] at haw
                cases hav
                cases haw
                apply Or.inr
                constructor
                · rfl
                · apply hmono a b
                  · exact List.mem_singleton.mpr rfl
                  · exact List.mem_singleton.mpr rfl
                  · exact hca
              | eq =>
                rw [hca, new.compareVec.eq_1] at hcmp
                cases hcmp
              | gt =>
                rw [hca] at hcmp
                cases hcmp
  | succ m ih =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | @snoc nv xv a =>
        cases w with
        | @snoc nw xw b =>
          change
            (match new.compareT a b with
            | Ordering.eq => new.compareVec xv xw
            | ord => ord) = Ordering.lt at hcmp
          have hvrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xv →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hv x (List.mem_append_left [a] hx)
          have hwrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xw →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hw x (List.mem_append_left [b] hx)
          have ha := hv a
            (List.mem_append_right (new.Vec.toList xv) (List.mem_singleton.mpr rfl))
          have hb := hw b
            (List.mem_append_right (new.Vec.toList xw) (List.mem_singleton.mpr rfl))
          have hmonoRest :
              ∀ x y : new.T lam,
                x ∈ new.Vec.toList xv → y ∈ new.Vec.toList xw →
                x < y → trans x < trans y := by
            intro x y hx hy hxy
            exact hmono x y
              (List.mem_append_left [a] hx)
              (List.mem_append_left [b] hy) hxy
          cases havrest : transAux xv with
          | mk fvr pr =>
            obtain ⟨svr, avr⟩ := pr
            cases hawrest : transAux xw with
            | mk fwr qr =>
              obtain ⟨swr, awr⟩ := qr
              rw [transAux.eq_3, havrest] at hav
              rw [transAux.eq_3, hawrest] at haw
              cases hca : new.compareT a b with
              | lt =>
                rw [hca] at hcmp
                have hab : a < b := hca
                have htab : trans a < trans b := by
                  exact hmono a b
                    (List.mem_append_right (new.Vec.toList xv)
                      (List.mem_singleton.mpr rfl))
                    (List.mem_append_right (new.Vec.toList xw)
                      (List.mem_singleton.mpr rfl)) hab
                have hec : T.early_collapse (trans a) < T.early_collapse (trans b) :=
                  bridge_early_collapse_lt (trans a) (trans b)
                    ha.1 ha.2 hb.1 htab
                have heca := bridge_early_collapse_closed (trans a) ha.1 ha.2
                have hecb := bridge_early_collapse_closed (trans b) hb.1 hb.2
                have invr := tc_transAux_inv xv hvrest fvr svr avr havrest
                have hsum :
                    T.add (T.card_times m (T.early_collapse (trans a))) svr <
                      T.add (T.card_times m (T.early_collapse (trans b))) swr := by
                  apply wt_card_append_lt m
                    (T.early_collapse (trans a)) (T.early_collapse (trans b))
                    svr swr heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                  exact invr.2.2.2.2.2.1
                cases hav
                cases haw
                exact Or.inl hsum
              | gt =>
                rw [hca] at hcmp
                cases hcmp
              | eq =>
                rw [hca] at hcmp
                have habEq : a = b := new.T_eq_sound a b hca
                cases habEq
                have hrec := ih xv xw hvrest hwrest hmonoRest hcmp
                  fvr fwr svr avr swr awr havrest hawrest
                rcases hrec with hsumRest | heqrest
                · cases hav
                  cases haw
                  apply Or.inl
                  exact bridge_add_left_lt
                    (T.card_times m (T.early_collapse (trans a)))
                    svr swr hsumRest
                · cases hav
                  cases haw
                  apply Or.inr
                  constructor
                  · rw [heqrest.1]
                  · exact heqrest.2

-- From CardAux.lean

theorem sc_transAux_card1_inv {lam : Nat} :
    ∀ {k : Nat} (v : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      ∀ found : Bool, ∀ sum a0 : T,
        transAux v = (found, sum, a0) →
        T.isNF1 (T.card_times 1 sum) ∧
          T.index_Prop1 1 (T.card_times 1 sum) ∧
          (∀ y : T, y ∈ T.G1 1 (T.card_times 1 sum) →
            y < T.card_times 1 sum) ∧
          (∀ c : T,
            T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
              T.card_times 1 sum < T.card_times (k + 1) c) := by
  intro k
  induction k with
  | zero =>
      intro v hcomp found sum a0 haux
      cases v with
      | @snoc n xs a =>
        cases xs with
        | nil =>
          rw [transAux.eq_2] at haux
          cases haux
          change
            T.isNF1 T.Z ∧ T.index_Prop1 1 T.Z ∧
              (∀ y : T, y ∈ T.G1 1 T.Z → y < T.Z) ∧
              (∀ c : T,
                T.isNF1 c → T.index_Prop1 0 c → c ≠ T.Z →
                  T.Z < T.card_times 1 c)
          refine ⟨T.isNF1.z, T.index_Prop1.z, ?_, ?_⟩
          · intro y hy
            rw [T.G1.eq_1] at hy
            cases hy
          · intro c _ _ hcNe
            exact tc_Z_lt_of_ne (T.card_times 1 c)
              (bridge_card_times_ne_Z 1 c hcNe)
  | succ m ih =>
      intro v hcomp found sum a0 haux
      cases v with
      | @snoc n xs a =>
        have hrest :
            ∀ x : new.T lam, x ∈ new.Vec.toList xs →
              T.isNF1 (trans x) ∧
                (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
          intro x hx
          exact hcomp x (List.mem_append_left [a] hx)
        have ha :
            T.isNF1 (trans a) ∧
              (∀ y : T, y ∈ T.G1 0 (trans a) → y < trans a) := by
          apply hcomp a
          exact List.mem_append_right (new.Vec.toList xs)
            (List.mem_singleton.mpr rfl)
        cases hrestaux : transAux xs with
        | mk foundRest restpair =>
          obtain ⟨sumRest, a0Rest⟩ := restpair
          have ihr := ih xs hrest foundRest sumRest a0Rest hrestaux
          rw [transAux.eq_3, hrestaux] at haux
          cases a with
          | Z =>
            rw [_root_.trans.eq_1] at haux
            change (foundRest, sumRest, a0Rest) = (found, sum, a0) at haux
            cases haux
            refine ⟨ihr.1, ihr.2.1, ihr.2.2.1, ?_⟩
            intro c hcNF hcIdx hcNe
            have hold := ihr.2.2.2 c hcNF hcIdx hcNe
            have hnext := bridge_card_times_level_lt (m + 1) (m + 2) c c
              (Nat.lt_succ_self (m + 1)) hcNF hcIdx hcNe hcNF hcIdx hcNe
            exact lt_trans_thm _ _ _ hold hnext
          | P als aadd =>
            have hane : (new.T.P als aadd : new.T lam) ≠ new.T.Z := by
              intro h
              cases h
            have hatNe := tc_trans_ne_Z_of_ne_Z (new.T.P als aadd) hane
            have hec := bridge_early_collapse_closed
              (trans (new.T.P als aadd)) ha.1 ha.2
            have hecNe := bridge_early_collapse_ne_Z
              (trans (new.T.P als aadd)) hatNe
            change
              (true,
                T.card_times m (T.early_collapse (trans (new.T.P als aadd))) + sumRest,
                a0Rest) = (found, sum, a0) at haux
            cases haux
            rw [← add_eq_hAdd]
            rw [ca_card_times_add, ca_card_times_one_comp]
            have happ := bridge_card_times_succ_append m
              (T.early_collapse (trans (new.T.P als aadd)))
              (T.card_times 1 sumRest)
              hec.1 hec.2.1 ihr.1 ihr.2.1 ihr.2.2.1 ihr.2.2.2
            refine ⟨happ.1, happ.2.1, happ.2.2, ?_⟩
            intro c hcNF hcIdx hcNe
            exact bridge_card_times_add_level_lt (m + 1) (m + 2)
              (T.early_collapse (trans (new.T.P als aadd))) c
              (T.card_times 1 sumRest)
              (Nat.lt_succ_self (m + 1)) hec.1 hec.2.1 hecNe
              hcNF hcIdx hcNe

-- From CardOrder_fixed.lean

theorem co_len1_sum_zero {lam : Nat}
    (v : new.Vec (new.T lam) 1) (f : Bool) (s a0 : T)
    (h : transAux v = (f, s, a0)) : s = T.Z := by
  cases v with
  | @snoc n xs a =>
    cases xs with
    | nil =>
      rw [transAux.eq_2] at h
      cases h
      rfl

theorem co_transAux_card1_lex {lam : Nat} :
    ∀ {k : Nat} (v w : new.Vec (new.T lam) (k + 1)),
      (∀ x : new.T lam, x ∈ new.Vec.toList v →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x : new.T lam, x ∈ new.Vec.toList w →
        T.isNF1 (trans x) ∧
          (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x)) →
      (∀ x y : new.T lam,
        x ∈ new.Vec.toList v → y ∈ new.Vec.toList w →
        x < y → trans x < trans y) →
      new.compareVec v w = Ordering.lt →
      ∀ fv fw : Bool, ∀ sv av sw aw : T,
        transAux v = (fv, sv, av) →
        transAux w = (fw, sw, aw) →
        T.card_times 1 sv < T.card_times 1 sw ∨
          (T.card_times 1 sv = T.card_times 1 sw ∧ av < aw) := by
  intro k
  induction k with
  | zero =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      have hlex := ao_transAux_lex v w hv hw hmono hcmp
        fv fw sv av sw aw hav haw
      have hsv : sv = T.Z := co_len1_sum_zero v fv sv av hav
      have hsw : sw = T.Z := co_len1_sum_zero w fw sw aw haw
      rcases hlex with hslt | heq
      · rw [hsv, hsw] at hslt
        exact False.elim (lt_irrefl_thm T.Z hslt)
      · apply Or.inr
        constructor
        · rw [hsv, hsw]
        · exact heq.2
  | succ m ih =>
      intro v w hv hw hmono hcmp fv fw sv av sw aw hav haw
      cases v with
      | @snoc nv xv a =>
        cases w with
        | @snoc nw xw b =>
          change
            (match new.compareT a b with
            | Ordering.eq => new.compareVec xv xw
            | ord => ord) = Ordering.lt at hcmp
          have hvrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xv →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hv x (List.mem_append_left [a] hx)
          have hwrest :
              ∀ x : new.T lam, x ∈ new.Vec.toList xw →
                T.isNF1 (trans x) ∧
                  (∀ y : T, y ∈ T.G1 0 (trans x) → y < trans x) := by
            intro x hx
            exact hw x (List.mem_append_left [b] hx)
          have ha := hv a
            (List.mem_append_right (new.Vec.toList xv) (List.mem_singleton.mpr rfl))
          have hb := hw b
            (List.mem_append_right (new.Vec.toList xw) (List.mem_singleton.mpr rfl))
          have hmonoRest :
              ∀ x y : new.T lam,
                x ∈ new.Vec.toList xv → y ∈ new.Vec.toList xw →
                x < y → trans x < trans y := by
            intro x y hx hy hxy
            exact hmono x y
              (List.mem_append_left [a] hx)
              (List.mem_append_left [b] hy) hxy
          cases havrest : transAux xv with
          | mk fvr pr =>
            obtain ⟨svr, avr⟩ := pr
            cases hawrest : transAux xw with
            | mk fwr qr =>
              obtain ⟨swr, awr⟩ := qr
              rw [transAux.eq_3, havrest] at hav
              rw [transAux.eq_3, hawrest] at haw
              cases hca : new.compareT a b with
              | lt =>
                rw [hca] at hcmp
                have htab : trans a < trans b := by
                  exact hmono a b
                    (List.mem_append_right (new.Vec.toList xv)
                      (List.mem_singleton.mpr rfl))
                    (List.mem_append_right (new.Vec.toList xw)
                      (List.mem_singleton.mpr rfl)) hca
                have hec : T.early_collapse (trans a) < T.early_collapse (trans b) :=
                  bridge_early_collapse_lt (trans a) (trans b)
                    ha.1 ha.2 hb.1 htab
                have heca := bridge_early_collapse_closed (trans a) ha.1 ha.2
                have hecb := bridge_early_collapse_closed (trans b) hb.1 hb.2
                have invr := sc_transAux_card1_inv xv hvrest fvr svr avr havrest
                cases hav
                cases haw
                cases m with
                | zero =>
                  have hsv : svr = T.Z := co_len1_sum_zero xv fvr svr av havrest
                  have hsw : swr = T.Z := co_len1_sum_zero xw fwr swr aw hawrest
                  rw [hsv, hsw]
                  rw [← add_eq_hAdd, T.add_Z, tc_card_times_zero]
                  rw [← add_eq_hAdd, T.add_Z, tc_card_times_zero]
                  apply Or.inl
                  exact bridge_card_times_lt_same 1
                    (T.early_collapse (trans a)) (T.early_collapse (trans b))
                    heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                | succ j =>
                  rw [← add_eq_hAdd]
                  rw [← add_eq_hAdd]
                  rw [ca_card_times_add, ca_card_times_one_comp]
                  rw [ca_card_times_add, ca_card_times_one_comp]
                  apply Or.inl
                  apply wt_card_append_lt (j + 2)
                    (T.early_collapse (trans a)) (T.early_collapse (trans b))
                    (T.card_times 1 svr) (T.card_times 1 swr)
                    heca.1 heca.2.1 hecb.1 hecb.2.1 hec
                  exact invr.2.2.2
              | gt =>
                rw [hca] at hcmp
                cases hcmp
              | eq =>
                rw [hca] at hcmp
                have habEq : a = b := new.T_eq_sound a b hca
                cases habEq
                have hrec := ih xv xw hvrest hwrest hmonoRest hcmp
                  fvr fwr svr avr swr awr havrest hawrest
                cases hav
                cases haw
                cases a with
                | Z =>
                  change
                    T.card_times 1 svr < T.card_times 1 swr ∨
                      (T.card_times 1 svr = T.card_times 1 swr ∧ av < aw)
                  exact hrec
                | P als aadd =>
                  cases m with
                  | zero =>
                    have hsv : svr = T.Z := co_len1_sum_zero xv fvr svr av havrest
                    have hsw : swr = T.Z := co_len1_sum_zero xw fwr swr aw hawrest
                    rcases hrec with hbad | hr
                    · rw [hsv, hsw] at hbad
                      exact False.elim (lt_irrefl_thm T.Z hbad)
                    · apply Or.inr
                      constructor
                      · rw [hsv, hsw]
                      · exact hr.2
                  | succ j =>
                    rw [← add_eq_hAdd]
                    rw [← add_eq_hAdd]
                    rw [ca_card_times_add, ca_card_times_one_comp]
                    rw [ca_card_times_add, ca_card_times_one_comp]
                    rcases hrec with hr | hr
                    · apply Or.inl
                      exact bridge_add_left_lt
                        (T.card_times (j + 2)
                          (T.early_collapse (trans (new.T.P als aadd))))
                        (T.card_times 1 svr) (T.card_times 1 swr) hr
                    · apply Or.inr
                      constructor
                      · rw [hr.1]
                      · exact hr.2

theorem ec_part_snd_index0 (s : T) (hs : T.isNF1 s) :
    T.index_Prop1 0 (T.part s).2 := by
  cases hp : T.part s with
  | mk a b =>
    change T.index_Prop1 0 b
    exact bridge_part_second_index0 s a b hs hp

theorem ec_index0_lt_posfixed (b c : T)
    (hb : T.index_Prop1 0 b)
    (hc : T.part c = (c, T.Z))
    (hcne : c ≠ T.Z) :
    b < c := by
  cases b with
  | Z =>
      cases c with
      | Z => exact False.elim (hcne rfl)
      | P q u v => exact T.Lt.Z_lt_P q u v
  | P p a d =>
      cases hb with
      | p _ _ _ hp htail =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        cases hp0
        cases c with
        | Z => exact False.elim (hcne rfl)
        | P q u v =>
          have hqne : q ≠ 0 := by
            intro hq
            rw [T.part, ite_eq_left hq] at hc
            cases hc
          have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
          exact T.Lt.p_head 0 q a u d v hqpos

theorem ec_add_index0_lt_pos_of_lt : ∀ a c b : T,
    T.part a = (a, T.Z) →
    T.part c = (c, T.Z) →
    T.index_Prop1 0 b →
    a < c →
    T.add a b < c := by
  intro a
  induction a with
  | Z =>
    intro c b _ hc hb hlt
    rw [T.add]
    exact ec_index0_lt_posfixed b c hb hc (fun h => by rw [h] at hlt; cases hlt)
  | P p x y _ ihy =>
    intro c b ha hc hb hlt
    have hpne : p ≠ 0 := by
      intro hp
      rw [T.part, ite_eq_left hp] at ha
      cases ha
    have hyfixed : T.part y = (y, T.Z) := by
      rw [T.part, ite_eq_right hpne] at ha
      cases hpy : T.part y with
      | mk r s =>
        rw [hpy] at ha
        cases ha
        rfl
    cases c with
    | Z => cases hlt
    | P q u v =>
      rw [T.P_add_eq]
      have hcinv : q ≠ 0 := by
        intro hq
        rw [T.part, ite_eq_left hq] at hc
        cases hc
      have hvfixed : T.part v = (v, T.Z) := by
        rw [T.part, ite_eq_right hcinv] at hc
        cases hpv : T.part v with
        | mk r s =>
          rw [hpv] at hc
          cases hc
          rfl
      rcases lt_inv p x y q u v hlt with hpq | (hm | ht)
      · exact T.Lt.p_head p q x u (T.add y b) v hpq
      · cases hm.1
        exact T.Lt.p_mid p x u (T.add y b) v hm.2
      · cases ht.1
        cases ht.2.1
        have htail : T.add y b < v :=
          ihy v b hyfixed hvfixed hb ht.2.2
        exact T.Lt.p_tail p x (T.add y b) v htail

theorem ec_pair_formula (s a b : T)
    (hs : T.isNF1 s) (hp : T.part s = (a, b)) :
    T.early_collapse s =
      if a = T.Z then s
      else if T.head b ≤ T.P 0 a T.Z then T.P 0 a b else b := by
  rw [T.early_collapse, hp]
  by_cases ha : a = T.Z
  · rw [ite_eq_left ha, ite_eq_left ha]
  · rw [ite_eq_right ha, ite_eq_right ha]
    have hbnf : T.isNF1 b := by
      have hparts := bridge_part_NF1 s hs
      rw [hp] at hparts
      exact hparts.2
    rw [T.stand, bridge_stand_eq_self_of_NF1 b hbnf]

theorem ec_part_snd_middle_mem (s a e f : T)
    (hp : T.part s = (a, T.P 0 e f)) :
    e ∈ T.G1 0 s := by
  have hadd := bridge_part_add s
  rw [hp] at hadd
  have he : e ∈ T.G1 0 (T.P 0 e f) := by
    rw [T.G1.eq_2, ite_eq_left (Nat.le_refl 0)]
    exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_singleton_self e))
  rw [← hadd, bridge_G1_add_eq]
  exact List.mem_append_right _ he

theorem ec_index0_lt_P0 (b c : T)
    (hb : T.index_Prop1 0 b)
    (hmid : ∀ e f : T, b = T.P 0 e f → e < c) :
    b < T.P 0 c T.Z := by
  cases b with
  | Z => exact T.Lt.Z_lt_P 0 c T.Z
  | P p e f =>
      cases hb with
      | p _ _ _ hp _ =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        cases hp0
        exact T.Lt.p_mid 0 e c f T.Z (hmid e f rfl)

theorem ec_one_del_NF_index_good1 (s : T)
    (hs : T.isNF1 s)
    (hi : T.index_Prop1 0 s)
    (_hg : ∀ x : T, x ∈ T.G1 1 s → x < s) :
    T.isNF1 (T.one_del s) ∧
      T.index_Prop1 0 (T.one_del s) ∧
      (∀ x : T, x ∈ T.G1 1 (T.one_del s) → x < T.one_del s) := by
  cases s with
  | Z =>
      change T.isNF1 T.Z ∧ T.index_Prop1 0 T.Z ∧
        (∀ x : T, x ∈ T.G1 1 T.Z → x < T.Z)
      constructor
      · exact T.isNF1.z
      · constructor
        · exact T.index_Prop1.z
        · intro x hx
          rw [T.G1.eq_1] at hx
          cases hx
  | P p a b =>
      cases hi with
      | p _ _ _ hp hib =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        cases hp0
        cases a with
        | Z =>
            change T.isNF1 b ∧ T.index_Prop1 0 b ∧
              (∀ x : T, x ∈ T.G1 1 b → x < b)
            have hbNF := (T.isNF1_P_inv 0 T.Z b hs).2.1
            constructor
            · exact hbNF
            · constructor
              · exact hib
              · intro x hx
                have hempty := index_Prop1_G1_empty 0 b hib 1
                  (Nat.zero_lt_succ 0)
                rw [hempty] at hx
                cases hx
        | P q c d =>
            change T.isNF1 (T.P 0 (T.P q c d) b) ∧
              T.index_Prop1 0 (T.P 0 (T.P q c d) b) ∧
              (∀ x : T, x ∈ T.G1 1 (T.P 0 (T.P q c d) b) →
                x < T.P 0 (T.P q c d) b)
            exact ⟨hs, T.index_Prop1.p 0 (T.P q c d) b
              (Nat.le_refl 0) hib, _hg⟩

end TranslationAlgebra
