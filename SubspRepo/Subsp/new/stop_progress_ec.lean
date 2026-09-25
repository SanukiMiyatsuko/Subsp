import Subsp.new.stop_progress

open T

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

