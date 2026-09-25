import CardAlg
import AuxCore

open T

theorem sa_one_del_index0 (c : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) :
    T.isNF1 (T.one_del c) ∧ T.index_Prop1 0 (T.one_del c) := by
  cases c with
  | Z =>
    exact ⟨T.isNF1.z, T.index_Prop1.z⟩
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp hbIdx =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      obtain ⟨haNF, hbNF, haG, hhead⟩ := T.isNF1_P_inv 0 a b hcNF
      cases a with
      | Z =>
        change T.isNF1 b ∧ T.index_Prop1 0 b
        exact ⟨hbNF, hbIdx⟩
      | P q d e =>
        change T.isNF1 (T.P 0 (T.P q d e) b) ∧
          T.index_Prop1 0 (T.P 0 (T.P q d e) b)
        exact ⟨hcNF, T.index_Prop1.p 0 (T.P q d e) b (Nat.le_refl 0) hbIdx⟩

#print axioms sa_one_del_index0

theorem sa_shift_base_closed (c : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) :
    T.isNF1 (T.card_times 1 (T.one_del c)) ∧
      T.index_Prop1 1 (T.card_times 1 (T.one_del c)) ∧
      (∀ x : T, x ∈ T.G1 1 (T.card_times 1 (T.one_del c)) →
        x < T.card_times 1 (T.one_del c)) := by
  have hd := sa_one_del_index0 c hcNF hcIdx
  exact bridge_card_times_closed 1 (T.one_del c) hd.1 hd.2

#print axioms sa_shift_base_closed

theorem sa_shift_base_bound (c z : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c)
    (hzNF : T.isNF1 z) (hzIdx : T.index_Prop1 0 z) (hzNe : z ≠ T.Z) :
    T.card_times 1 (T.one_del c) < T.card_times 2 z := by
  have hd := sa_one_del_index0 c hcNF hcIdx
  by_cases hdZ : T.one_del c = T.Z
  · rw [hdZ, T.card_times.eq_1]
    exact tc_Z_lt_of_ne (T.card_times 2 z)
      (bridge_card_times_ne_Z 2 z hzNe)
  · exact bridge_card_times_level_lt 1 2 (T.one_del c) z
      (Nat.lt_succ_self 1) hd.1 hd.2 hdZ hzNF hzIdx hzNe

#print axioms sa_shift_base_bound

theorem sa_one_del_card_succ_add (k : Nat) (c y : T)
    (hcIdx : T.index_Prop1 0 c) (hcNe : c ≠ T.Z) :
    T.one_del (T.add (T.card_times (k + 1) c) y) =
      T.add (T.card_times (k + 1) c) y := by
  cases c with
  | Z => exact False.elim (hcNe rfl)
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp hbIdx =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      rw [T.card_times.eq_3, ite_eq_left rfl]
      rw [← add_eq_hAdd]
      rw [Rank1Termination.add_assoc]
      rw [T.P_add_eq, T.add]
      rfl

#print axioms sa_one_del_card_succ_add

