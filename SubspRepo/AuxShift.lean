import Bridge
import AuxBridge

open T

theorem ash_one_del_NF_index0 (s : T)
    (hs : T.isNF1 s) (hi : T.index_Prop1 0 s) :
    T.isNF1 (T.one_del s) ∧ T.index_Prop1 0 (T.one_del s) := by
  cases s with
  | Z =>
      rw [T.one_del]
      exact ⟨T.isNF1.z, T.index_Prop1.z⟩
  | P p a b =>
      cases hi with
      | p _ _ _ hp hbidx =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        by_cases ha : a = T.Z
        · subst a
          rw [T.one_del]
          have hbNF := (T.isNF1_P_inv 0 T.Z b hs).2.1
          exact ⟨hbNF, hbidx⟩
        · change T.one_del (T.P 0 a b) = T.P 0 a b
          rfl
          
theorem ash_one_del_ne_Z_of_shape (s : T)
    (hs : T.index_Prop1 0 s) (hne : s ≠ T.Z)
    (hnotone : s ≠ T.P 0 T.Z T.Z) :
    T.one_del s ≠ T.Z := by
  cases s with
  | Z => exact False.elim (hne rfl)
  | P p a b =>
      cases hs with
      | p _ _ _ hp hbidx =>
        have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
        subst p
        by_cases ha : a = T.Z
        · subst a
          rw [T.one_del]
          intro hb
          apply hnotone
          rw [hb]
        · change T.one_del (T.P 0 a b) = T.P 0 a b
          intro h
          cases h

theorem ash_one_del_lt_index0 (a b : T)
    (haNF : T.isNF1 a) (haIdx : T.index_Prop1 0 a) (haNe : a ≠ T.Z)
    (hbNF : T.isNF1 b) (hbIdx : T.index_Prop1 0 b) (hbNe : b ≠ T.Z)
    (hab : a < b) :
    T.one_del a < T.one_del b := by
  cases a with
  | Z => exact False.elim (haNe rfl)
  | P pa aa ab =>
    cases haIdx with
    | p _ _ _ hpa habIdx =>
      have hpa0 : pa = 0 := Nat.eq_zero_of_le_zero hpa
      subst pa
      cases b with
      | Z => exact False.elim (hbNe rfl)
      | P pb ba bb =>
        cases hbIdx with
        | p _ _ _ hpb hbbIdx =>
          have hpb0 : pb = 0 := Nat.eq_zero_of_le_zero hpb
          subst pb
          cases lt_inv 0 aa ab 0 ba bb hab with
          | inl hzero => exact False.elim (Nat.lt_irrefl 0 hzero)
          | inr hor =>
            cases hor with
            | inl hmid =>
              have haa : aa < ba := hmid.2
              by_cases haaZ : aa = T.Z
              · subst aa
                rw [T.one_del]
                cases ab with
                | Z =>
                  by_cases hbaZ : ba = T.Z
                  · subst ba
                    exact False.elim (lt_Z_inv haa)
                  · change T.Z < T.one_del (T.P 0 ba bb)
                    have hresNe : T.one_del (T.P 0 ba bb) ≠ T.Z := by
                      change T.P 0 ba bb ≠ T.Z
                      intro h
                      cases h
                    exact tc_Z_lt_of_ne (T.one_del (T.P 0 ba bb)) hresNe
                | P q c d =>
                  by_cases hbaZ : ba = T.Z
                  · subst ba
                    exact False.elim (lt_Z_inv haa)
                  · rw [T.one_del]
                    change T.P q c d < T.P 0 ba bb
                    exact T.Lt.p_mid 0 T.Z ba (T.P q c d) bb haa
              · by_cases hbaZ : ba = T.Z
                · subst ba
                  exact False.elim (lt_Z_inv haa)
                · change T.P 0 aa ab < T.P 0 ba bb
                  exact T.Lt.p_mid 0 aa ba ab bb haa
            | inr htail =>
              cases htail.1
              cases htail.2.1
              have hablt : ab < bb := htail.2.2
              by_cases haaZ : aa = T.Z
              · subst aa
                rw [T.one_del, T.one_del]
                exact hablt
              · change T.P 0 aa ab < T.P 0 aa bb
                exact T.Lt.p_tail 0 aa ab bb hablt

#print axioms ash_one_del_NF_index0
#print axioms ash_one_del_lt_index0

theorem ash_card_times_add (n : Nat) : ∀ a b : T,
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  intro a
  induction a with
  | Z =>
      intro b
      rw [T.add, T.card_times]
      cases n with
      | zero => rw [T.card_times, T.add]
      | succ k => rw [T.card_times, T.add]
  | P p x y ihx ihy =>
      intro b
      rw [T.P_add_eq]
      cases n with
      | zero =>
        rw [T.card_times, T.card_times]
        rw [T.P_add_eq]
      | succ k =>
        rw [T.card_times, T.card_times]
        by_cases hp : p = 0
        · rw [ite_eq_left hp, ite_eq_left hp]
          rw [ihy]
          rw [T.add_assoc]
        · rw [ite_eq_right hp, ite_eq_right hp]
          rw [ihy]
          rw [T.add_assoc]

#print axioms ash_card_times_add

theorem ash_card_times_one_comp (n : Nat) : ∀ c : T,
    T.card_times 1 (T.card_times (n + 1) c) =
      T.card_times (n + 2) c := by
  intro c
  induction c with
  | Z =>
      rw [T.card_times, T.card_times, T.card_times]
  | P p a b iha ihb =>
      rw [T.card_times]
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        rw [ash_card_times_add]
        rw [T.card_times]
        rw [ite_eq_right (by intro h; cases h : (1:Nat) = 0)]
        rw [T.card_times]
        rw [ite_eq_left hp]
        rw [ihb]
        change
          T.add
            (T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n)) (T.early_collapse a)))
              T.Z)
            (T.card_times (n + 2) b) =
          T.add
            (T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1)))
                (T.early_collapse a)) T.Z)
            (T.card_times (n + 2) b)
        congr 2
        -- both prefixes are n+1 copies of P 1 Z Z
        induction n with
        | zero => rfl
        | succ n ihn =>
          rw [mul_succ_shape 1 T.Z n, mul_succ_shape 1 T.Z (n + 1)]
          rw [T.P_add_eq]
          rw [← ihn]
      · rw [ite_eq_right hp]
        rw [ash_card_times_add]
        rw [T.card_times]
        rw [ite_eq_right (by intro h; cases h : (1:Nat) = 0)]
        rw [T.card_times]
        rw [ite_eq_right hp]
        rw [ihb]
        change
          T.add
            (T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat 1))
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 1))) a)) T.Z)
            (T.card_times (n + 2) b) =
          T.add
            (T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (n + 2))) a) T.Z)
            (T.card_times (n + 2) b)
        congr 2
        induction n with
        | zero => rfl
        | succ n ihn =>
          rw [mul_succ_shape 1 T.Z (n + 1), mul_succ_shape 1 T.Z (n + 2)]
          rw [T.P_add_eq]
          rw [← ihn]

#print axioms ash_card_times_one_comp
