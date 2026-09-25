import AuxBridge

open T

theorem ca_card_times_add (n : Nat) : ∀ a b : T,
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  intro a
  induction a with
  | Z =>
    intro b
    rw [T.add.eq_1, T.card_times.eq_1, T.add.eq_1]
  | P p c d ihc ihd =>
    intro b
    rw [T.P_add_eq]
    cases n with
    | zero =>
      rw [T.card_times.eq_2, T.card_times.eq_2]
      rw [aux_card_times_zero]
      rw [T.P_add_eq]
    | succ k =>
      rw [T.card_times.eq_def, T.card_times.eq_def]
      change
        T.add
          (if p = 0 then
            T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                (T.early_collapse c)) T.Z
          else
            T.P 1
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) c) T.Z)
          (T.card_times (k + 1) (T.add d b)) =
        T.add
          (T.add
            (if p = 0 then
              T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                  (T.early_collapse c)) T.Z
            else
              T.P 1
                (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) c) T.Z)
            (T.card_times (k + 1) d))
          (T.card_times (k + 1) b)
      rw [ihd b]
      exact (Rank1Termination.add_assoc
        (if p = 0 then
          T.P 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
              (T.early_collapse c)) T.Z
        else
          T.P 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) c) T.Z)
        (T.card_times (k + 1) d) (T.card_times (k + 1) b)).symm

#print axioms ca_card_times_add

theorem ca_card_times_one_comp {c : T}
    (hc : T.index_Prop1 0 c) : ∀ m : Nat,
    T.card_times 1 (T.card_times m c) = T.card_times (m + 1) c := by
  intro m
  induction c generalizing m with
  | Z =>
    rw [T.card_times.eq_1, T.card_times.eq_1, T.card_times.eq_1]
  | P p a b iha ihb =>
    cases hc with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      cases m with
      | zero =>
        rw [T.card_times.eq_2]
      | succ k =>
        rw [T.card_times.eq_3, ite_eq_left rfl]
        rw [← add_eq_hAdd
              (T.P 1
                ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a)
                T.Z)
              (T.card_times (k + 1) b),
            T.P_add_eq, T.add.eq_1]
        rw [T.card_times.eq_3, ite_eq_right (by
          intro h
          cases h)]
        rw [← add_eq_hAdd
              (T.P 1
                ((T.P 1 T.Z T.Z).mul (T.ofNat 1) +
                  ((T.P 1 T.Z T.Z).mul (T.ofNat k) + T.early_collapse a))
                T.Z)
              (T.card_times 1 (T.card_times (k + 1) b)),
            T.P_add_eq, T.add.eq_1]
        rw [T.card_times.eq_3, ite_eq_left rfl]
        rw [← add_eq_hAdd
              (T.P 1
                ((T.P 1 T.Z T.Z).mul (T.ofNat (k + 1)) +
                  T.early_collapse a)
                T.Z)
              (T.card_times (k + 2) b),
            T.P_add_eq, T.add.eq_1]
        have htail := ihb hb (k + 1)
        rw [htail]
        rw [mul_succ_shape 1 T.Z 0, T.ofNat.eq_1, T.mul.eq_1]
        rw [mul_succ_shape 1 T.Z k]
        have hmid :
            T.add (T.P 1 T.Z T.Z)
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                (T.early_collapse a)) =
            T.add
              (T.P 1 T.Z (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)))
              (T.early_collapse a) := by
          rw [T.P_add_eq, T.add.eq_1, T.P_add_eq]
        change
          T.P 1
            (T.add (T.P 1 T.Z T.Z)
              (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k))
                (T.early_collapse a)))
            (T.card_times (k + 2) b) =
          T.P 1
            (T.add
              (T.P 1 T.Z (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)))
              (T.early_collapse a))
            (T.card_times (k + 2) b)
        rw [hmid]

#print axioms ca_card_times_one_comp

theorem ca_one_del_index0 (c : T)
    (hcNF : T.isNF1 c) (hcIdx : T.index_Prop1 0 c) :
    T.isNF1 (T.one_del c) ∧ T.index_Prop1 0 (T.one_del c) := by
  cases c with
  | Z =>
    change T.isNF1 T.Z ∧ T.index_Prop1 0 T.Z
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
        change
          T.isNF1 (T.P 0 (T.P q d e) b) ∧
            T.index_Prop1 0 (T.P 0 (T.P q d e) b)
        exact ⟨hcNF,
          T.index_Prop1.p 0 (T.P q d e) b (Nat.le_refl 0) hbIdx⟩

#print axioms ca_one_del_index0

theorem ca_card_times_pos_shape (n : Nat) (c : T)
    (hcIdx : T.index_Prop1 0 c) (hcNe : c ≠ T.Z) :
    ∃ mid tail : T, T.card_times (n + 1) c = T.P 1 mid tail := by
  cases c with
  | Z => exact False.elim (hcNe rfl)
  | P p a b =>
    cases hcIdx with
    | p _ _ _ hp hb =>
      have hp0 : p = 0 := Nat.eq_zero_of_le_zero hp
      subst p
      rw [T.card_times.eq_3, ite_eq_left rfl]
      refine ⟨T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
          (T.early_collapse a), T.card_times (n + 1) b, ?_⟩
      change
        T.add
          (T.P 1
            (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
              (T.early_collapse a)) T.Z)
          (T.card_times (n + 1) b) =
        T.P 1
          (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat n))
            (T.early_collapse a))
          (T.card_times (n + 1) b)
      rw [T.P_add_eq, T.add.eq_1]

#print axioms ca_card_times_pos_shape
