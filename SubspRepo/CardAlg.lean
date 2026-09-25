import Bridge
open T

theorem ca_card_times_zero (c : T) : T.card_times 0 c = c := by
  cases c with
  | Z => rfl
  | P p a b => rfl

theorem ca_card_times_add (n : Nat) (a b : T) :
    T.card_times n (T.add a b) =
      T.add (T.card_times n a) (T.card_times n b) := by
  induction a with
  | Z =>
    rw [T.add, T.card_times.eq_1, T.add]
  | P p x y ihx ihy =>
    cases b with
    | Z =>
      rw [T.add_Z, T.card_times.eq_1, T.add_Z]
    | P q c d =>
      rw [T.P_add_eq]
      cases n with
      | zero =>
        rw [ca_card_times_zero, ca_card_times_zero, ca_card_times_zero]
        rw [T.P_add_eq]
      | succ k =>
        rw [T.card_times.eq_3, T.card_times.eq_3, T.card_times.eq_3]
        rw [ihy]
        by_cases hp : p = 0
        · rw [← add_eq_hAdd]
          exact (Rank1Termination.add_assoc _ _ _).symm
        · rw [← add_eq_hAdd]
          exact (Rank1Termination.add_assoc _ _ _).symm

#print axioms ca_card_times_add

theorem ca_mul_P1_ofNat_succ (k : Nat) :
    T.add (T.P 1 T.Z T.Z)
      (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) =
    T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1)) := by
  rw [T.ofNat.eq_2, T.mul.eq_2]
  rw [← add_eq_hAdd]
  rw [T.P_add_eq, T.add]
  exact (mul_add_shape 1 T.Z k).symm

#print axioms ca_mul_P1_ofNat_succ


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
      rw [ca_card_times_zero]
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
        rw [T.card_times.eq_3, ite_eq_right (by decide : (1:Nat) ≠ 0)]
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
        rw [T.card_times.eq_3, ite_eq_right (by decide : (1:Nat) ≠ 0)]
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

#print axioms ca_card_times_one_comp
