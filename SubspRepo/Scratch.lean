import Subsp.new.trans
open T

theorem ct_head (n : Nat) (s : T) :
    T.head (T.card_times n s) = T.card_times n (T.head s) := by
  cases s with
  | Z => rfl
  | P p a b =>
    cases n with
    | zero => rfl
    | succ k =>
      change
        T.head
          (T.add
            (if p = 0 then
              T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)) T.Z
            else
              T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) T.Z)
            (T.card_times (k + 1) b)) =
        T.add
          (if p = 0 then
            T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)) T.Z
          else
            T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k + 1))) a) T.Z)
          (T.card_times (k + 1) T.Z)
      by_cases hp : p = 0
      · rw [ite_eq_left hp, T.card_times.eq_1, T.add_Z, T.P_add_eq]
        rfl
      · rw [ite_eq_right hp, T.card_times.eq_1, T.add_Z, T.P_add_eq]
        rfl
