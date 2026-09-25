import Subsp.new.stop_order_aux
open T

theorem c1_p0 (a b : T) :
    T.card_times 1 (T.P 0 a b) =
      T.P 1 (T.early_collapse a) (T.card_times 1 b) := by
  rw [T.card_times.eq_3, ite_eq_left rfl]
  rw [T.ofNat.eq_1, T.mul.eq_1]
  change T.add (T.P 1 (T.add T.Z (T.early_collapse a)) T.Z)
    (T.card_times 1 b) = T.P 1 (T.early_collapse a) (T.card_times 1 b)
  rw [T.add.eq_1, T.P_add_eq, T.add.eq_1]

theorem c1_p1 (a b : T) :
    T.card_times 1 (T.P 1 a b) =
      T.P 1 (T.P 1 T.Z a) (T.card_times 1 b) := by
  rw [T.card_times.eq_3, ite_eq_right (Nat.one_ne_zero)]
  rw [mul_succ_shape 1 T.Z 0]
  rw [T.ofNat.eq_1, T.mul.eq_1]
  change T.add (T.P 1 (T.add (T.P 1 T.Z T.Z) a) T.Z)
    (T.card_times 1 b) = T.P 1 (T.P 1 T.Z a) (T.card_times 1 b)
  rw [T.P_add_eq, T.add.eq_1]
  rw [T.P_add_eq, T.add.eq_1]
