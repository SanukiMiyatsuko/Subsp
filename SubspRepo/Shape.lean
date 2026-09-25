import Bridge
open T

theorem shape (k:Nat) (a b:T) :
  T.card_times (k+1) (T.P 0 a b) =
    T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a))
      (T.card_times (k+1) b) := by
  rw [T.card_times.eq_def]
  change
    T.add
      (if 0 = 0 then
        T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat k)) (T.early_collapse a)) T.Z
      else
        T.P 1 (T.add (T.mul (T.P 1 T.Z T.Z) (T.ofNat (k+1))) a) T.Z)
      (T.card_times (k+1) b) = _
  rw [ite_eq_left rfl]
  rw [T.P_add_eq, T.add]
