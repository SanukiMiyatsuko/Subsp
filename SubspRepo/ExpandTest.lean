import CardAlg
open T

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
#print axioms wt_expand_card_succ_add
