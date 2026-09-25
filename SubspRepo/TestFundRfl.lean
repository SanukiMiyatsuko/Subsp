import Subsp.Buchholz.Rank1
import Subsp.new.subsp
import Subsp.new.trans
open T

theorem test_trans_ofNat {lam : Nat} (n : Nat) :
  trans (new.T.ofNat (lam := lam) n) = T.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [new.T.ofNat, T.ofNat, trans]
    change T.P 0 T.Z (trans (new.T.ofNat n)) = T.P 0 T.Z (T.ofNat n)
    rw [ih]

theorem test_trans_fund_rfl {lam : Nat} (s t : new.T lam) :
  trans (new.T.fund s t) = T.fund1 (trans s) (trans t) := by
  cases s with
  | Z =>
      rw [new.T.fund, trans, T.fund1]
  | P ls add =>
    sorry
