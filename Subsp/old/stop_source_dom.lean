import Subsp.old.stop_source_mul

/-! Domain-sensitive source fundamental-sequence lemmas. -/

namespace new

theorem T.fund_P_tail_eq {lam : Nat}
    (ls : Vec (T lam) lam) (add t : T lam)
    (hadd : add ≠ T.Z) :
    T.fund (T.P ls add) t = T.P ls (T.fund add t) := by
  rw [T.fund, ite_eq_right hadd]

end new
