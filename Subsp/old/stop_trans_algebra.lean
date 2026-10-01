import Subsp.old.stop_ot_domain

/-! Algebraic compatibility of the legacy translation. -/

namespace LegacyTranslation

theorem trans_add {lam : Nat} (s t : new.T lam) :
    trans (new.T.add s t) = T.add (trans s) (trans t) := by
  induction s with
  | Z => rfl
  | P v a _ ih =>
      rw [new.T.add, trans_as_add, trans_as_add, ih]
      exact Rank1Termination.add_assoc (transAux v).1 (trans a) (trans t)

theorem trans_mul {lam : Nat} (s t : new.T lam) :
    trans (new.T.mul s t) = T.mul (trans s) (trans t) := by
  induction t using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v a _ ih =>
      rw [new.T.mul, trans_add, _root_.trans.eq_2]
      rcases haux : transAux v with ⟨head, lower⟩
      simp only [haux, T.mul, ih]
  | nil => trivial
  | snoc => trivial

end LegacyTranslation
