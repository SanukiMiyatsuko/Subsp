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


theorem trans_iter {lam : Nat}
    (F : new.T lam → new.T lam) (G : T → T)
    (hFG : ∀ x, trans (F x) = G (trans x))
    (t : new.T lam) :
    trans (new.T.iter F t) = T.iter G (trans t) := by
  induction t using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v a _ ih =>
      rw [new.T.iter, hFG, _root_.trans.eq_2]
      rcases haux : transAux v with ⟨head, lower⟩
      simp only [haux, T.iter, ih]
  | nil => trivial
  | snoc => trivial


theorem trans_fund_tail {lam : Nat}
    (ls : new.Vec (new.T lam) lam) (add t : new.T lam)
    (hadd : add ≠ new.T.Z)
    (hrec :
      trans (new.T.fund add t) =
        T.fund1 (trans add) (trans t)) :
    trans (new.T.fund (new.T.P ls add) t) =
      T.fund1 (trans (new.T.P ls add)) (trans t) := by
  rw [new.T.fund, ite_eq_right hadd]
  obtain ⟨p, a, hhead, _⟩ := aux_principal ls
  simp only [trans_as_add, hhead, p_zero_add]
  cases hta : trans add with
  | Z =>
      exact False.elim
        (trans_ne_zero_of_ne_zero add hadd hta)
  | P q c d =>
      rw [hrec, hta]
      rfl

end LegacyTranslation
