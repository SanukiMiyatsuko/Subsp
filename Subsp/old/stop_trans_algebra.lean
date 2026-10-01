import Subsp.old.stop_ot_domain

/-! Algebraic compatibility of the legacy translation. -/

namespace LegacyTranslation

theorem trans_add {lam : Nat} (s t : new.T lam) :
    trans (s + t) = T.add (trans s) (trans t) := by
  induction s using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v a _ ih =>
      change trans (new.T.P v (a + t)) = T.add (trans (new.T.P v a)) (trans t)
      rw [trans_as_add, trans_as_add, ih]
      exact (Rank1Termination.add_assoc (transAux v).1 (trans a) (trans t)).symm
  | nil => trivial
  | snoc => trivial

theorem target_add_mul_comm (s t : T) :
    T.add s (T.mul s t) = T.add (T.mul s t) s := by
  induction t with
  | Z => cases s <;> rfl
  | P _ _ b _ ih =>
      change T.add s (T.add (T.mul s b) s) = T.add (T.add (T.mul s b) s) s
      rw [← Rank1Termination.add_assoc, ih]

theorem trans_mul {lam : Nat} (s t : new.T lam) :
    trans (new.T.mul s t) = T.mul (trans s) (trans t) := by
  induction t using new.T.rec (motive_2 := fun _ _ => True) with
  | Z => rfl
  | P v a _ ih =>
      rw [new.T.mul, trans_add, ih, trans_as_add]
      obtain ⟨p, b, hhead, _⟩ := aux_principal v
      rw [hhead, T.P_add_eq, zero_add, T.mul]
      exact target_add_mul_comm (trans s) (trans a)
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
      rw [new.T.iter, hFG, trans_as_add]
      obtain ⟨p, b, hhead, _⟩ := aux_principal v
      rw [hhead, T.P_add_eq, zero_add, T.iter, ih]
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
