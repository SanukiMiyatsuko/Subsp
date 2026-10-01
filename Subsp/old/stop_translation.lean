import Subsp.old.stop_types
import Subsp.old.stop_countable
import Subsp.old.trans

/-! Bounds for the legacy translation, including all dimensions of OT. -/

namespace LegacyTranslation

theorem zero_add (t : T) : T.add T.Z t = t := by
  cases t <;> rfl

theorem trans_as_add {lam : Nat} (v : new.Vec (new.T lam) lam) (b : new.T lam) :
    trans (new.T.P v b) = T.add (transAux v).1 (trans b) := by
  cases h : transAux v
  rw [_root_.trans.eq_2, h]
  rfl

theorem aux_zero_tail {lam k : Nat} (v : new.Vec (new.T lam) (k + 1)) :
    (transAux (.snoc (k + 1) v new.T.Z)).1 = (transAux v).1 := by
  cases h : transAux v
  simp [transAux, h]

theorem aux_principal {lam k : Nat} (v : new.Vec (new.T lam) k) :
    ∃ p a, (transAux v).1 = T.P p a T.Z ∧ p ≤ k - 1 := by
  induction v with
  | nil => exact ⟨0, T.Z, rfl, Nat.le_refl 0⟩
  | snoc k v a ih =>
      cases k with
      | zero =>
          cases v
          cases a <;> exact ⟨0, _, rfl, Nat.le_refl 0⟩
      | succ k =>
          cases a with
          | Z =>
              obtain ⟨p, a, he, hp⟩ := ih
              exact ⟨p, a, (aux_zero_tail v).trans he, by omega⟩
          | P w b =>
              rcases haux : transAux v with ⟨head, lower⟩
              refine ⟨k + 1, T.card_times (k + 1) (T.one_del (trans (new.T.P w b))) + lower, ?_, Nat.le_refl _⟩
              rw [transAux, haux]

theorem trans_lt_level {lam : Nat} (s : new.T lam) (hlam : 0 < lam) :
    trans s < T.P lam T.Z T.Z := by
  cases s with
  | Z => exact .Z_lt_P _ _ _
  | P v b =>
      obtain ⟨p, a, he, hp⟩ := aux_principal v
      rw [trans_as_add, he, T.P_add_eq, zero_add]
      exact .p_head _ _ _ _ _ _ (by omega)

theorem aux_countable_head {lam k : Nat} (v : new.Vec (new.T lam) k)
    (hv : ∀ i : Fin k, 0 < i.val → v.idx i = new.T.Z) :
    ∃ a : new.T lam, (transAux v).1 = T.P 0 (trans a) T.Z := by
  induction v with
  | nil => exact ⟨new.T.Z, rfl⟩
  | snoc k v a ih =>
      cases k with
      | zero =>
          cases v
          cases a with
          | Z => exact ⟨new.T.Z, rfl⟩
          | P w b => exact ⟨new.T.P w b, rfl⟩
      | succ k =>
          have haz : a = new.T.Z := by
            simpa [new.Vec.idx] using hv (Fin.last (k + 1)) (Nat.zero_lt_succ k)
          subst a
          have hvp : ∀ i : Fin (k + 1), 0 < i.val → v.idx i = new.T.Z := by
            intro i hi
            simpa [new.Vec.idx, i.isLt] using hv i.castSucc hi
          obtain ⟨a, he⟩ := ih hvp
          exact ⟨a, (aux_zero_tail v).trans he⟩

theorem Countable_bound {lam : Nat} (s : new.T lam) (hs : new.T.Countable s) :
    trans s < T.P 0 (T.P lam T.Z T.Z) T.Z := by
  cases hs with
  | z => exact .Z_lt_P _ _ _
  | p v b hv _ =>
      cases lam with
      | zero =>
          cases v
          rw [trans_as_add]
          change T.add (T.P 0 T.Z T.Z) (trans b) < _
          rw [T.P_add_eq, zero_add]
          exact .p_mid _ _ _ _ _ (.Z_lt_P _ _ _)
      | succ k =>
          obtain ⟨a, he⟩ := aux_countable_head v hv
          rw [trans_as_add, he, T.P_add_eq, zero_add]
          exact .p_mid _ _ _ _ _ (trans_lt_level a (Nat.zero_lt_succ k))

theorem OT_bound (lam : Nat) (s : new.T lam) (hs : new.T.isOT lam s) :
    trans s < T.P 0 (T.P lam T.Z T.Z) T.Z :=
  Countable_bound s (new.T.isOT_Countable lam s hs)

end LegacyTranslation
