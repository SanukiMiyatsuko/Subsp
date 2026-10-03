import Subsp.old.stop_types
import Subsp.old.stop_basic
import Subsp.old.trans

/-! Outer shape of the legacy translation and its bound on OT. -/

namespace LegacyTranslation

theorem zero_add (t : T) : T.add T.Z t = t := by
  cases t <;> rfl

theorem p_zero_add (p : Nat) (a y : T) : T.add (T.P p a T.Z) y = T.P p a y := by
  cases y <;> rfl

theorem trans_as_add {lam : Nat} (v : new.Vec (new.T lam) lam) (b : new.T lam) :
    trans (new.T.P v b) = T.add (transAux v).1 (trans b) := by
  cases h : transAux v
  rw [_root_.trans.eq_2, h]
  rfl

theorem transAux_snoc_zero {lam m : Nat} (v : new.Vec (new.T lam) (m + 1)) :
    transAux (new.Vec.snoc (m + 1) v new.T.Z) = transAux v := by
  simp only [transAux, _root_.trans, T.early_collapse, T.part]
  exact Prod.eta _

theorem aux_zero_tail {lam k : Nat} (v : new.Vec (new.T lam) (k + 1)) :
    (transAux (.snoc (k + 1) v new.T.Z)).1 = (transAux v).1 :=
  congrArg Prod.fst (transAux_snoc_zero v)

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
              refine ⟨k + 1, T.card_times (k + 1) (T.one_del (trans (new.T.P w b))) + lower, ?_,
                Nat.le_refl _⟩
              rw [transAux, haux]

theorem trans_lt_level {lam : Nat} (s : new.T lam) (hlam : 0 < lam) :
    trans s < T.P lam T.Z T.Z := by
  cases s with
  | Z => exact .Z_lt_P _ _ _
  | P v b =>
      obtain ⟨p, a, he, hp⟩ := aux_principal v
      rw [trans_as_add, he, p_zero_add]
      exact .p_head _ _ _ _ _ _ (by omega)

theorem trans_ne_zero_of_ne_zero {lam : Nat} (s : new.T lam) (hs : s ≠ new.T.Z) :
    trans s ≠ T.Z := by
  cases s with
  | Z => exact absurd rfl hs
  | P v b =>
      obtain ⟨p, a, hp, _⟩ := aux_principal v
      rw [trans_as_add, hp, p_zero_add]
      intro h; cases h

theorem transAux_countable_exact {lam k : Nat} (v : new.Vec (new.T lam) (k + 1))
    (hv : ∀ i : Fin (k + 1), 0 < i.val → v.idx i = new.T.Z) :
    transAux v = transAux (new.Vec.snoc 0 new.Vec.nil (v.idx ⟨0, Nat.zero_lt_succ k⟩)) := by
  induction k with
  | zero => cases v with | snoc _ xs a => cases xs; rfl
  | succ k ih =>
      cases v with
      | snoc _ xs a =>
          obtain rfl : a = new.T.Z := by
            simpa [new.Vec.idx] using hv (Fin.last (k + 1)) (Nat.zero_lt_succ k)
          rw [transAux_snoc_zero]
          simpa [new.Vec.idx] using
            ih xs fun i hi => by simpa [new.Vec.idx, i.isLt] using hv i.castSucc hi

theorem transAux_zeros {lam : Nat} (k : Nat) :
    transAux (new.Vec.ofFn k (fun _ => (new.T.Z : new.T lam))) = (T.P 0 T.Z T.Z, T.Z) := by
  cases k with
  | zero => rfl
  | succ k =>
      rw [transAux_countable_exact _ fun i _ => new.Vec.ofFn_idx _ _ i]
      simp [new.Vec.ofFn_idx, transAux, _root_.trans, T.early_collapse, T.part]

theorem transAux_countable_head_exact {lam k : Nat} (v : new.Vec (new.T lam) (k + 1))
    (hv : ∀ i : Fin (k + 1), 0 < i.val → v.idx i = new.T.Z) :
    (transAux v).1 = T.P 0 (trans (v.idx ⟨0, Nat.zero_lt_succ k⟩)) T.Z := by
  rw [transAux_countable_exact v hv]
  cases v.idx ⟨0, Nat.zero_lt_succ k⟩ <;> simp [transAux, _root_.trans]

theorem OT_bound (lam : Nat) (s : new.T lam) (hs : new.T.isOT lam s) :
    trans s < T.P 0 (T.P lam T.Z T.Z) T.Z := by
  rcases new.T.isOT_Countable lam s hs with _ | ⟨v, b, hv, _⟩
  · exact .Z_lt_P _ _ _
  · cases lam with
    | zero =>
        cases v
        show T.add (T.P 0 T.Z T.Z) (trans b) < _
        rw [p_zero_add]
        exact .p_mid _ _ _ _ _ (.Z_lt_P _ _ _)
    | succ k =>
        rw [trans_as_add, transAux_countable_head_exact v hv, p_zero_add]
        exact .p_mid _ _ _ _ _ (trans_lt_level _ (Nat.zero_lt_succ k))

end LegacyTranslation
