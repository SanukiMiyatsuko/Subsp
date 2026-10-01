import Subsp.old.stop_principal

/-! Lexicographic comparison of the two components of `transAux`. -/

namespace LegacyTranslation

open T

def VecMono {lam k : Nat} (v w : new.Vec (new.T lam) k) : Prop :=
  ∀ i : Fin k, v.idx i < w.idx i → trans (v.idx i) < trans (w.idx i)

theorem VecMono_prefix {lam k : Nat} (v w : new.Vec (new.T lam) k) (a b : new.T lam)
    (h : VecMono (.snoc k v a) (.snoc k w b)) : VecMono v w := by
  intro i
  simpa only [new.Vec.idx, Fin.val_castSucc, i.isLt, dite_true] using h i.castSucc

theorem VecMono_last {lam k : Nat} (v w : new.Vec (new.T lam) k) (a b : new.T lam)
    (h : VecMono (.snoc k v a) (.snoc k w b)) : a < b → trans a < trans b := by
  simpa only [new.Vec.idx, Fin.val_last, Nat.lt_irrefl, dite_false] using h (Fin.last k)

theorem compare_snoc_lt {lam k : Nat} (v w : new.Vec (new.T lam) k) (a b : new.T lam)
    (h : new.compareVec (.snoc k v a) (.snoc k w b) = .lt) :
    a < b ∨ (a = b ∧ new.compareVec v w = .lt) := by
  simp only [new.compareVec] at h
  cases hab : new.compareT a b with
  | lt => exact Or.inl hab
  | eq => exact Or.inr ⟨new.T_eq_sound a b hab, by simpa only [hab] using h⟩
  | gt => simp [hab] at h

theorem aux_lower_lt {lam k : Nat} (v w : new.Vec (new.T lam) k)
    (hv : VecGood v) (hw : VecGood w) (hm : VecMono v w)
    (hlt : new.compareVec v w = .lt) : (transAux v).2 < (transAux w).2 := by
  induction v with
  | nil => cases w; cases hlt
  | snoc k v a ih =>
      cases w with
      | snoc _ w b =>
          have ha := VecGood_last v a hv
          have hb := VecGood_last w b hw
          have hvp := VecGood_prefix v a hv
          have hwp := VecGood_prefix w b hw
          have hmp := VecMono_prefix v w a b hm
          have hmab := VecMono_last v w a b hm
          rcases compare_snoc_lt v w a b hlt with hab | ⟨rfl, hrest⟩
          · have he := early_collapse_lt k _ _ ha.1 ha.2 hb.1 (hmab hab)
            cases k with
            | zero =>
                cases v; cases w
                rw [aux_single, aux_single]
                exact he
            | succ k =>
                rw [aux_lower_snoc, aux_lower_snoc]
                exact card_times_append_lt (k + 1) _ _ _ _
                  (early_collapse_closed (k + 1) _ ha.1 ha.2).1
                  (early_collapse_closed (k + 1) _ hb.1 hb.2).1 he
                  (aux_lower_closed v hvp).2.2
          · cases k with
            | zero => cases v; cases w; cases hrest
            | succ k =>
                rw [aux_lower_snoc, aux_lower_snoc]
                exact add_left_lt _ _ _ (ih w hvp hwp hmp hrest)

theorem aux_head_lt {lam k : Nat} (v w : new.Vec (new.T lam) k)
    (hv : VecGood v) (hw : VecGood w) (hm : VecMono v w)
    (hlt : new.compareVec v w = .lt) : (transAux v).1 < (transAux w).1 := by
  induction v with
  | nil => cases w; cases hlt
  | snoc k v a ih =>
      cases w with
      | snoc _ w b =>
          have ha := VecGood_last v a hv
          have hb := VecGood_last w b hw
          have hvp := VecGood_prefix v a hv
          have hwp := VecGood_prefix w b hw
          have hmp := VecMono_prefix v w a b hm
          have hmab := VecMono_last v w a b hm
          rcases compare_snoc_lt v w a b hlt with hab | ⟨rfl, hrest⟩
          · cases k with
            | zero =>
                cases v; cases w
                rw [aux_single, aux_single]
                exact .p_mid _ _ _ _ _ (hmab hab)
            | succ k =>
                have hbn : b ≠ new.T.Z := by
                  intro he
                  subst b
                  cases a <;> cases hab
                rw [aux_head_snoc w b hbn]
                by_cases haz : a = new.T.Z
                · subst a
                  rw [aux_zero_tail]
                  obtain ⟨p, c, he, hp⟩ := aux_principal v
                  rw [he]
                  exact .p_head _ _ _ _ _ _ (by omega)
                · rw [aux_head_snoc v a haz]
                  exact .p_mid _ _ _ _ _ (card_times_append_lt (k + 1) _ _ _ _
                    (one_del_NF _ ha.1) (one_del_NF _ hb.1)
                    (one_del_lt _ _ ha.1 (trans_ne_zero_of_ne_zero a haz) (hmab hab))
                    (aux_lower_closed v hvp).2.2)
          · cases k with
            | zero => cases v; cases w; cases hrest
            | succ k =>
                by_cases haz : a = new.T.Z
                · subst a
                  rw [aux_zero_tail, aux_zero_tail]
                  exact ih w hvp hwp hmp hrest
                · rw [aux_head_snoc v a haz, aux_head_snoc w a haz]
                  exact .p_mid _ _ _ _ _
                    (add_left_lt _ _ _ (aux_lower_lt v w hvp hwp hmp hrest))

theorem trans_P_head {lam : Nat} (v : new.Vec (new.T lam) lam) (b : new.T lam) :
    T.head (trans (new.T.P v b)) = (transAux v).1 := by
  obtain ⟨p, a, he, _⟩ := aux_principal v
  rw [trans_as_add, he, T.P_add_eq, zero_add]
  rfl

theorem trans_lt_of_vec_lt {lam : Nat} (v w : new.Vec (new.T lam) lam) (a b : new.T lam)
    (hv : VecGood v) (hw : VecGood w) (hm : VecMono v w)
    (hlt : new.compareVec v w = .lt) :
    trans (new.T.P v a) < trans (new.T.P w b) := by
  apply lt_of_head_lt
  rw [trans_P_head, trans_P_head]
  exact aux_head_lt v w hv hw hm hlt

end LegacyTranslation
