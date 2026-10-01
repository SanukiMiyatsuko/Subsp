import Subsp.old.stop_nf_core
import Subsp.old.stop_source_fund_nf

/-! Basic support embeddings used by the legacy translation support proof. -/

namespace LegacyTranslation

theorem source_vec_idx_mem_Gi {lam k : Nat} (u : Nat)
    (v : new.Vec (new.T lam) k) (i : Fin k) (hui : u ≤ i.val) :
    v.idx i ∈ new.Vec.Gi u v := by
  exact (new.Vec.mem_Gi_iff u v (v.idx i)).2
    ⟨i, hui, Or.inl rfl⟩

theorem source_coord_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (i : Fin lam) (hui : u ≤ i.val) :
    v.idx i ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a (v.idx i)).2
    (Or.inl ⟨i, hui, Or.inl rfl⟩)

theorem source_coord_support_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (i : Fin lam) (hui : u ≤ i.val)
    (hz : z ∈ new.T.Gi u (v.idx i)) :
    z ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a z).2
    (Or.inl ⟨i, hui, Or.inr hz⟩)

theorem source_tail_support_mem_Gi {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a z : new.T lam)
    (hz : z ∈ new.T.Gi u a) :
    z ∈ new.T.Gi u (new.T.P v a) := by
  exact (new.T.mem_Gi_P u v a z).2 (Or.inr hz)

theorem trans_tail_le {lam : Nat}
    (v : new.Vec (new.T lam) lam) (a : new.T lam)
    (h : T.isNF1 (trans (new.T.P v a))) :
    trans a ≤ trans (new.T.P v a) := by
  rw [trans_as_add]
  exact add_right_le_of_NF _ _ h

theorem trans_head_support_mem {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam) (x : T)
    (hx : x ∈ T.G1 u (transAux v).1) :
    x ∈ T.G1 u (trans (new.T.P v a)) := by
  rw [trans_as_add, G1_add]
  exact List.mem_append_left _ hx

theorem trans_tail_support_mem {lam : Nat} (u : Nat)
    (v : new.Vec (new.T lam) lam) (a : new.T lam) (x : T)
    (hx : x ∈ T.G1 u (trans a)) :
    x ∈ T.G1 u (trans (new.T.P v a)) := by
  rw [trans_as_add, G1_add]
  exact List.mem_append_right _ hx


theorem cardArg_head_or_eq (n p : Nat) (a b tail : T)
    (hs : T.isNF1 (T.P p a b)) :
    cardArg n p a < T.P (max p n) (cardArg n p a) tail ∨
      (n ≤ p ∧ cardArg n p a = a) := by
  obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv p a b hs
  by_cases hpn : p < n
  · apply Or.inl
    have hm : max p n = n := Nat.max_eq_right (Nat.le_of_lt hpn)
    have hiP := cardArg_index_of_lt n p a ha hga hpn
    have hiN : T.index_Prop1 n (cardArg n p a) :=
      Rank1Termination.index_mono (Nat.le_of_lt hpn) _ hiP
    have hclosed := cardArg_closed n p a ha hga
    have hgood : ∀ x : T, x ∈ T.G1 n (cardArg n p a) → x < cardArg n p a := by
      simpa only [hm] using hclosed.2
    rw [hm]
    exact good_index_lt_wrap n _ tail hiN hgood
  · have hnp : n ≤ p := Nat.le_of_not_gt hpn
    rw [Nat.max_eq_left hnp]
    unfold cardArg
    rw [ite_eq_right hpn]
    split
    · apply Or.inl
      obtain ⟨rfl, _⟩ := ‹p = n ∧ _›
      exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)
    · exact Or.inr ⟨hnp, rfl⟩

theorem card_times_support_decomp (u n : Nat) (hun : u ≤ n)
    (R : T → Prop)
    (hR : ∀ x y : T, x ≤ y → R y → R x) :
    ∀ s c : T, T.isNF1 s → s ≤ c →
      (∀ y : T, y ∈ T.G1 u s → y < c ∨ R y) →
      ∀ x : T, x ∈ T.G1 u (T.card_times n s) →
        x < T.card_times n s ∨ x < c ∨ R x := by
  intro s c hs hsc hdec
  induction hs generalizing c with
  | z =>
      intro x hx
      cases hx
  | p p a b ha hb hga hh _ ih =>
      have hsfull : T.isNF1 (T.P p a b) := .p p a b ha hb hga hh
      rw [card_times_P]
      intro x hx
      have hum : u ≤ max p n := Nat.le_trans hun (Nat.le_max_right p n)
      simp only [T.G1, hum, ite_true, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · rcases cardArg_head_or_eq n p a b (T.card_times n b) hsfull with h | ⟨hnp, heq⟩
        · exact Or.inl h
        · rw [heq]
          have hup : u ≤ p := Nat.le_trans hun hnp
          rcases hdec a (by simp [T.G1, hup]) with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      · obtain ⟨y, hy, hxy⟩ :=
          cardArg_support_witness u n p a b hun hsfull x hx
        rcases hdec y hy with h | h
        · exact Or.inr (Or.inl (lt_of_le_of_lt_thm T _ _ _ hxy h))
        · exact Or.inr (Or.inr (hR x y hxy h))
      · have hb_le_c : b ≤ c := partial_order.trans _ _ _
          (T.isNF1_tail_le _ hsfull p a b rfl) hsc
        have hdec_b : ∀ y : T, y ∈ T.G1 u b → y < c ∨ R y := by
          intro y hy
          apply hdec y
          by_cases hup : u ≤ p <;> simp [T.G1, hup, hy]
        rcases ih c hb_le_c hdec_b x hx with h | h | h
        · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

end LegacyTranslation
