import Subsp.old.stop_cardinal

/-! Support bounds for cardinal multiplication and lower-index remainders. -/

namespace LegacyTranslation

open T

theorem head_base_le (n p : Nat) (a : T) (hnp : n ≤ p) : T.P n T.Z T.Z ≤ T.P p a T.Z := by
  rcases Nat.eq_or_lt_of_le hnp with rfl | hnp
  · exact (T.Z_le a).imp (T.Lt.p_mid _ _ _ _ _) (congrArg (fun x => T.P n x T.Z))
  · exact Or.inl (.p_head _ _ _ _ _ _ hnp)

theorem card_times_self_le (n : Nat) (s : T) (hs : T.isNF1 s) : s ≤ T.card_times n s := by
  induction hs with
  | z => exact Or.inr rfl
  | p p a b ha _ _ _ _ ih =>
      rw [card_times_P]
      by_cases hpn : p < n
      · exact Or.inl (.p_head _ _ _ _ _ _ (by omega))
      · rw [cardArg, ite_eq_right hpn]
        split
        · obtain ⟨rfl, halt⟩ := ‹p = n ∧ _›
          rw [Nat.max_self]
          exact Or.inl (.p_mid _ _ _ _ _ (card_prefix_lt p a ha (head_le_card_of_lt p a halt)))
        · rw [Nat.max_eq_left (Nat.le_of_not_gt hpn)]
          exact ih.imp (T.Lt.p_tail _ _ _ _) (congrArg (T.P p a))

theorem card_times_support (n : Nat) (s : T) (hs : T.isNF1 s) :
    ∀ x ∈ T.G1 n (T.card_times n s), x < T.card_times n s ∨ x ∈ T.G1 n s := by
  induction hs with
  | z => intro x hx; cases hx
  | p p a b ha hb hg hh _ ih =>
      have hnf := card_times_closed n _ (.p p a b ha hb hg hh)
      rw [card_times_P] at hnf ⊢
      have htail := NF_tail_lt _ _ _ hnf
      intro x hx
      have hnp : n ≤ max p n := Nat.le_max_right p n
      simp only [T.G1, hnp, ite_true, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · by_cases hpn : p < n
        · apply Or.inl
          have hi := cardArg_index_of_lt n p a ha hg hpn
          exact lt_of_lt_of_le_thm T _ _ _ (index_lt_level p n _ hi hpn)
            (partial_order.trans _ _ _ (head_base_le n (max p n) _ (Nat.le_max_right p n))
              (head_le_self (T.P (max p n) (cardArg n p a) (T.card_times n b))))
        · rw [cardArg, ite_eq_right hpn]
          split
          · obtain ⟨rfl, _⟩ := ‹p = n ∧ _›
            rw [Nat.max_self]
            exact Or.inl (.p_mid _ _ _ _ _ (.Z_lt_P _ _ _))
          · exact Or.inr (by simp [T.G1, Nat.le_of_not_gt hpn])
      · by_cases hpn : p < n
        · rw [index_Prop1_G1_empty p _ (cardArg_index_of_lt n p a ha hg hpn) n hpn] at hx
          cases hx
        · have hnp' : n ≤ p := Nat.le_of_not_gt hpn
          unfold cardArg at hx
          rw [ite_eq_right hpn] at hx
          split at hx
          · obtain ⟨rfl, _⟩ := ‹p = n ∧ _›
            simp only [T.G1, Nat.le_refl, ite_true, List.mem_append,
              List.mem_singleton, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | hx
            · exact Or.inl (.Z_lt_P _ _ _)
            · exact Or.inr (by simp [T.G1, hx])
          · exact Or.inr (by simp [T.G1, hnp', hx])
      · rcases ih x hx with h | h
        · exact Or.inl (lt_trans_thm _ _ _ h htail)
        · apply Or.inr
          by_cases hnp' : n ≤ p <;> simp [T.G1, hnp', h]

theorem card_times_good (n : Nat) (s : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) :
    ∀ x ∈ T.G1 n (T.card_times n s), x < T.card_times n s := by
  intro x hx
  rcases card_times_support n s hs x hx with h | h
  · exact h
  · exact lt_of_lt_of_le_thm T _ _ _ (hg x h) (card_times_self_le n s hs)

theorem one_del_good_pos (n : Nat) (hn : 0 < n) (s : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) :
    ∀ x ∈ T.G1 n (T.one_del s), x < T.one_del s := by
  cases s with
  | Z => exact hg
  | P p a b =>
      cases p with
      | zero =>
          cases a with
          | Z =>
              have hi := isNF1_index 0 0 T.Z b hs (Nat.le_refl 0)
              cases hi with
              | p _ _ _ _ hb =>
                  change ∀ x ∈ T.G1 n b, x < b
                  rw [index_Prop1_G1_empty 0 b hb n hn]
                  intro x hx; cases hx
          | P _ _ _ => exact hg
      | succ _ => exact hg

theorem card_times_append_closed (n : Nat) (s b : T) (hs : T.isNF1 s)
    (hb : T.isNF1 b) (hbound : b < T.P n T.Z T.Z) :
    T.isNF1 (T.add (T.card_times n s) b) := by
  induction hs with
  | z => exact hb
  | p p a c ha hc hg hh _ ih =>
      rw [card_times_P, T.P_add_eq]
      obtain ⟨harg, hsupport⟩ := cardArg_closed n p a ha hg
      refine .p _ _ _ harg ih hsupport ?_
      cases c with
      | Z =>
          exact partial_order.trans _ _ _ (T.head_mono hbound)
            (head_base_le n (max p n) _ (Nat.le_max_right p n))
      | P q d e =>
          have hnf := card_times_closed n _ (.p p a (T.P q d e) ha hc hg hh)
          rw [card_times_P] at hnf
          have hhead := (T.isNF1_P_inv _ _ _ hnf).2.2.2
          rw [card_times_P, T.head_add_ne_Z]
          simpa only [card_times_P, T.head] using hhead

theorem card_times_append_good (n u : Nat) (hun : u < n) (s b : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) (hb : T.index_Prop1 u b) :
    ∀ x ∈ T.G1 n (T.add (T.card_times n s) b), x < T.add (T.card_times n s) b := by
  intro x hx
  rw [G1_add, index_Prop1_G1_empty u b hb n hun, List.append_nil] at hx
  exact lt_of_lt_of_le_thm T _ _ _ (card_times_good n s hs hg x hx) (add_self_le _ _)

end LegacyTranslation
