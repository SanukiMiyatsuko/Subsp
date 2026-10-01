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

theorem cardArg_support_bound (u n p : Nat) (a b c : T)
    (hun : u ≤ n) (hs : T.isNF1 (T.P p a b))
    (hg : ∀ x : T, x ∈ T.G1 u (T.P p a b) → x ≤ c) :
    ∀ x : T, x ∈ T.G1 u (cardArg n p a) → x ≤ c := by
  obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv p a b hs
  have support_arg (hup : u ≤ p) :
      ∀ x : T, x ∈ T.G1 u a → x ≤ c := by
    intro x hx
    apply hg x
    simp [T.G1, hup, hx]
  have arg_le (hup : u ≤ p) : a ≤ c := by
    apply hg a
    simp [T.G1, hup]
  unfold cardArg
  by_cases hpn : p < n
  · rw [ite_eq_left hpn]
    by_cases hup : u ≤ p
    · have hec := early_collapse_closed p a ha hga
      by_cases hp : p = 0
      · rw [ite_eq_left hp]
        exact early_collapse_support_bound u p a c hup ha (arg_le hup) (support_arg hup)
      · rw [ite_eq_right hp]
        apply stand_zero_support_le u p _ c hup hec.1
        exact early_collapse_support_bound u p a c hup ha (arg_le hup) (support_arg hup)
    · have hpu : p < u := Nat.lt_of_not_ge hup
      have hemp : T.G1 u (T.early_collapse p a) = [] :=
        early_collapse_support_above p u a ha hga hpu
      by_cases hp : p = 0
      · rw [ite_eq_left hp, hemp]
        intro x hx
        cases hx
      · rw [ite_eq_right hp, T.stand, stand_eq_self _ (early_collapse_closed p a ha hga).1]
        split
        · simp [T.G1, hup, hemp]
        · rw [hemp]
          intro x hx
          cases hx
  · rw [ite_eq_right hpn]
    have hnp : n ≤ p := Nat.le_of_not_gt hpn
    have hup : u ≤ p := Nat.le_trans hun hnp
    split
    · intro x hx
      simp only [T.G1, hup, ite_true, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · exact T.Z_le c
      · cases hx
      · exact support_arg hup x hx
    · exact support_arg hup

theorem cardArg_head_or_bound (u n p : Nat) (a b tail c : T)
    (hun : u ≤ n) (hs : T.isNF1 (T.P p a b))
    (hg : ∀ x : T, x ∈ T.G1 u (T.P p a b) → x ≤ c) :
    cardArg n p a < T.P (max p n) (cardArg n p a) tail ∨
      cardArg n p a ≤ c := by
  obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv p a b hs
  by_cases hpn : p < n
  · have hm : max p n = n := Nat.max_eq_right (Nat.le_of_lt hpn)
    have hiP := cardArg_index_of_lt n p a ha hga hpn
    have hiN : T.index_Prop1 n (cardArg n p a) :=
      Rank1Termination.index_mono (Nat.le_of_lt hpn) _ hiP
    have hclosed := cardArg_closed n p a ha hga
    have hgood : ∀ x : T, x ∈ T.G1 n (cardArg n p a) → x < cardArg n p a := by
      simpa only [hm] using hclosed.2
    apply Or.inl
    rw [hm]
    cases hiN with
    | z => exact T.Lt.Z_lt_P _ _ _
    | p q d e hq _ =>
        rcases Nat.eq_or_lt_of_le hq with rfl | hq
        · exact T.Lt.p_mid _ _ _ _ _ (hgood d (by simp [T.G1]))
        · exact T.Lt.p_head _ _ _ _ _ _ hq
  · have hnp : n ≤ p := Nat.le_of_not_gt hpn
    have hm : max p n = p := Nat.max_eq_left hnp
    rw [hm]
    unfold cardArg
    rw [ite_eq_right hpn]
    split
    · exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))
    · apply Or.inr
      have hup : u ≤ p := Nat.le_trans hun hnp
      apply hg a
      simp [T.G1, hup]

theorem card_times_support_bound (u n : Nat) (hun : u ≤ n) :
    ∀ s c : T, T.isNF1 s → s ≤ c →
      (∀ x : T, x ∈ T.G1 u s → x ≤ c) →
      ∀ x : T, x ∈ T.G1 u (T.card_times n s) →
        x < T.card_times n s ∨ x ≤ c := by
  intro s c hs hsc hsup
  induction hs generalizing c with
  | z =>
      intro x hx
      cases hx
  | p p a b ha hb hga hh _ ih =>
      have hsfull : T.isNF1 (T.P p a b) := .p p a b ha hb hga hh
      rw [card_times_P]
      have hum : u ≤ max p n := Nat.le_trans hun (Nat.le_max_right p n)
      intro x hx
      simp only [T.G1, hum, ite_true, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · exact cardArg_head_or_bound u n p a b (T.card_times n b) c hun hsfull hsup
      · exact Or.inr (cardArg_support_bound u n p a b c hun hsfull hsup x hx)
      · have hb_le : b ≤ c := partial_order.trans _ _ _
          (T.isNF1_tail_le _ hsfull p a b rfl) hsc
        have hbsup : ∀ y : T, y ∈ T.G1 u b → y ≤ c := by
          intro y hy
          apply hsup y
          by_cases hup : u ≤ p <;> simp [T.G1, hup, hy]
        rcases ih c hb_le hbsup x hx with h | h
        · exact Or.inl (T.Lt.p_tail _ _ _ _ h)
        · exact Or.inr h

theorem card_times_good (n : Nat) (s : T) (hs : T.isNF1 s)
    (hg : ∀ x ∈ T.G1 n s, x < s) :
    ∀ x ∈ T.G1 n (T.card_times n s), x < T.card_times n s := by
  intro x hx
  rcases card_times_support n s hs x hx with h | h
  · exact h
  · exact lt_of_lt_of_le_thm T _ _ _ (hg x h) (card_times_self_le n s hs)

theorem one_del_G1_subset (u : Nat) (s x : T)
    (hx : x ∈ T.G1 u (T.one_del s)) :
    x ∈ T.G1 u s := by
  cases s with
  | Z => exact hx
  | P p a b =>
      cases p with
      | zero =>
          cases a with
          | Z =>
              by_cases hu : u ≤ 0
              · simp only [T.one_del, T.G1, hu, ite_true, List.mem_append,
                  List.mem_singleton] at hx ⊢
                exact Or.inr (Or.inr hx)
              · simpa only [T.one_del, T.G1, hu, ite_false] using hx
          | P q c d => exact hx
      | succ p => exact hx

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
