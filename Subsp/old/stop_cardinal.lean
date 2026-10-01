import Subsp.old.stop_card

/-! Normal forms and order comparison for the legacy cardinal multiplier. -/

namespace LegacyTranslation

open T

def cardArg (n p : Nat) (a : T) : T :=
  if p < n then
    if p = 0 then T.early_collapse p a
    else T.stand (T.P p T.Z (T.early_collapse p a))
  else if p = n ∧ a < T.P n (T.P 0 T.Z T.Z) T.Z then T.P n T.Z a
  else a

theorem card_times_P (n p : Nat) (a b : T) :
    T.card_times n (T.P p a b) =
      T.P (max p n) (cardArg n p a) (T.card_times n b) := by
  by_cases hpn : p < n
  · have hm : max p n = n := Nat.max_eq_right (Nat.le_of_lt hpn)
    by_cases hp : p = 0
    · subst p
      simp only [T.card_times, cardArg, hpn, hm, ite_true,
        ← add_eq_hAdd, T.P_add_eq, zero_add]
    · simp only [T.card_times, cardArg, hpn, hp, hm, ite_true, ite_false,
        ← add_eq_hAdd, T.P_add_eq, zero_add]
  · have hm : max p n = p := Nat.max_eq_left (Nat.le_of_not_gt hpn)
    by_cases hp : p = n
    · subst p
      by_cases ha : a < T.P n (T.P 0 T.Z T.Z) T.Z <;>
        simp only [T.card_times, cardArg, hpn, ha, hm, true_and, ite_true, ite_false,
          ← add_eq_hAdd, T.P_add_eq, zero_add]
    · simp only [T.card_times, cardArg, hpn, hp, hm, false_and, ite_false,
        ← add_eq_hAdd, T.P_add_eq, zero_add]

theorem stand_insert_closed (n : Nat) (a b : T) (ha : T.isNF1 a)
    (hg : ∀ x ∈ T.G1 n a, x < a) (hb : T.isNF1 b) :
    T.isNF1 (T.stand (T.P n a b)) := by
  rw [T.stand, stand_eq_self b hb]
  split
  · exact .p n a b ha hb hg ‹_›
  · exact hb

theorem stand_index (n : Nat) (s : T) (hs : T.index_Prop1 n s) :
    T.index_Prop1 n (T.stand s) := by
  induction hs with
  | z => exact .z
  | p p a b hp _ ih =>
      rw [T.stand]
      split
      · exact .p p a _ hp ih
      · exact ih

theorem stand_insert_base_le (n : Nat) (a b : T) (hb : T.isNF1 b) :
    T.P n a T.Z ≤ T.stand (T.P n a b) := by
  rw [T.stand, stand_eq_self b hb]
  split
  · exact head_le_self (T.P n a b)
  · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (lt_of_not_le _ _ ‹_›) (head_le_self b))

theorem head_le_card_of_lt (n : Nat) (a : T)
    (ha : a < T.P n (T.P 0 T.Z T.Z) T.Z) : T.head a ≤ T.P n T.Z T.Z := by
  cases ha with
  | Z_lt_P => exact T.Z_le _
  | p_head _ _ _ _ _ _ h => exact Or.inl (.p_head _ _ _ _ _ _ h)
  | p_mid _ a _ _ _ h =>
      have haz : a = T.Z := by
        cases h with
        | Z_lt_P => rfl
        | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
        | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h
      subst a
      exact Or.inr rfl
  | p_tail _ _ _ _ h => cases h

theorem NF_tail_lt (p : Nat) (a b : T) (hs : T.isNF1 (T.P p a b)) : b < T.P p a b := by
  rcases T.isNF1_tail_le _ hs p a b rfl with h | h
  · exact h
  · have he := congrArg T.size h
    simp only [T.size] at he
    omega

theorem card_prefix_lt (n : Nat) (a : T) (ha : T.isNF1 a)
    (hh : T.head a ≤ T.P n T.Z T.Z) : a < T.P n T.Z a := by
  cases a with
  | Z => exact .Z_lt_P _ _ _
  | P p b c =>
      rcases hh with hh | hh
      · cases hh with
        | p_head _ _ _ _ _ _ h => exact .p_head _ _ _ _ _ _ h
        | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h
      · cases hh
        exact .p_tail _ _ _ _ (NF_tail_lt n T.Z c ha)

theorem cardArg_closed (n p : Nat) (a : T) (ha : T.isNF1 a)
    (hg : ∀ x ∈ T.G1 p a, x < a) :
    T.isNF1 (cardArg n p a) ∧
      (∀ x ∈ T.G1 (max p n) (cardArg n p a), x < cardArg n p a) := by
  unfold cardArg
  split
  · have hpn : p < n := ‹_›
    have hm : max p n = n := Nat.max_eq_right (Nat.le_of_lt hpn)
    obtain ⟨heNF, heIdx⟩ := early_collapse_closed p a ha hg
    split
    · refine ⟨heNF, ?_⟩
      rw [hm, index_Prop1_G1_empty p _ heIdx n hpn]
      intro x hx; cases hx
    · have hnf := stand_insert_closed p T.Z _ .z (fun x hx => by cases hx) heNF
      have hi := stand_index p _ (.p p T.Z _ (Nat.le_refl p) heIdx)
      refine ⟨hnf, ?_⟩
      rw [hm, index_Prop1_G1_empty p _ hi n hpn]
      intro x hx; cases hx
  · split
    · obtain ⟨rfl, halt⟩ := ‹p = n ∧ _›
      have hh := head_le_card_of_lt p a halt
      refine ⟨.p p T.Z a .z ha (fun x hx => by cases hx) hh, ?_⟩
      intro x hx
      simp only [Nat.max_self, T.G1, Nat.le_refl, ite_true, List.append_nil,
        List.mem_append, List.mem_singleton] at hx
      rcases hx with rfl | hx
      · exact .Z_lt_P _ _ _
      · exact lt_trans_thm _ _ _ (hg x hx) (card_prefix_lt p a ha hh)
    · have hnp : n ≤ p := Nat.le_of_not_gt ‹¬ p < n›
      simpa only [Nat.max_eq_left hnp] using (And.intro ha hg)

theorem cardArg_index_of_lt (n p : Nat) (a : T) (ha : T.isNF1 a)
    (hg : ∀ x ∈ T.G1 p a, x < a) (hpn : p < n) :
    T.index_Prop1 p (cardArg n p a) := by
  rw [cardArg, ite_eq_left hpn]
  have hi := (early_collapse_closed p a ha hg).2
  split
  · exact hi
  · exact stand_index p _ (.p p T.Z _ (Nat.le_refl p) hi)

theorem cardArg_lower (n p : Nat) (a : T) (ha : T.isNF1 a)
    (hg : ∀ x ∈ T.G1 p a, x < a) (hp : 0 < p) (hpn : p ≤ n) :
    T.P p T.Z T.Z ≤ cardArg n p a := by
  by_cases hlt : p < n
  · rw [cardArg, ite_eq_left hlt, ite_eq_right (Nat.ne_of_gt hp)]
    exact stand_insert_base_le p T.Z _ (early_collapse_closed p a ha hg).1
  · have he : p = n := by omega
    subst n
    rw [cardArg, ite_eq_right (Nat.lt_irrefl p)]
    split
    · exact head_le_self (T.P p T.Z a)
    · have hnot : ¬ a < T.P p (T.P 0 T.Z T.Z) T.Z := by simpa using ‹¬ (p = p ∧ _)›
      rcases lt_total_thm a (T.P p (T.P 0 T.Z T.Z) T.Z) with h | h | h
      · exact False.elim (hnot h)
      · exact Or.inl (lt_trans_thm _ _ _ (.p_mid _ _ _ _ _ (.Z_lt_P _ _ _)) h)
      · subst a
        exact Or.inl (.p_mid _ _ _ _ _ (.Z_lt_P _ _ _))

theorem cardArg_lt_same (n p : Nat) (a b : T) (ha : T.isNF1 a)
    (hga : ∀ x ∈ T.G1 p a, x < a) (hb : T.isNF1 b)
    (hgb : ∀ x ∈ T.G1 p b, x < b) (hab : a < b) :
    cardArg n p a < cardArg n p b := by
  by_cases hpn : p < n
  · rw [cardArg, ite_eq_left hpn, cardArg, ite_eq_left hpn]
    have he := early_collapse_lt p a b ha hga hb hab
    split
    · exact he
    · exact stand_insert_lt p T.Z _ _ (early_collapse_closed p a ha hga).1
        (early_collapse_closed p b hb hgb).1 he
  · by_cases hp : p = n
    · subst n
      simp only [cardArg, Nat.lt_irrefl, ite_false, true_and]
      by_cases hal : a < T.P p (T.P 0 T.Z T.Z) T.Z
      · rw [ite_eq_left hal]
        split
        · exact .p_tail _ _ _ _ hab
        · have hnot : ¬ b < T.P p (T.P 0 T.Z T.Z) T.Z := ‹_›
          rcases lt_total_thm b (T.P p (T.P 0 T.Z T.Z) T.Z) with h | h | h
          · exact False.elim (hnot h)
          · exact lt_trans_thm _ _ _ (.p_mid _ _ _ _ _ (.Z_lt_P _ _ _)) h
          · subst b
            exact .p_mid _ _ _ _ _ (.Z_lt_P _ _ _)
      · have hbl : ¬ b < T.P p (T.P 0 T.Z T.Z) T.Z :=
          fun h => hal (lt_trans_thm _ _ _ hab h)
        simp only [hal, hbl, ite_false]
        exact hab
    · simpa only [cardArg, hpn, hp, false_and, ite_false] using hab

theorem index_lt_level (p q : Nat) (a : T) (ha : T.index_Prop1 p a) (hpq : p < q) :
    a < T.P q T.Z T.Z := by
  cases ha with
  | z => exact .Z_lt_P _ _ _
  | p r a b hr _ => exact .p_head _ _ _ _ _ _ (Nat.lt_of_le_of_lt hr hpq)

theorem card_heads_lt (n p q : Nat) (a b c d : T) (hpq : p < q)
    (ha : T.isNF1 a) (hga : ∀ x ∈ T.G1 p a, x < a)
    (hb : T.isNF1 b) (hgb : ∀ x ∈ T.G1 q b, x < b) :
    T.P (max p n) (cardArg n p a) c < T.P (max q n) (cardArg n q b) d := by
  by_cases hqn : q ≤ n
  · have hpn : p < n := Nat.lt_of_lt_of_le hpq hqn
    rw [Nat.max_eq_right (Nat.le_of_lt hpn), Nat.max_eq_right hqn]
    exact .p_mid _ _ _ _ _ (lt_of_lt_of_le_thm T _ _ _
      (index_lt_level p q _ (cardArg_index_of_lt n p a ha hga hpn) hpq)
      (cardArg_lower n q b hb hgb (by omega) hqn))
  · apply T.Lt.p_head
    omega

theorem card_times_lt (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (h : s < t) : T.card_times n s < T.card_times n t := by
  induction h with
  | Z_lt_P q a b =>
      rw [card_times_P]
      exact .Z_lt_P _ _ _
  | p_head p q a c b d hpq =>
      rw [card_times_P, card_times_P]
      obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv _ _ _ hs
      obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv _ _ _ ht
      exact card_heads_lt n p q a c _ _ hpq ha hga hc hgc
  | p_mid p a c b d hac _ =>
      rw [card_times_P, card_times_P]
      obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv _ _ _ hs
      obtain ⟨hc, _, hgc, _⟩ := T.isNF1_P_inv _ _ _ ht
      exact .p_mid _ _ _ _ _ (cardArg_lt_same n p a c ha hga hc hgc hac)
  | p_tail p a b d _ ih =>
      rw [card_times_P, card_times_P]
      exact .p_tail _ _ _ _ (ih (T.isNF1_P_inv _ _ _ hs).2.1 (T.isNF1_P_inv _ _ _ ht).2.1)

theorem card_times_le (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (h : s ≤ t) : T.card_times n s ≤ T.card_times n t :=
  h.imp (card_times_lt n s t hs ht) (congrArg (T.card_times n))

theorem card_times_head (n : Nat) (s : T) :
    T.card_times n (T.head s) = T.head (T.card_times n s) := by
  cases s with
  | Z => rfl
  | P p a b =>
      change T.card_times n (T.P p a T.Z) = _
      rw [card_times_P, card_times_P]
      rfl

theorem NF_head (s : T) (hs : T.isNF1 s) : T.isNF1 (T.head s) := by
  cases hs with
  | z => exact .z
  | p p a b ha _ hg _ => exact .p p a T.Z ha .z hg (T.Z_le _)

theorem card_times_closed (n : Nat) (s : T) (hs : T.isNF1 s) :
    T.isNF1 (T.card_times n s) := by
  induction hs with
  | z => exact .z
  | p p a b ha hb hg hh _ ih =>
      obtain ⟨harg, hsupport⟩ := cardArg_closed n p a ha hg
      rw [card_times_P]
      refine .p _ _ _ harg ih hsupport ?_
      have h := card_times_le n (T.head b) (T.P p a T.Z) (NF_head b hb)
        (.p p a T.Z ha .z hg (T.Z_le _)) hh
      rw [card_times_head, card_times_P] at h
      exact h

theorem card_times_index (n u : Nat) (s : T) (hs : T.index_Prop1 u s) :
    T.index_Prop1 (max u n) (T.card_times n s) := by
  induction hs with
  | z => exact .z
  | p p a b hp _ ih =>
      rw [card_times_P]
      exact .p _ _ _ (by omega) ih

theorem card_times_lt_iff (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t) :
    T.card_times n s < T.card_times n t ↔ s < t := by
  refine ⟨?_, card_times_lt n s t hs ht⟩
  intro h
  rcases lt_total_thm s t with hst | hts | he
  · exact hst
  · exact False.elim (lt_asymm_thm h (card_times_lt n t s ht hs hts))
  · subst t
    exact False.elim (lt_irrefl_thm _ h)

theorem card_times_injective (n : Nat) (s t : T) (hs : T.isNF1 s) (ht : T.isNF1 t)
    (h : T.card_times n s = T.card_times n t) : s = t := by
  rcases lt_total_thm s t with hst | hts | he
  · have hlt := card_times_lt n s t hs ht hst
    rw [h] at hlt
    exact False.elim (lt_irrefl_thm _ hlt)
  · have hlt := card_times_lt n t s ht hs hts
    rw [h] at hlt
    exact False.elim (lt_irrefl_thm _ hlt)
  · exact he

end LegacyTranslation
