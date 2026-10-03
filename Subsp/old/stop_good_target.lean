import Subsp.old.stop_principal

/-! Target-side support bounds for cardinal multiplication and early collapse. -/

namespace LegacyTranslation

open T

/-- Every summand `P p c _` of a target term satisfies `Pr p c`. -/
def SumAll (Pr : Nat → T → Prop) : T → Prop
  | .Z => True
  | .P p c r => Pr p c ∧ SumAll Pr r

/-- `P p c _` occurs as a summand of a target term. -/
def IsSummand (p : Nat) (c : T) : T → Prop
  | .Z => False
  | .P q a r => (q = p ∧ a = c) ∨ IsSummand p c r

theorem SumAll_mono (Pr Qr : Nat → T → Prop) (h : ∀ p c, Pr p c → Qr p c) :
    ∀ t, SumAll Pr t → SumAll Qr t
  | .Z, _ => trivial
  | .P p c r, ⟨hpc, hr⟩ => ⟨h p c hpc, SumAll_mono Pr Qr h r hr⟩

theorem SumAll_of_summand (Pr : Nat → T → Prop) :
    ∀ t, (∀ p c, IsSummand p c t → Pr p c) → SumAll Pr t
  | .Z, _ => trivial
  | .P q a r, h => ⟨h q a (Or.inl ⟨rfl, rfl⟩),
      SumAll_of_summand Pr r (fun p c hs => h p c (Or.inr hs))⟩

theorem SumAll_part (Pr : Nat → T → Prop) (n : Nat) : ∀ t, SumAll Pr t →
    SumAll (fun p c => n < p ∧ Pr p c) (T.part n t).1 ∧
      SumAll (fun p c => p ≤ n ∧ Pr p c) (T.part n t).2
  | .Z, _ => ⟨trivial, trivial⟩
  | .P p c r, ⟨hpc, hr⟩ => by
      have ih := SumAll_part Pr n r hr
      by_cases hp : p ≤ n
      · simp only [T.part, hp, ite_true]
        exact ⟨ih.1, ⟨hp, hpc⟩, ih.2⟩
      · simp only [T.part, hp, ite_false]
        exact ⟨⟨⟨by omega, hpc⟩, ih.1⟩, ih.2⟩

theorem SumAll_one_del (Pr : Nat → T → Prop) (t : T) (h : SumAll Pr t) :
    SumAll Pr (T.one_del t) := by
  match t, h with
  | .P 0 .Z _, h => exact h.2
  | .Z, h | .P (_ + 1) _ _, h | .P 0 (.P _ _ _) _, h => exact h

theorem SumAll_G1_self (n : Nat) : ∀ t : T, SumAll (fun p c => n ≤ p → c ∈ T.G1 n t) t
  | .Z => trivial
  | .P p c r => by
      refine ⟨fun hnp => by simp [T.G1, hnp], ?_⟩
      apply SumAll_mono _ _ _ r (SumAll_G1_self n r)
      intro q d h hnq
      have hd := h hnq
      by_cases hnp : n ≤ p <;> simp [T.G1, hnp, hd]

theorem G1_of_SumAll (u : Nat) (R : T → Prop) : ∀ t : T,
    SumAll (fun p c => u ≤ p → R c ∧ ∀ y ∈ T.G1 u c, R y) t → ∀ y ∈ T.G1 u t, R y
  | .Z, _, y, hy => by cases hy
  | .P p c r, ⟨hpc, hr⟩, y, hy => by
      by_cases hup : u ≤ p
      · simp only [T.G1, hup, ite_true, List.mem_append, List.mem_singleton] at hy
        rcases hy with (rfl | hy) | hy
        · exact (hpc hup).1
        · exact (hpc hup).2 y hy
        · exact G1_of_SumAll u R r hr y hy
      · simp only [T.G1, hup, ite_false] at hy
        exact G1_of_SumAll u R r hr y hy

theorem summand_le_head (K : Nat) (X : T) : ∀ t : T, T.isNF1 t → IsSummand K X t →
    T.P K X T.Z ≤ T.head t
  | .Z, _, h => h.elim
  | .P p a r, ht, h => by
      rcases h with ⟨rfl, rfl⟩ | h
      · exact Or.inr rfl
      · have hr := (T.isNF1_P_inv p a r ht).2.1
        have hhd := (T.isNF1_P_inv p a r ht).2.2.2
        exact partial_order.trans _ _ _ (summand_le_head K X r hr h) hhd

theorem summand_head_part2 (K : Nat) (X : T) : ∀ t : T, T.isNF1 t → IsSummand K X t →
    T.P K X T.Z ≤ T.head (T.part K t).2
  | .Z, _, h => h.elim
  | .P p a r, ht, h => by
      have hr := (T.isNF1_P_inv p a r ht).2.1
      have hhd := (T.isNF1_P_inv p a r ht).2.2.2
      by_cases hp : p ≤ K
      · simp only [T.part, hp, ite_true, T.head]
        rcases h with ⟨rfl, rfl⟩ | h
        · exact Or.inr rfl
        · exact partial_order.trans _ _ _ (summand_le_head K X r hr h) hhd
      · simp only [T.part, hp, ite_false]
        rcases h with ⟨rfl, _⟩ | h
        · exact False.elim (hp (Nat.le_refl _))
        · exact summand_head_part2 K X r hr h

/-- A principal argument is below the ambient term once its high part is controlled. -/
theorem summand_arg_lt (K : Nat) (X tv TS : T) (hTS : T.isNF1 TS) (hX : T.isNF1 X)
    (htv : T.isNF1 tv) (hsum : IsSummand K X TS) (hlt : tv < TS)
    (hhigh : (T.part K tv).1 = (T.part K X).1)
    (hlow : (T.part K X).2 < T.P K X T.Z) : X < TS := by
  rcases part_lt_cases K tv TS htv hTS hlt with h | ⟨he, _⟩
  · rw [hhigh] at h
    exact lt_of_part_lt_cases K X TS hX hTS (Or.inl h)
  · apply lt_of_part_lt_cases K X TS hX hTS (Or.inr ⟨hhigh ▸ he, ?_⟩)
    exact lt_of_lt_of_le_thm T _ _ _ hlow
      (partial_order.trans _ _ _ (summand_head_part2 K X TS hTS hsum) (head_le_self _))

theorem stand_G1_subset (u : Nat) : ∀ s x : T, x ∈ T.G1 u (T.stand s) → x ∈ T.G1 u s
  | .Z, x, hx => hx
  | .P a b c, x, hx => by
      rw [T.stand] at hx
      split at hx
      · by_cases hu : u ≤ a
        · simp only [T.G1, hu, ite_true, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (stand_G1_subset u c x hx)
        · simp only [T.G1, hu, ite_false] at hx ⊢
          exact stand_G1_subset u c x hx
      · have h := stand_G1_subset u c x hx
        by_cases hu : u ≤ a <;> simp [T.G1, hu, h]

theorem card_stand_G1_subset (n u : Nat) : ∀ s x : T,
    x ∈ T.G1 u (T.card_times n (T.stand s)) → x ∈ T.G1 u (T.card_times n s)
  | .Z, x, hx => hx
  | .P a b c, x, hx => by
      rw [T.stand] at hx
      split at hx
      · rw [card_times_P] at hx ⊢
        by_cases hu : u ≤ max a n
        · simp only [T.G1, hu, ite_true, List.mem_append] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (card_stand_G1_subset n u c x hx)
        · simp only [T.G1, hu, ite_false] at hx ⊢
          exact card_stand_G1_subset n u c x hx
      · have h := card_stand_G1_subset n u c x hx
        rw [card_times_P]
        by_cases hu : u ≤ max a n <;> simp [T.G1, hu, h]

theorem early_collapse_support_exact (u n : Nat) (s : T)
    (hun : u ≤ n) (hs : T.isNF1 s) :
    ∀ x : T, x ∈ T.G1 u (T.early_collapse n s) →
      x = (T.part n s).1 ∨ x ∈ T.G1 u s := by
  intro x hx
  rcases hp : T.part n s with ⟨a, b⟩
  have hb : T.isNF1 b := by
    simpa [hp] using (part_NF n s hs).2
  have hmem : ∀ y : T, y ∈ T.G1 u a ++ T.G1 u b → y ∈ T.G1 u s := by
    intro y hy
    rw [← part_add n s hs, hp, G1_add]
    exact hy
  simp only [T.early_collapse, hp] at hx
  split at hx
  · exact Or.inr (hmem x (List.mem_append_right _ hx))
  · rw [T.stand, stand_eq_self b hb] at hx
    split at hx
    · simp only [T.G1, hun, ite_true, List.mem_append, List.mem_singleton] at hx
      rcases hx with (rfl | hx) | hx
      · exact Or.inl rfl
      · exact Or.inr (hmem x (List.mem_append_left _ hx))
      · exact Or.inr (hmem x (List.mem_append_right _ hx))
    · exact Or.inr (hmem x (List.mem_append_right _ hx))

theorem early_collapse_le_wrap (n : Nat) (a : T) (ha : T.isNF1 a)
    (hg : ∀ x ∈ T.G1 n a, x < a) :
    T.early_collapse n a ≤ T.P n a T.Z := by
  have hlow := part_snd_lt_wrap n a T.Z ha hg
  dsimp only [T.early_collapse]
  split
  · exact Or.inl hlow
  · rw [T.stand, stand_eq_self _ (part_NF n a ha).2]
    split
    · have he := part_add n a ha
      cases hb : (T.part n a).2 with
      | Z => rw [hb, T.add_Z] at he; rw [he]; exact Or.inr rfl
      | P q d e =>
          refine Or.inl (T.Lt.p_mid _ _ _ _ _ ?_)
          have hlt := add_lt_add_of_ne_Z (T.part n a).1 (T.part n a).2 (by rw [hb]; intro h; cases h)
          rwa [he] at hlt
    · exact Or.inl hlow

theorem cardArg_le_head (n p : Nat) (a b : T) (hs : T.isNF1 (T.P p a b))
    (hcase : p < n ∨ (p = n ∧ a < T.P n (T.P 0 T.Z T.Z) T.Z)) :
    cardArg n p a ≤ T.P p a T.Z := by
  obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv p a b hs
  rcases hcase with hpn | ⟨rfl, hlt⟩
  · by_cases hp : p = 0
    · subst p
      simp only [cardArg, hpn, ite_true]
      exact early_collapse_le_wrap 0 a ha hga
    · simp only [cardArg, hpn, hp, ite_true, ite_false]
      have he := early_collapse_closed p a ha hga
      rw [T.stand, stand_eq_self _ he.1]
      split
      · cases a with
        | Z => exact Or.inr (by simp [T.early_collapse, T.part])
        | P q d e => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))
      · exact early_collapse_le_wrap p a ha hga
  · simp only [cardArg, Nat.lt_irrefl, hlt, and_self, ite_true, ite_false]
    cases a with
    | Z => exact Or.inr rfl
    | P q d e => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))

/-- Hypotheses on a summand `P p c _` used to bound the supports of cardinal products. -/
def CardCond (n u : Nat) (R : T → Prop) (p : Nat) (c : T) : Prop :=
  (n ≤ p → R c) ∧ (u ≤ p → ∀ y ∈ T.G1 u c, R y) ∧ (u ≤ p → p < n → R (T.part p c).1)

theorem card_times_support_bounded (n u : Nat) (hun : u ≤ n) (R : T → Prop)
    (hR : ∀ x y : T, x ≤ y → R y → R x) :
    ∀ s : T, T.isNF1 s → R s → SumAll (CardCond n u R) s →
      ∀ y ∈ T.G1 u (T.card_times n s), R y := by
  intro s hs
  induction hs with
  | z => intro _ _ y hy; cases hy
  | p p a b ha hb hga hh _ ihb =>
      intro hRs hsum y hy
      have hsfull : T.isNF1 (T.P p a b) := .p p a b ha hb hga hh
      obtain ⟨⟨hc1, hc2, hc3⟩, hsb⟩ := hsum
      have hRZ : R T.Z := hR _ _ (T.Z_le _) hRs
      have hRhead : R (T.P p a T.Z) := hR _ _ (head_le_self (T.P p a b)) hRs
      have hRb : R b := hR _ _ (T.isNF1_tail_le _ hsfull p a b rfl) hRs
      rw [card_times_P] at hy
      have hum : u ≤ max p n := Nat.le_trans hun (Nat.le_max_right p n)
      simp only [T.G1, hum, ite_true, List.mem_append, List.mem_singleton] at hy
      rcases hy with (rfl | hy) | hy
      · by_cases hcase : p < n ∨ (p = n ∧ a < T.P n (T.P 0 T.Z T.Z) T.Z)
        · exact hR _ _ (cardArg_le_head n p a b hsfull hcase) hRhead
        · rw [show cardArg n p a = a by
            unfold cardArg
            rw [ite_eq_right (fun h => hcase (Or.inl h)), ite_eq_right (fun h => hcase (Or.inr h))]]
          exact hc1 (Nat.le_of_not_gt fun h => hcase (Or.inl h))
      · by_cases hpn : p < n
        · by_cases hp : p = 0
          · subst p
            simp only [cardArg, hpn, ite_true] at hy
            by_cases hu0 : u = 0
            · subst u
              rcases early_collapse_support_exact 0 0 a (Nat.le_refl 0) ha y hy with h | h
              · rw [h]; exact hc3 (Nat.le_refl 0) hpn
              · exact hc2 (Nat.le_refl 0) y h
            · have hi := (early_collapse_closed 0 a ha hga).2
              rw [index_Prop1_G1_empty 0 _ hi u (Nat.pos_of_ne_zero hu0)] at hy
              cases hy
          · simp only [cardArg, hpn, hp, ite_true, ite_false] at hy
            have hy' := stand_G1_subset u _ y hy
            by_cases hup : u ≤ p
            · simp only [T.G1, hup, ite_true, List.mem_append, List.mem_singleton,
                List.not_mem_nil, or_false] at hy'
              rcases hy' with rfl | hy'
              · exact hRZ
              · rcases early_collapse_support_exact u p a hup ha y hy' with h | h
                · rw [h]; exact hc3 hup hpn
                · exact hc2 hup y h
            · simp only [T.G1, hup, ite_false] at hy'
              have hi := (early_collapse_closed p a ha hga).2
              rw [index_Prop1_G1_empty p _ hi u (by omega)] at hy'
              cases hy'
        · by_cases hcase : p = n ∧ a < T.P n (T.P 0 T.Z T.Z) T.Z
          · obtain ⟨rfl, hlt⟩ := hcase
            simp only [cardArg, Nat.lt_irrefl, hlt, and_self, ite_true, ite_false] at hy
            simp only [T.G1, hun, ite_true, List.mem_append, List.mem_singleton,
              List.not_mem_nil, or_false] at hy
            rcases hy with rfl | hy
            · exact hRZ
            · exact hc2 hun y hy
          · rw [show cardArg n p a = a by unfold cardArg; rw [ite_eq_right hpn, ite_eq_right hcase]]
              at hy
            exact hc2 (Nat.le_trans hun (Nat.le_of_not_gt hpn)) y hy
      · exact ihb hRb hsb y hy

theorem early_card_support_bounded (n u : Nat) (hun : u ≤ n) (R : T → Prop)
    (hR : ∀ x y : T, x ≤ y → R y → R x) (t : T) (ht : T.isNF1 t) (hRt : R t)
    (hsum : SumAll (CardCond n u R) t) :
    ∀ y ∈ T.G1 u (T.card_times n (T.early_collapse n t)), R y := by
  have hpart := SumAll_part _ n t hsum
  have hLNF := (part_NF n t ht).2
  have hHNF := (part_NF n t ht).1
  have hRL : R (T.part n t).2 := by
    apply hR _ _ _ hRt
    have h := add_right_le_of_NF (T.part n t).1 (T.part n t).2 (by rw [part_add n t ht]; exact ht)
    rwa [part_add n t ht] at h
  have hLsum : SumAll (CardCond n u R) (T.part n t).2 :=
    SumAll_mono _ _ (fun _ _ h => h.2) _ hpart.2
  have hLsup := card_times_support_bounded n u hun R hR _ hLNF hRL hLsum
  dsimp only [T.early_collapse]
  split
  · exact hLsup
  · rename_i hne
    intro y hy
    have hy' := card_stand_G1_subset n u _ y hy
    rw [card_times_P, Nat.max_self] at hy'
    have hca : cardArg n n (T.part n t).1 = (T.part n t).1 := by
      cases hH : (T.part n t).1 with
      | Z => exact False.elim (hne hH)
      | P q d e =>
          unfold cardArg
          rw [ite_eq_right (Nat.lt_irrefl n), ite_eq_right fun ⟨_, hlt⟩ =>
            lt_asymm_thm hlt (T.Lt.p_head _ _ _ _ _ _ (part_first_head_gt n q t d e hH))]
    rw [hca] at hy'
    simp only [T.G1, hun, ite_true, List.mem_append, List.mem_singleton] at hy'
    rcases hy' with (rfl | hy') | hy'
    · exact hR _ _ (part_first_le n t ht) hRt
    · apply G1_of_SumAll u R _ _ y hy'
      apply SumAll_mono _ _ _ _ hpart.1
      intro p c ⟨hnp, hc1, hc2, _⟩ hup
      exact ⟨hc1 (Nat.le_of_lt hnp), hc2 hup⟩
    · exact hLsup y hy'

end LegacyTranslation
