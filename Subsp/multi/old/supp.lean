import Subsp.multi.old.alg

/-! Supports of collapsed and multiplied Buchholz terms: upper bounds (`SumAll`, `CardCond`)
and domination of the supports of the inputs (`DomBy`). -/

namespace OB

open T

/-- Every summand `P p c _` of a term satisfies `Pr p c`. -/
def SumAll (Pr : Nat → T → Prop) : T → Prop
  | Z => True
  | P p c r => Pr p c ∧ SumAll Pr r

/-- `P p c _` occurs as a summand of a term. -/
def IsSummand (p : Nat) (c : T) : T → Prop
  | Z => False
  | P q a r => (q = p ∧ a = c) ∨ IsSummand p c r

theorem SumAll_mono (Pr Qr : Nat → T → Prop) (h : ∀ p c, Pr p c → Qr p c) :
    ∀ t, SumAll Pr t → SumAll Qr t
  | Z, _ => trivial
  | P p c r, ⟨hpc, hr⟩ => ⟨h p c hpc, SumAll_mono Pr Qr h r hr⟩

theorem SumAll_of_summand (Pr : Nat → T → Prop) :
    ∀ t, (∀ p c, IsSummand p c t → Pr p c) → SumAll Pr t
  | Z, _ => trivial
  | P q a r, h => ⟨h q a (Or.inl ⟨rfl, rfl⟩),
      SumAll_of_summand Pr r (fun p c hs => h p c (Or.inr hs))⟩

theorem SumAll_and3 (P1 P2 P3 : Nat → T → Prop) :
    ∀ t, SumAll P1 t → SumAll P2 t → SumAll P3 t →
      SumAll (fun p c => P1 p c ∧ P2 p c ∧ P3 p c) t
  | Z, _, _, _ => trivial
  | P _ _ r, ⟨h1, r1⟩, ⟨h2, r2⟩, ⟨h3, r3⟩ => ⟨⟨h1, h2, h3⟩, SumAll_and3 P1 P2 P3 r r1 r2 r3⟩

theorem SumAll_part (Pr : Nat → T → Prop) (n : Nat) : ∀ t, SumAll Pr t →
    SumAll (fun p c => n < p ∧ Pr p c) (part n t).1 ∧
      SumAll (fun p c => p ≤ n ∧ Pr p c) (part n t).2
  | Z, _ => ⟨trivial, trivial⟩
  | P p c r, ⟨hpc, hr⟩ => by
    have ih := SumAll_part Pr n r hr
    by_cases hp : p ≤ n
    · rw [part_P_le c r hp]
      exact ⟨ih.1, ⟨hp, hpc⟩, ih.2⟩
    · rw [part_P_gt c r hp]
      exact ⟨⟨⟨Nat.lt_of_not_le hp, hpc⟩, ih.1⟩, ih.2⟩

theorem SumAll_oneDel (Pr : Nat → T → Prop) (t : T) (h : SumAll Pr t) : SumAll Pr (oneDel t) := by
  rcases oneDel_cases t with he | ⟨b, rfl, he⟩
  · rw [he]; exact h
  · rw [he]; exact h.2

theorem SumAll_G1_self (n : Nat) : ∀ t : T, SumAll (fun p c => n ≤ p → c ∈ T.G1 n t) t
  | Z => trivial
  | P p c r => by
    refine ⟨fun hnp => (MT.G1_P_mem hnp).2 (Or.inl rfl), ?_⟩
    apply SumAll_mono _ _ _ r (SumAll_G1_self n r)
    intro q d h hnq
    have hd := h hnq
    by_cases hnp : n ≤ p
    · exact (MT.G1_P_mem hnp).2 (Or.inr (Or.inr hd))
    · rw [T.G1, ite_eq_right hnp]; exact hd

theorem G1_of_SumAll (u : Nat) (R : T → Prop) : ∀ t : T,
    SumAll (fun p c => u ≤ p → R c ∧ ∀ y ∈ T.G1 u c, R y) t → ∀ y ∈ T.G1 u t, R y
  | Z, _, y, hy => by cases hy
  | P p c r, ⟨hpc, hr⟩, y, hy => by
    by_cases hup : u ≤ p
    · rcases (MT.G1_P_mem hup).1 hy with rfl | hy | hy
      · exact (hpc hup).1
      · exact (hpc hup).2 y hy
      · exact G1_of_SumAll u R r hr y hy
    · rw [T.G1, ite_eq_right hup] at hy
      exact G1_of_SumAll u R r hr y hy

theorem summand_le_head (K : Nat) (X : T) : ∀ t : T, T.isNF1 t → IsSummand K X t →
    P K X Z ≤ T.head t
  | Z, _, h => h.elim
  | P p a r, ht, h => by
    rcases h with ⟨rfl, rfl⟩ | h
    · exact Or.inr rfl
    · have hr := (T.isNF1_P_inv p a r ht).2.1
      have hhd := (T.isNF1_P_inv p a r ht).2.2.2
      exact partial_order.trans _ _ _ (summand_le_head K X r hr h) hhd

theorem summand_head_part2 (K : Nat) (X : T) : ∀ t : T, T.isNF1 t → IsSummand K X t →
    P K X Z ≤ T.head (part K t).2
  | Z, _, h => h.elim
  | P p a r, ht, h => by
    have hr := (T.isNF1_P_inv p a r ht).2.1
    have hhd := (T.isNF1_P_inv p a r ht).2.2.2
    by_cases hp : p ≤ K
    · rw [part_P_le a r hp]
      show P K X Z ≤ P p a Z
      rcases h with ⟨rfl, rfl⟩ | h
      · exact Or.inr rfl
      · exact partial_order.trans _ _ _ (summand_le_head K X r hr h) hhd
    · rw [part_P_gt a r hp]
      rcases h with ⟨rfl, _⟩ | h
      · exact absurd (Nat.le_refl _) hp
      · exact summand_head_part2 K X r hr h

/-- A principal argument is below the ambient term once its high part is controlled. -/
theorem summand_arg_lt (K : Nat) (X tv TS : T) (hTS : T.isNF1 TS) (hX : T.isNF1 X)
    (htv : T.isNF1 tv) (hsum : IsSummand K X TS) (hlt : tv < TS)
    (hhigh : (part K tv).1 = (part K X).1) (hlow : (part K X).2 < P K X Z) : X < TS := by
  rcases part_lt_cases K tv TS htv hTS hlt with h | ⟨he, _⟩
  · rw [hhigh] at h
    exact lt_of_part_lt_cases K X TS hX hTS (Or.inl h)
  · apply lt_of_part_lt_cases K X TS hX hTS (Or.inr ⟨hhigh ▸ he, ?_⟩)
    exact lt_of_lt_of_le_thm T _ _ _ hlow
      (partial_order.trans _ _ _ (summand_head_part2 K X TS hTS hsum) (MT.head_le_self _))

theorem stand_G1_subset (u : Nat) : ∀ s x : T, x ∈ T.G1 u (MT.stand s) → x ∈ T.G1 u s
  | Z, x, hx => hx
  | P a b c, x, hx => by
    rw [MT.stand] at hx
    by_cases hh : T.head (MT.stand c) ≤ P a b Z
    · rw [ite_eq_left hh] at hx
      by_cases hu : u ≤ a
      · rcases (MT.G1_P_mem hu).1 hx with rfl | hx | hx
        · exact (MT.G1_P_mem hu).2 (Or.inl rfl)
        · exact (MT.G1_P_mem hu).2 (Or.inr (Or.inl hx))
        · exact (MT.G1_P_mem hu).2 (Or.inr (Or.inr (stand_G1_subset u c x hx)))
      · rw [T.G1, ite_eq_right hu] at hx ⊢
        exact stand_G1_subset u c x hx
    · rw [ite_eq_right hh] at hx
      have h := stand_G1_subset u c x hx
      by_cases hu : u ≤ a
      · exact (MT.G1_P_mem hu).2 (Or.inr (Or.inr h))
      · rw [T.G1, ite_eq_right hu]; exact h

theorem G1_ct_P_mem {n u p : Nat} {a b x : T} (hx : x ∈ T.G1 u (ct n b)) :
    x ∈ T.G1 u (ct n (P p a b)) := by
  rw [ct_P]
  by_cases hu : u ≤ max p n
  · exact (MT.G1_P_mem hu).2 (Or.inr (Or.inr hx))
  · rw [T.G1, ite_eq_right hu]; exact hx

theorem card_stand_G1_subset (n u : Nat) : ∀ s x : T,
    x ∈ T.G1 u (ct n (MT.stand s)) → x ∈ T.G1 u (ct n s)
  | Z, x, hx => hx
  | P a b c, x, hx => by
    rw [MT.stand] at hx
    by_cases hh : T.head (MT.stand c) ≤ P a b Z
    · rw [ite_eq_left hh, ct_P] at hx
      rw [ct_P]
      by_cases hu : u ≤ max a n
      · rcases (MT.G1_P_mem hu).1 hx with rfl | hx | hx
        · exact (MT.G1_P_mem hu).2 (Or.inl rfl)
        · exact (MT.G1_P_mem hu).2 (Or.inr (Or.inl hx))
        · exact (MT.G1_P_mem hu).2 (Or.inr (Or.inr (card_stand_G1_subset n u c x hx)))
      · rw [T.G1, ite_eq_right hu] at hx ⊢
        exact card_stand_G1_subset n u c x hx
    · rw [ite_eq_right hh] at hx
      exact G1_ct_P_mem (card_stand_G1_subset n u c x hx)

theorem G1_part_fst_subset (u n : Nat) (s : T) (hs : T.isNF1 s) :
    ∀ x ∈ T.G1 u (part n s).1, x ∈ T.G1 u s := by
  intro x hx
  rw [← part_add n s hs, MT.G1_add]
  exact List.mem_append_left _ hx

theorem G1_part_snd_subset (u n : Nat) (s : T) (hs : T.isNF1 s) :
    ∀ x ∈ T.G1 u (part n s).2, x ∈ T.G1 u s := by
  intro x hx
  rw [← part_add n s hs, MT.G1_add]
  exact List.mem_append_right _ hx

theorem ec_support_exact (u n : Nat) (s : T) (hun : u ≤ n) (hs : T.isNF1 s) :
    ∀ x : T, x ∈ T.G1 u (ec n s) → x = (part n s).1 ∨ x ∈ T.G1 u s := by
  intro x hx
  have hb := (part_NF n s hs).2
  rw [ec] at hx
  by_cases hz : (part n s).1 = Z
  · rw [ite_eq_left hz] at hx
    exact Or.inr (G1_part_snd_subset u n s hs x hx)
  · rw [ite_eq_right hz, MT.stand, MT.stand_of_NF1 hb] at hx
    by_cases hh : T.head (part n s).2 ≤ P n (part n s).1 Z
    · rw [ite_eq_left hh] at hx
      rcases (MT.G1_P_mem hun).1 hx with rfl | hx | hx
      · exact Or.inl rfl
      · exact Or.inr (G1_part_fst_subset u n s hs x hx)
      · exact Or.inr (G1_part_snd_subset u n s hs x hx)
    · rw [ite_eq_right hh] at hx
      exact Or.inr (G1_part_snd_subset u n s hs x hx)

theorem ec_le_wrap (n : Nat) (a : T) (ha : T.isNF1 a) (hg : ∀ x ∈ T.G1 n a, x < a) :
    ec n a ≤ P n a Z := by
  have hlow := part_snd_lt_wrap n a Z ha hg
  rw [ec]
  by_cases hz : (part n a).1 = Z
  · rw [ite_eq_left hz]; exact Or.inl hlow
  · rw [ite_eq_right hz, MT.stand, MT.stand_of_NF1 (part_NF n a ha).2]
    by_cases hh : T.head (part n a).2 ≤ P n (part n a).1 Z
    · rw [ite_eq_left hh]
      have he := part_add n a ha
      cases hb : (part n a).2 with
      | Z => rw [hb, T.add_Z] at he; rw [he]; exact Or.inr rfl
      | P q d e =>
        refine Or.inl (T.Lt.p_mid _ _ _ _ _ ?_)
        have hlt := add_lt_add_of_ne_Z (part n a).1 (part n a).2 (by rw [hb]; intro h; cases h)
        rwa [he] at hlt
    · rw [ite_eq_right hh]; exact Or.inl hlow

theorem cardArg_le_head (n p : Nat) (a b : T) (hs : T.isNF1 (P p a b))
    (hcase : p < n ∨ (p = n ∧ a < P n (P 0 Z Z) Z)) : cardArg n p a ≤ P p a Z := by
  obtain ⟨ha, _, hga, _⟩ := T.isNF1_P_inv p a b hs
  rcases hcase with hpn | ⟨rfl, hlt⟩
  · rw [cardArg_lt_case n p a hpn]
    by_cases hp : p = 0
    · rw [ite_eq_left hp]
      exact ec_le_wrap p a ha hga
    · rw [ite_eq_right hp]
      have he := ec_closed p a ha hga
      rw [MT.stand, MT.stand_of_NF1 he.1]
      by_cases hh : T.head (ec p a) ≤ P p Z Z
      · rw [ite_eq_left hh]
        cases a with
        | Z =>
          refine Or.inr ?_
          show P p Z (ec p Z) = P p Z Z
          rfl
        | P q d e => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))
      · rw [ite_eq_right hh]; exact ec_le_wrap p a ha hga
  · rw [cardArg_same_small p a hlt]
    cases a with
    | Z => exact Or.inr rfl
    | P q d e => exact Or.inl (T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _))

/-- Hypotheses on a summand `P p c _` used to bound the supports of cardinal products. -/
def CardCond (n u : Nat) (R : T → Prop) (p : Nat) (c : T) : Prop :=
  (n ≤ p → R c) ∧ (u ≤ p → ∀ y ∈ T.G1 u c, R y) ∧ (u ≤ p → p < n → R (part p c).1)

theorem ct_support_bounded (n u : Nat) (hun : u ≤ n) (R : T → Prop)
    (hR : ∀ x y : T, x ≤ y → R y → R x) :
    ∀ s : T, T.isNF1 s → R s → SumAll (CardCond n u R) s → ∀ y ∈ T.G1 u (ct n s), R y := by
  intro s hs
  induction hs with
  | z => intro _ _ y hy; cases hy
  | p p a b ha hb hga hh _ ihb =>
    intro hRs hsum y hy
    have hsfull : T.isNF1 (P p a b) := T.isNF1.p p a b ha hb hga hh
    obtain ⟨⟨hc1, hc2, hc3⟩, hsb⟩ := hsum
    have hRZ : R Z := hR _ _ (T.Z_le _) hRs
    have hRhead : R (P p a Z) := hR _ _ (MT.head_le_self (P p a b)) hRs
    have hRb : R b := hR _ _ (T.isNF1_tail_le _ hsfull p a b rfl) hRs
    rw [ct_P] at hy
    have hum : u ≤ max p n := Nat.le_trans hun (Nat.le_max_right p n)
    rcases (MT.G1_P_mem hum).1 hy with rfl | hy | hy
    · by_cases hcase : p < n ∨ (p = n ∧ a < P n (P 0 Z Z) Z)
      · exact hR _ _ (cardArg_le_head n p a b hsfull hcase) hRhead
      · have hpn : ¬ p < n := fun h => hcase (Or.inl h)
        rw [cardArg_eq_self n p a hpn (fun h => hcase (Or.inr h))]
        exact hc1 (Nat.le_of_not_gt hpn)
    · by_cases hpn : p < n
      · rw [cardArg_lt_case n p a hpn] at hy
        by_cases hp : p = 0
        · rw [ite_eq_left hp] at hy
          subst hp
          by_cases hu0 : u = 0
          · subst hu0
            rcases ec_support_exact 0 0 a (Nat.le_refl 0) ha y hy with h | h
            · rw [h]; exact hc3 (Nat.le_refl 0) hpn
            · exact hc2 (Nat.le_refl 0) y h
          · have hi := (ec_closed 0 a ha hga).2
            rw [index_Prop1_G1_empty 0 _ hi u (Nat.pos_of_ne_zero hu0)] at hy
            cases hy
        · rw [ite_eq_right hp] at hy
          have hy' := stand_G1_subset u _ y hy
          by_cases hup : u ≤ p
          · rcases (MT.G1_P_mem hup).1 hy' with rfl | hy' | hy'
            · exact hRZ
            · cases hy'
            · rcases ec_support_exact u p a hup ha y hy' with h | h
              · rw [h]; exact hc3 hup hpn
              · exact hc2 hup y h
          · rw [T.G1, ite_eq_right hup] at hy'
            have hi := (ec_closed p a ha hga).2
            rw [index_Prop1_G1_empty p _ hi u (Nat.lt_of_not_le hup)] at hy'
            cases hy'
      · by_cases hcase : p = n ∧ a < P n (P 0 Z Z) Z
        · obtain ⟨rfl, hlt⟩ := hcase
          rw [cardArg_same_small p a hlt] at hy
          rcases (MT.G1_P_mem hun).1 hy with rfl | hy | hy
          · exact hRZ
          · cases hy
          · exact hc2 hun y hy
        · rw [cardArg_eq_self n p a hpn hcase] at hy
          exact hc2 (Nat.le_trans hun (Nat.le_of_not_gt hpn)) y hy
    · exact ihb hRb hsb y hy

theorem early_card_support_bounded (n u : Nat) (hun : u ≤ n) (R : T → Prop)
    (hR : ∀ x y : T, x ≤ y → R y → R x) (t : T) (ht : T.isNF1 t) (hRt : R t)
    (hsum : SumAll (CardCond n u R) t) : ∀ y ∈ T.G1 u (ct n (ec n t)), R y := by
  have hpart := SumAll_part _ n t hsum
  have hLNF := (part_NF n t ht).2
  have hRL : R (part n t).2 := by
    apply hR _ _ _ hRt
    have h := add_right_le_of_NF (part n t).1 (part n t).2 (by rw [part_add n t ht]; exact ht)
    rwa [part_add n t ht] at h
  have hLsum : SumAll (CardCond n u R) (part n t).2 :=
    SumAll_mono _ _ (fun _ _ h => h.2) _ hpart.2
  have hLsup := ct_support_bounded n u hun R hR _ hLNF hRL hLsum
  rw [ec]
  by_cases hne : (part n t).1 = Z
  · rw [ite_eq_left hne]; exact hLsup
  · rw [ite_eq_right hne]
    intro y hy
    have hy' := card_stand_G1_subset n u _ y hy
    rw [ct_P, Nat.max_self] at hy'
    have hca : cardArg n n (part n t).1 = (part n t).1 := by
      cases hH : (part n t).1 with
      | Z => exact absurd hH hne
      | P q d e =>
        apply cardArg_eq_self n n _ (Nat.lt_irrefl n)
        intro ⟨_, hlt⟩
        exact lt_asymm_thm hlt (T.Lt.p_head _ _ _ _ _ _ (part_first_head_gt n q t d e hH))
    rw [hca] at hy'
    rcases (MT.G1_P_mem hun).1 hy' with rfl | hy' | hy'
    · exact hR _ _ (part_first_le n t ht) hRt
    · apply G1_of_SumAll u R _ _ y hy'
      apply SumAll_mono _ _ _ _ hpart.1
      intro p c ⟨hnp, hc1, hc2, _⟩ hup
      exact ⟨hc1 (Nat.le_of_lt hnp), hc2 hup⟩
    · exact hLsup y hy'

/-! ### Domination of supports -/

/-- `y` is dominated by some element of `l`. -/
def DomBy (l : List T) (y : T) : Prop := ∃ v ∈ l, y ≤ v

theorem DomBy_of_mem (l : List T) (y : T) (h : y ∈ l) : DomBy l y := ⟨y, h, Or.inr rfl⟩

theorem DomBy_mono (l l' : List T) (h : ∀ v ∈ l, v ∈ l') (y : T) (hy : DomBy l y) :
    DomBy l' y := by
  obtain ⟨v, hv, hyv⟩ := hy
  exact ⟨v, h v hv, hyv⟩

theorem DomBy_trans (l l' : List T) (h : ∀ v ∈ l, DomBy l' v) (y : T) (hy : DomBy l y) :
    DomBy l' y := by
  obtain ⟨v, hv, hyv⟩ := hy
  obtain ⟨w, hw, hvw⟩ := h v hv
  exact ⟨w, hw, partial_order.trans _ _ _ hyv hvw⟩

/-- The high part of an argument below a sum is a prefix of it. -/
theorem part_fst_of_between (K : Nat) (H L d : T) (hH : T.isNF1 H) (hd : T.isNF1 d)
    (hHL : T.isNF1 (T.add H L)) (hHfix : part K H = (H, Z)) (hLlow : (part K L).1 = Z)
    (h1 : H < d) (h2 : d < T.add H L) : (part K d).1 = H := by
  have hpHL : (part K (T.add H L)).1 = H := by
    rw [part_add_distrib, hHfix, hLlow, T.add_Z]
  rcases part_lt_cases K H d hH hd h1 with h | ⟨he, _⟩
  · rw [hHfix] at h
    rcases part_lt_cases K d (T.add H L) hd hHL h2 with h' | ⟨he', _⟩
    · rw [hpHL] at h'
      exact absurd h' (lt_asymm_thm h)
    · rw [hpHL] at he'
      exact he'
  · rw [hHfix] at he
    exact he.symm

/-- If the high part does not dominate the low part, the low part starts with `P K d _`, where
`d` exceeds the high part and (for good terms) has the same high part. -/
theorem low_head_of_not_le (K : Nat) (t : T) (ht : T.isNF1 t)
    (hnot : ¬ T.head (part K t).2 ≤ P K (part K t).1 Z) :
    ∃ d r, (part K t).2 = P K d r ∧ (part K t).1 < d ∧ T.isNF1 d ∧
      ((∀ y ∈ T.G1 K t, y < t) → (part K d).1 = (part K t).1) := by
  have he := part_add K t ht
  have hLNF := (part_NF K t ht).2
  have hi := part_second_index K t
  cases hL : (part K t).2 with
  | Z => rw [hL] at hnot; exact absurd (T.Z_le _) hnot
  | P q d r =>
    rw [hL] at hi hLNF hnot
    change ¬ P q d Z ≤ P K (part K t).1 Z at hnot
    cases hi with
    | p _ _ _ hq _ =>
      have hqK : q = K := by
        rcases Nat.eq_or_lt_of_le hq with h | h
        · exact h
        · exact absurd (Or.inl (T.Lt.p_head _ _ _ _ _ _ h)) hnot
      subst q
      have hdH : (part K t).1 < d := by
        rcases lt_total_thm (part K t).1 d with h | h | h
        · exact h
        · exact absurd (Or.inl (T.Lt.p_mid _ _ _ _ _ h)) hnot
        · exact absurd (Or.inr (by rw [h])) hnot
      have hdNF := (T.isNF1_P_inv K d r hLNF).1
      refine ⟨d, r, rfl, hdH, hdNF, fun hg => ?_⟩
      have hdt : d < t := by
        apply hg d
        rw [← he, MT.G1_add, hL]
        exact List.mem_append_right _ ((MT.G1_P_mem (Nat.le_refl K)).2 (Or.inl rfl))
      apply part_fst_of_between K _ _ d (part_NF K t ht).1 hdNF (by rw [he]; exact ht)
        (part_first_fixed K t) (by rw [part_of_index K _ (part_second_index K t)]) hdH
      rw [he]; exact hdt

/-- Supports of a term are dominated by supports of its collapse. -/
theorem G1_dom_ec (K u : Nat) (huK : u ≤ K) (X : T) (hX : T.isNF1 X)
    (hg : ∀ y ∈ T.G1 K X, y < X) : ∀ y ∈ T.G1 u X, DomBy (T.G1 u (ec K X)) y := by
  intro y hy
  have he := part_add K X hX
  have hLNF := (part_NF K X hX).2
  rw [← he, MT.G1_add, List.mem_append] at hy
  rw [ec]
  by_cases hz : (part K X).1 = Z
  · rw [ite_eq_left hz]
    rcases hy with hy | hy
    · rw [hz] at hy; cases hy
    · exact DomBy_of_mem _ _ hy
  · rw [ite_eq_right hz, MT.stand, MT.stand_of_NF1 hLNF]
    by_cases hh : T.head (part K X).2 ≤ P K (part K X).1 Z
    · rw [ite_eq_left hh]
      apply DomBy_of_mem
      rcases hy with hy | hy
      · exact (MT.G1_P_mem huK).2 (Or.inr (Or.inl hy))
      · exact (MT.G1_P_mem huK).2 (Or.inr (Or.inr hy))
    · rw [ite_eq_right hh]
      rcases hy with hy | hy
      · obtain ⟨d, r, hL, -, hdNF, hpd⟩ := low_head_of_not_le K X hX hh
        refine ⟨y, ?_, Or.inr rfl⟩
        rw [hL]
        refine (MT.G1_P_mem huK).2 (Or.inr (Or.inl ?_))
        rw [← part_add K d hdNF, MT.G1_add, hpd hg]
        exact List.mem_append_left _ hy
      · exact DomBy_of_mem _ _ hy

theorem high_lt_low_head (K : Nat) (H : T) (hH : part K H = (H, Z)) (hne : H ≠ Z) :
    ¬ H < P K (P 0 Z Z) Z := by
  cases H with
  | Z => exact absurd rfl hne
  | P q d e =>
    have hq := part_first_head_gt K q (P q d e) d e (by rw [hH])
    intro h
    exact lt_asymm_thm h (T.Lt.p_head _ _ _ _ _ _ hq)

theorem cardArg_self_high (n : Nat) (H d : T) (hH : part n H = (H, Z)) (hne : H ≠ Z)
    (hd : H ≤ d) : cardArg n n d = d := by
  apply cardArg_eq_self n n d (Nat.lt_irrefl n)
  intro ⟨_, hlt⟩
  exact high_lt_low_head n H hH hne (lt_of_le_of_lt_thm T _ _ _ hd hlt)

theorem G1_mem_P_self {u p : Nat} (hup : u ≤ p) (c d : T) : c ∈ T.G1 u (P p c d) :=
  (MT.G1_P_mem hup).2 (Or.inl rfl)

/-- The high part of a good term is dominated by supports of its collapse. -/
theorem high_dom_ec (u : Nat) (t : T) (ht : T.isNF1 t) (hH : (part u t).1 ≠ Z) :
    DomBy (T.G1 u (ec u t)) (part u t).1 ∧ DomBy (T.G1 u (ct u (ec u t))) (part u t).1 := by
  have hLNF := (part_NF u t ht).2
  have hfix := part_first_fixed u t
  rw [ec, ite_eq_right hH, MT.stand, MT.stand_of_NF1 hLNF]
  by_cases hh : T.head (part u t).2 ≤ P u (part u t).1 Z
  · rw [ite_eq_left hh, ct_P, Nat.max_self, cardArg_self_high u _ _ hfix hH (Or.inr rfl)]
    exact ⟨DomBy_of_mem _ _ (G1_mem_P_self (Nat.le_refl u) _ _),
      DomBy_of_mem _ _ (G1_mem_P_self (Nat.le_refl u) _ _)⟩
  · rw [ite_eq_right hh]
    obtain ⟨d, r, hL, hdH, -, -⟩ := low_head_of_not_le u t ht hh
    rw [hL, ct_P, Nat.max_self, cardArg_self_high u _ d hfix hH (Or.inl hdH)]
    exact ⟨⟨d, G1_mem_P_self (Nat.le_refl u) _ _, Or.inl hdH⟩,
      ⟨d, G1_mem_P_self (Nat.le_refl u) _ _, Or.inl hdH⟩⟩

theorem G1_stand_insert_supset (u K : Nat) (e : T) (he : T.isNF1 e) :
    ∀ y ∈ T.G1 u e, y ∈ T.G1 u (MT.stand (P K Z e)) := by
  intro y hy
  rw [MT.stand, MT.stand_of_NF1 he]
  by_cases hh : T.head e ≤ P K Z Z
  · rw [ite_eq_left hh]
    by_cases hu : u ≤ K
    · exact (MT.G1_P_mem hu).2 (Or.inr (Or.inr hy))
    · rw [T.G1, ite_eq_right hu]; exact hy
  · rw [ite_eq_right hh]; exact hy

theorem IsSummand_of_part (n K : Nat) (X : T) : ∀ t : T, IsSummand K X t →
    (n < K ∧ IsSummand K X (part n t).1) ∨ (K ≤ n ∧ IsSummand K X (part n t).2)
  | Z, h => h.elim
  | P p a r, h => by
    by_cases hp : p ≤ n
    · rw [part_P_le a r hp]
      rcases h with ⟨rfl, rfl⟩ | h
      · exact Or.inr ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
      · rcases IsSummand_of_part n K X r h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, Or.inr h2⟩
    · rw [part_P_gt a r hp]
      rcases h with ⟨rfl, rfl⟩ | h
      · exact Or.inl ⟨Nat.lt_of_not_le hp, Or.inl ⟨rfl, rfl⟩⟩
      · rcases IsSummand_of_part n K X r h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, Or.inr h2⟩
        · exact Or.inr ⟨h1, h2⟩

theorem G1_summand_subset (u K : Nat) (X : T) (huK : u ≤ K) : ∀ t : T, IsSummand K X t →
    ∀ y ∈ T.G1 u X, y ∈ T.G1 u t
  | Z, h => h.elim
  | P p a r, h => by
    intro y hy
    rcases h with ⟨rfl, rfl⟩ | h
    · exact (MT.G1_P_mem huK).2 (Or.inr (Or.inl hy))
    · have := G1_summand_subset u K X huK r h y hy
      by_cases hp : u ≤ p
      · exact (MT.G1_P_mem hp).2 (Or.inr (Or.inr this))
      · rw [T.G1, ite_eq_right hp]; exact this

theorem G1_summand_mem (u p : Nat) (a : T) (hup : u ≤ p) : ∀ t : T, IsSummand p a t →
    a ∈ T.G1 u t
  | Z, h => h.elim
  | P q b r, h => by
    rcases h with ⟨rfl, rfl⟩ | h
    · exact G1_mem_P_self hup _ _
    · have := G1_summand_mem u p a hup r h
      by_cases hq : u ≤ q
      · exact (MT.G1_P_mem hq).2 (Or.inr (Or.inr this))
      · rw [T.G1, ite_eq_right hq]; exact this

theorem IsSummand_NF (K : Nat) (X : T) : ∀ t : T, T.isNF1 t → IsSummand K X t →
    T.isNF1 X ∧ ∀ y ∈ T.G1 K X, y < X
  | Z, _, h => h.elim
  | P p a r, ht, h => by
    obtain ⟨ha, hr, hg, _⟩ := T.isNF1_P_inv p a r ht
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨ha, hg⟩
    · exact IsSummand_NF K X r hr h

theorem card_summand_lift (ι u K : Nat) (X y : T) (huι : u ≤ ι)
    (h : DomBy (T.G1 u (cardArg ι K X)) y) :
    ∀ s : T, IsSummand K X s → DomBy (T.G1 u (ct ι s)) y
  | Z, hs => hs.elim
  | P p a r, hs => by
    rw [ct_P]
    rcases hs with ⟨rfl, rfl⟩ | hs
    · exact DomBy_mono _ _ (fun v hv =>
        (MT.G1_P_mem (Nat.le_trans huι (Nat.le_max_right p ι))).2 (Or.inr (Or.inl hv))) y h
    · exact DomBy_mono _ _ (fun v hv => G1_ct_P_mem hv) y (card_summand_lift ι u K X y huι h r hs)

/-- Supports of a summand argument are dominated after cardinal multiplication. -/
theorem card_summand_dom (ι u K : Nat) (X : T) (huK : u ≤ K) (huι : u ≤ ι) :
    ∀ s : T, T.isNF1 s → IsSummand K X s → ∀ y ∈ T.G1 u X, DomBy (T.G1 u (ct ι s)) y := by
  intro s hs hsum y hy
  obtain ⟨ha, hga⟩ := IsSummand_NF K X s hs hsum
  apply card_summand_lift ι u K X y huι _ s hsum
  by_cases hKι : K < ι
  · rw [cardArg_lt_case ι K X hKι]
    by_cases hK0 : K = 0
    · rw [ite_eq_left hK0]
      exact G1_dom_ec K u huK X ha hga y hy
    · rw [ite_eq_right hK0]
      exact DomBy_mono _ _ (G1_stand_insert_supset u K _ (ec_closed K X ha hga).1) y
        (G1_dom_ec K u huK X ha hga y hy)
  · by_cases hc : K = ι ∧ X < P ι (P 0 Z Z) Z
    · obtain ⟨rfl, hlt⟩ := hc
      rw [cardArg_same_small K X hlt]
      exact DomBy_of_mem _ _ ((MT.G1_P_mem huK).2 (Or.inr (Or.inr hy)))
    · rw [cardArg_eq_self ι K X hKι hc]
      exact DomBy_of_mem _ _ hy

theorem card_summand_high_dom (ι u : Nat) (X : T) (huι : u < ι) :
    ∀ s : T, T.isNF1 s → IsSummand u X s → (part u X).1 ≠ Z →
      DomBy (T.G1 u (ct ι s)) (part u X).1 := by
  intro s hs hsum hne
  obtain ⟨ha, hga⟩ := IsSummand_NF u X s hs hsum
  apply card_summand_lift ι u u X _ (Nat.le_of_lt huι) _ s hsum
  have hd := (high_dom_ec u X ha hne).1
  rw [cardArg_lt_case ι u X huι]
  by_cases hp0 : u = 0
  · rw [ite_eq_left hp0]; exact hd
  · rw [ite_eq_right hp0]
    exact DomBy_mono _ _ (G1_stand_insert_supset u u _ (ec_closed u X ha hga).1) _ hd

theorem card_ec_G1_low_subset (ι u : Nat) (t : T) (ht : T.isNF1 t) :
    ∀ y ∈ T.G1 u (ct ι (part ι t).2), y ∈ T.G1 u (ct ι (ec ι t)) := by
  intro y hy
  have hLNF := (part_NF ι t ht).2
  rw [ec]
  by_cases hz : (part ι t).1 = Z
  · rw [ite_eq_left hz]; exact hy
  · rw [ite_eq_right hz, MT.stand, MT.stand_of_NF1 hLNF]
    by_cases hh : T.head (part ι t).2 ≤ P ι (part ι t).1 Z
    · rw [ite_eq_left hh]
      exact G1_ct_P_mem hy
    · rw [ite_eq_right hh]; exact hy

/-- Supports of a summand argument of a good term are dominated after collapse and
multiplication. -/
theorem early_card_summand_dom (ι u K : Nat) (t X : T) (ht : T.isNF1 t)
    (hg : ∀ y ∈ T.G1 ι t, y < t) (hs : IsSummand K X t) (huK : u ≤ K) (huι : u ≤ ι) :
    ∀ y ∈ T.G1 u X, DomBy (T.G1 u (ct ι (ec ι t))) y := by
  intro y hy
  have hLNF := (part_NF ι t ht).2
  rcases IsSummand_of_part ι K X t hs with ⟨_, hH⟩ | ⟨_, hL⟩
  · have hyH := G1_summand_subset u K X huK _ hH y hy
    have hne : (part ι t).1 ≠ Z := by intro h; rw [h] at hH; exact hH
    rw [ec, ite_eq_right hne, MT.stand, MT.stand_of_NF1 hLNF]
    by_cases hh : T.head (part ι t).2 ≤ P ι (part ι t).1 Z
    · rw [ite_eq_left hh, ct_P, Nat.max_self,
        cardArg_self_high ι _ _ (part_first_fixed ι t) hne (Or.inr rfl)]
      exact DomBy_of_mem _ _ ((MT.G1_P_mem huι).2 (Or.inr (Or.inl hyH)))
    · rw [ite_eq_right hh]
      obtain ⟨d, r, hL, hdH, hdNF, hpd⟩ := low_head_of_not_le ι t ht hh
      rw [hL, ct_P, Nat.max_self, cardArg_self_high ι _ d (part_first_fixed ι t) hne (Or.inl hdH)]
      apply DomBy_of_mem
      refine (MT.G1_P_mem huι).2 (Or.inr (Or.inl ?_))
      rw [← part_add ι d hdNF, MT.G1_add, hpd hg]
      exact List.mem_append_left _ hyH
  · exact DomBy_mono _ _ (card_ec_G1_low_subset ι u t ht) y
      (card_summand_dom ι u K X huK huι _ hLNF hL y hy)

theorem early_card_summand_high_dom (ι u : Nat) (t X : T) (ht : T.isNF1 t)
    (hs : IsSummand u X t) (huι : u < ι) (hne : (part u X).1 ≠ Z) :
    DomBy (T.G1 u (ct ι (ec ι t))) (part u X).1 := by
  have hLNF := (part_NF ι t ht).2
  rcases IsSummand_of_part ι u X t hs with ⟨hKι, _⟩ | ⟨_, hL⟩
  · exact absurd hKι (Nat.lt_asymm huι)
  · exact DomBy_mono _ _ (card_ec_G1_low_subset ι u t ht) _
      (card_summand_high_dom ι u X huι _ hLNF hL hne)

theorem IsSummand_oneDel (K : Nat) (X : T) (t : T) (h : IsSummand K X t)
    (hne : ¬ (K = 0 ∧ X = Z)) : IsSummand K X (oneDel t) := by
  rcases oneDel_cases t with he | ⟨b, rfl, he⟩
  · rw [he]; exact h
  · rw [he]
    rcases h with ⟨h1, h2⟩ | h
    · exact absurd ⟨h1.symm, h2.symm⟩ hne
    · exact h

theorem oneDel_card_summand_dom (ι u K : Nat) (t X : T) (ht : T.isNF1 t)
    (hs : IsSummand K X t) (huK : u ≤ K) (huι : u ≤ ι) :
    ∀ y ∈ T.G1 u X, DomBy (T.G1 u (ct ι (oneDel t))) y := by
  intro y hy
  by_cases hz : K = 0 ∧ X = Z
  · obtain ⟨rfl, rfl⟩ := hz
    cases hy
  · exact card_summand_dom ι u K X huK huι _ (oneDel_NF t ht) (IsSummand_oneDel K X t hs hz) y hy

theorem oneDel_card_summand_high_dom (ι u : Nat) (t X : T) (ht : T.isNF1 t)
    (hs : IsSummand u X t) (huι : u < ι) (hne : (part u X).1 ≠ Z) :
    DomBy (T.G1 u (ct ι (oneDel t))) (part u X).1 := by
  have hz : ¬ (u = 0 ∧ X = Z) := by
    intro ⟨_, hX⟩
    rw [hX] at hne
    exact hne rfl
  exact card_summand_high_dom ι u X huι _ (oneDel_NF t ht) (IsSummand_oneDel u X t hs hz) hne

theorem IsSummand_add_right (p : Nat) (c : T) : ∀ H L : T, IsSummand p c L →
    IsSummand p c (T.add H L)
  | Z, L, h => h
  | P q a r, L, h => by rw [T.P_add_eq]; exact Or.inr (IsSummand_add_right p c r L h)

theorem summands_of_part_fst (n : Nat) : ∀ c : T, ∀ p a, IsSummand p a (part n c).1 →
    IsSummand p a c
  | Z, _, _, h => h
  | P q b r, p, a, h => by
    by_cases hq : q ≤ n
    · rw [part_P_le b r hq] at h
      exact Or.inr (summands_of_part_fst n r p a h)
    · rw [part_P_gt b r hq] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (summands_of_part_fst n r p a h)

theorem summands_of_part_snd (n : Nat) : ∀ c : T, ∀ p a, IsSummand p a (part n c).2 →
    IsSummand p a c ∧ p ≤ n
  | Z, _, _, h => h.elim
  | P q b r, p, a, h => by
    by_cases hq : q ≤ n
    · rw [part_P_le b r hq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨Or.inl ⟨rfl, rfl⟩, hq⟩
      · exact (summands_of_part_snd n r p a h).imp_left Or.inr
    · rw [part_P_gt b r hq] at h
      exact (summands_of_part_snd n r p a h).imp_left Or.inr

theorem part_fst_summand_gt (q : Nat) : ∀ h : T, ∀ p c, IsSummand p c (part q h).1 → q < p
  | Z, _, _, hs => hs.elim
  | P p' a r, p, c, hs => by
    by_cases hp : p' ≤ q
    · rw [part_P_le a r hp] at hs
      exact part_fst_summand_gt q r p c hs
    · rw [part_P_gt a r hp] at hs
      rcases hs with ⟨rfl, _⟩ | hs
      · exact Nat.lt_of_not_le hp
      · exact part_fst_summand_gt q r p c hs

end OB
