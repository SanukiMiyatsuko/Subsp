import Subsp.old.stop_good

/-! Target-side visibility lemmas: supports of collapsed and multiplied terms dominate
the supports of their inputs. -/

namespace LegacyTranslation

open T

/-- `y` is dominated by some element of `l`. -/
def DomBy (l : List T) (y : T) : Prop := ∃ v ∈ l, y ≤ v

theorem DomBy_of_mem (l : List T) (y : T) (h : y ∈ l) : DomBy l y := ⟨y, h, Or.inr rfl⟩

theorem DomBy_mono (l l' : List T) (h : ∀ v ∈ l, v ∈ l') (y : T) (hy : DomBy l y) : DomBy l' y := by
  obtain ⟨v, hv, hyv⟩ := hy
  exact ⟨v, h v hv, hyv⟩

theorem DomBy_trans (l l' : List T) (h : ∀ v ∈ l, DomBy l' v) (y : T) (hy : DomBy l y) :
    DomBy l' y := by
  obtain ⟨v, hv, hyv⟩ := hy
  obtain ⟨w, hw, hvw⟩ := h v hv
  exact ⟨w, hw, partial_order.trans _ _ _ hyv hvw⟩

/-- The high part of an argument below a sum is a prefix of it. -/
theorem part_fst_of_between (K : Nat) (H L d : T) (hH : T.isNF1 H) (hd : T.isNF1 d)
    (hHL : T.isNF1 (T.add H L)) (hHfix : T.part K H = (H, T.Z))
    (hLlow : (T.part K L).1 = T.Z)
    (h1 : H < d) (h2 : d < T.add H L) : (T.part K d).1 = H := by
  have hpHL : (T.part K (T.add H L)).1 = H := by
    rw [part_add_distrib, hHfix, hLlow, T.add_Z]
  rcases part_lt_cases K H d hH hd h1 with h | ⟨he, _⟩
  · rw [hHfix] at h
    rcases part_lt_cases K d (T.add H L) hd hHL h2 with h' | ⟨he', _⟩
    · rw [hpHL] at h'
      exact False.elim (lt_asymm_thm h h')
    · rw [hpHL] at he'
      exact he'
  · rw [hHfix] at he
    exact he.symm

theorem G1_part_fst_subset (u n : Nat) (s : T) (hs : T.isNF1 s) :
    ∀ x ∈ T.G1 u (T.part n s).1, x ∈ T.G1 u s := by
  intro x hx
  rw [← part_add n s hs, G1_add]
  exact List.mem_append_left _ hx

/-- If the high part does not dominate the low part, the low part starts with `P K d _`, where
`d` exceeds the high part and (for good terms) has the same high part. -/
theorem low_head_of_not_le (K : Nat) (t : T) (ht : T.isNF1 t)
    (hnot : ¬ T.head (T.part K t).2 ≤ T.P K (T.part K t).1 T.Z) :
    ∃ d r, (T.part K t).2 = T.P K d r ∧ (T.part K t).1 < d ∧ T.isNF1 d ∧
      ((∀ y ∈ T.G1 K t, y < t) → (T.part K d).1 = (T.part K t).1) := by
  have he := part_add K t ht
  have hLNF := (part_NF K t ht).2
  have hi := part_second_index K t
  cases hL : (T.part K t).2 with
  | Z => rw [hL] at hnot; exact False.elim (hnot (T.Z_le _))
  | P q d r =>
      rw [hL] at hi hLNF hnot
      simp only [T.head] at hnot
      cases hi with
      | p _ _ _ hq _ =>
          have hqK : q = K := by
            rcases Nat.eq_or_lt_of_le hq with h | h
            · exact h
            · exact False.elim (hnot (Or.inl (T.Lt.p_head _ _ _ _ _ _ h)))
          subst q
          have hdH : (T.part K t).1 < d := by
            rcases lt_total_thm (T.part K t).1 d with h | h | h
            · exact h
            · exact False.elim (hnot (Or.inl (T.Lt.p_mid _ _ _ _ _ h)))
            · exact False.elim (hnot (Or.inr (by rw [h])))
          have hdNF := (T.isNF1_P_inv K d r hLNF).1
          refine ⟨d, r, rfl, hdH, hdNF, fun hg => ?_⟩
          have hdt : d < t := by
            apply hg d
            rw [← he, G1_add, hL]
            exact List.mem_append_right _ (by simp [T.G1])
          apply part_fst_of_between K _ _ d (part_NF K t ht).1 hdNF (by rw [he]; exact ht)
            (part_first_fixed K t) (by rw [hL, ← hL, part_of_index K _ (part_second_index K t)]) hdH
          rw [he]; exact hdt

/-- Supports of a term are dominated by supports of its early collapse. -/
theorem G1_dom_early_collapse (K u : Nat) (huK : u ≤ K) (X : T) (hX : T.isNF1 X)
    (hg : ∀ y ∈ T.G1 K X, y < X) :
    ∀ y ∈ T.G1 u X, DomBy (T.G1 u (T.early_collapse K X)) y := by
  intro y hy
  have he := part_add K X hX
  have hHNF := (part_NF K X hX).1
  have hLNF := (part_NF K X hX).2
  rw [← he, G1_add, List.mem_append] at hy
  dsimp only [T.early_collapse]
  split
  · rename_i hz
    rcases hy with hy | hy
    · rw [hz] at hy; cases hy
    · exact DomBy_of_mem _ _ hy
  · rename_i hz
    rw [T.stand, stand_eq_self _ hLNF]
    split
    · apply DomBy_of_mem
      simp only [T.G1, huK, ite_true, List.mem_append, List.mem_singleton]
      rcases hy with hy | hy
      · exact Or.inl (Or.inr hy)
      · exact Or.inr hy
    · rename_i hnot
      rcases hy with hy | hy
      · obtain ⟨d, r, hL, -, hdNF, hpd⟩ := low_head_of_not_le K X hX hnot
        refine ⟨y, ?_, Or.inr rfl⟩
        rw [hL]
        simp only [T.G1, huK, ite_true, List.mem_append, List.mem_singleton]
        left; right
        rw [← part_add K d hdNF, G1_add, hpd hg]
        exact List.mem_append_left _ hy
      · exact DomBy_of_mem _ _ hy

theorem high_lt_low_head (K : Nat) (H : T) (hH : T.part K H = (H, T.Z)) (hne : H ≠ T.Z) :
    ¬ H < T.P K (T.P 0 T.Z T.Z) T.Z := by
  cases H with
  | Z => exact False.elim (hne rfl)
  | P q d e =>
      have hq := part_first_head_gt K q (T.P q d e) d e (by rw [hH])
      intro h
      exact lt_asymm_thm h (T.Lt.p_head _ _ _ _ _ _ hq)

theorem cardArg_self_high (n : Nat) (H d : T) (hH : T.part n H = (H, T.Z)) (hne : H ≠ T.Z)
    (hd : H ≤ d) : cardArg n n d = d := by
  unfold cardArg
  rw [ite_eq_right (Nat.lt_irrefl n), ite_eq_right]
  intro ⟨_, hlt⟩
  exact high_lt_low_head n H hH hne (lt_of_le_of_lt_thm T _ _ _ hd hlt)

/-- The high part of a good term is dominated by supports of its early collapse. -/
theorem high_dom_early_collapse (u : Nat) (t : T) (ht : T.isNF1 t)
    (hH : (T.part u t).1 ≠ T.Z) :
    DomBy (T.G1 u (T.early_collapse u t)) (T.part u t).1 ∧
      DomBy (T.G1 u (T.card_times u (T.early_collapse u t))) (T.part u t).1 := by
  have he := part_add u t ht
  have hHNF := (part_NF u t ht).1
  have hLNF := (part_NF u t ht).2
  have hfix := part_first_fixed u t
  dsimp only [T.early_collapse]
  rw [ite_eq_right hH, T.stand, stand_eq_self _ hLNF]
  split
  · rw [card_times_P, Nat.max_self, cardArg_self_high u _ _ hfix hH (Or.inr rfl)]
    exact ⟨DomBy_of_mem _ _ (by simp [T.G1]), DomBy_of_mem _ _ (by simp [T.G1])⟩
  · obtain ⟨d, r, hL, hdH, -, -⟩ := low_head_of_not_le u t ht ‹_›
    rw [hL, card_times_P, Nat.max_self, cardArg_self_high u _ d hfix hH (Or.inl hdH)]
    exact ⟨⟨d, by simp [T.G1], Or.inl hdH⟩, ⟨d, by simp [T.G1], Or.inl hdH⟩⟩

theorem G1_stand_insert_supset (u K : Nat) (e : T) (he : T.isNF1 e) :
    ∀ y ∈ T.G1 u e, y ∈ T.G1 u (T.stand (T.P K T.Z e)) := by
  intro y hy
  rw [T.stand, stand_eq_self e he]
  split
  · by_cases hu : u ≤ K <;> simp [T.G1, hu, hy]
  · exact hy

theorem IsSummand_of_part (n K : Nat) (X : T) : ∀ t : T, IsSummand K X t →
    (n < K ∧ IsSummand K X (T.part n t).1) ∨ (K ≤ n ∧ IsSummand K X (T.part n t).2)
  | .Z, h => h.elim
  | .P p a r, h => by
      by_cases hp : p ≤ n
      · simp only [T.part, hp, ite_true]
        rcases h with ⟨rfl, rfl⟩ | h
        · exact Or.inr ⟨hp, Or.inl ⟨rfl, rfl⟩⟩
        · rcases IsSummand_of_part n K X r h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h1, Or.inr h2⟩
      · simp only [T.part, hp, ite_false]
        rcases h with ⟨rfl, rfl⟩ | h
        · exact Or.inl ⟨by omega, Or.inl ⟨rfl, rfl⟩⟩
        · rcases IsSummand_of_part n K X r h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, Or.inr h2⟩
          · exact Or.inr ⟨h1, h2⟩

theorem G1_summand_subset (u K : Nat) (X : T) (huK : u ≤ K) : ∀ t : T, IsSummand K X t →
    ∀ y ∈ T.G1 u X, y ∈ T.G1 u t
  | .Z, h => h.elim
  | .P p a r, h => by
      intro y hy
      rcases h with ⟨rfl, rfl⟩ | h
      · simp [T.G1, huK, hy]
      · have := G1_summand_subset u K X huK r h y hy
        by_cases hp : u ≤ p <;> simp [T.G1, hp, this]

theorem IsSummand_NF (K : Nat) (X : T) : ∀ t : T, T.isNF1 t → IsSummand K X t →
    T.isNF1 X ∧ ∀ y ∈ T.G1 K X, y < X
  | .Z, _, h => h.elim
  | .P p a r, ht, h => by
      obtain ⟨ha, hr, hg, _⟩ := T.isNF1_P_inv p a r ht
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨ha, hg⟩
      · exact IsSummand_NF K X r hr h

theorem card_summand_lift (ι u K : Nat) (X y : T) (huι : u ≤ ι)
    (h : DomBy (T.G1 u (cardArg ι K X)) y) :
    ∀ s : T, IsSummand K X s → DomBy (T.G1 u (T.card_times ι s)) y
  | .Z, hs => hs.elim
  | .P p a r, hs => by
      rw [card_times_P]
      rcases hs with ⟨rfl, rfl⟩ | hs
      · exact DomBy_mono _ _ (fun v hv => by
          simp only [T.G1, Nat.le_trans huι (Nat.le_max_right p ι), ite_true, List.mem_append]
          exact Or.inl (Or.inr hv)) y h
      · exact DomBy_mono _ _ (fun v hv => by by_cases hu : u ≤ max p ι <;> simp [T.G1, hu, hv]) y
          (card_summand_lift ι u K X y huι h r hs)

/-- Supports of a summand argument are dominated after cardinal multiplication. -/
theorem card_summand_dom (ι u K : Nat) (X : T) (huK : u ≤ K) (huι : u ≤ ι) :
    ∀ s : T, T.isNF1 s → IsSummand K X s →
      ∀ y ∈ T.G1 u X, DomBy (T.G1 u (T.card_times ι s)) y := by
  intro s hs hsum y hy
  obtain ⟨ha, hga⟩ := IsSummand_NF K X s hs hsum
  apply card_summand_lift ι u K X y huι _ s hsum
  by_cases hKι : K < ι
  · by_cases hK0 : K = 0
    · subst K
      simp only [cardArg, hKι, ite_true]
      exact G1_dom_early_collapse 0 u huK X ha hga y hy
    · simp only [cardArg, hKι, hK0, ite_true, ite_false]
      exact DomBy_mono _ _ (G1_stand_insert_supset u K _ (early_collapse_closed K X ha hga).1) y
        (G1_dom_early_collapse K u huK X ha hga y hy)
  · unfold cardArg
    rw [ite_eq_right hKι]
    split
    · apply DomBy_of_mem
      by_cases hu : u ≤ ι <;> simp [T.G1, hu, hy]
    · exact DomBy_of_mem _ _ hy

theorem card_summand_high_dom (ι u : Nat) (X : T) (huι : u < ι) :
    ∀ s : T, T.isNF1 s → IsSummand u X s → (T.part u X).1 ≠ T.Z →
      DomBy (T.G1 u (T.card_times ι s)) (T.part u X).1 := by
  intro s hs hsum hne
  obtain ⟨ha, hga⟩ := IsSummand_NF u X s hs hsum
  apply card_summand_lift ι u u X _ (Nat.le_of_lt huι) _ s hsum
  have hd := (high_dom_early_collapse u X ha hne).1
  by_cases hp0 : u = 0
  · subst u
    simp only [cardArg, huι, ite_true]
    exact hd
  · simp only [cardArg, huι, hp0, ite_true, ite_false]
    exact DomBy_mono _ _ (G1_stand_insert_supset u u _ (early_collapse_closed u X ha hga).1) _ hd

theorem card_early_G1_low_subset (ι u : Nat) (t : T) (ht : T.isNF1 t) :
    ∀ y ∈ T.G1 u (T.card_times ι (T.part ι t).2),
      y ∈ T.G1 u (T.card_times ι (T.early_collapse ι t)) := by
  intro y hy
  have hLNF := (part_NF ι t ht).2
  dsimp only [T.early_collapse]
  split
  · exact hy
  · rw [T.stand, stand_eq_self _ hLNF]
    split
    · rw [card_times_P, Nat.max_self]
      by_cases hu : u ≤ ι <;> simp [T.G1, hu, hy]
    · exact hy

/-- Supports of a summand argument of a good term are dominated after collapse and
multiplication at a positive index. -/
theorem early_card_summand_dom (ι u K : Nat) (t X : T) (ht : T.isNF1 t)
    (hg : ∀ y ∈ T.G1 ι t, y < t) (hs : IsSummand K X t) (huK : u ≤ K) (huι : u ≤ ι) :
    ∀ y ∈ T.G1 u X, DomBy (T.G1 u (T.card_times ι (T.early_collapse ι t))) y := by
  intro y hy
  have he := part_add ι t ht
  have hHNF := (part_NF ι t ht).1
  have hLNF := (part_NF ι t ht).2
  rcases IsSummand_of_part ι K X t hs with ⟨hKι, hH⟩ | ⟨hKι, hL⟩
  · -- the summand lies in the collapsed high part
    have hyH := G1_summand_subset u K X huK _ hH y hy
    have hne : (T.part ι t).1 ≠ T.Z := by intro h; rw [h] at hH; exact hH
    dsimp only [T.early_collapse]
    rw [ite_eq_right hne, T.stand, stand_eq_self _ hLNF]
    split
    · rw [card_times_P, Nat.max_self, cardArg_self_high ι _ _ (part_first_fixed ι t) hne (Or.inr rfl)]
      exact DomBy_of_mem _ _ (by simp [T.G1, huι, hyH])
    · obtain ⟨d, r, hL, hdH, hdNF, hpd⟩ := low_head_of_not_le ι t ht ‹_›
      rw [hL, card_times_P, Nat.max_self,
        cardArg_self_high ι _ d (part_first_fixed ι t) hne (Or.inl hdH)]
      apply DomBy_of_mem
      simp only [T.G1, huι, ite_true, List.mem_append, List.mem_singleton]
      left; right
      rw [← part_add ι d hdNF, G1_add, hpd hg]
      exact List.mem_append_left _ hyH
  · exact DomBy_mono _ _ (card_early_G1_low_subset ι u t ht) y
      (card_summand_dom ι u K X huK huι _ hLNF hL y hy)

theorem early_card_summand_high_dom (ι u : Nat) (t X : T) (ht : T.isNF1 t)
    (hs : IsSummand u X t) (huι : u < ι) (hne : (T.part u X).1 ≠ T.Z) :
    DomBy (T.G1 u (T.card_times ι (T.early_collapse ι t))) (T.part u X).1 := by
  have hLNF := (part_NF ι t ht).2
  rcases IsSummand_of_part ι u X t hs with ⟨hKι, _⟩ | ⟨_, hL⟩
  · exact False.elim (Nat.lt_asymm huι hKι)
  · exact DomBy_mono _ _ (card_early_G1_low_subset ι u t ht) _
      (card_summand_high_dom ι u X huι _ hLNF hL hne)

theorem IsSummand_one_del (K : Nat) (X : T) (t : T) (h : IsSummand K X t)
    (hne : ¬ (K = 0 ∧ X = T.Z)) : IsSummand K X (T.one_del t) := by
  match t, h with
  | .P 0 .Z _, h => exact Or.resolve_left h fun ⟨h1, h2⟩ => hne ⟨h1.symm, h2.symm⟩
  | .Z, h | .P (_ + 1) _ _, h | .P 0 (.P _ _ _) _, h => exact h

theorem one_del_card_summand_dom (ι u K : Nat) (t X : T) (ht : T.isNF1 t)
    (hs : IsSummand K X t) (huK : u ≤ K) (huι : u ≤ ι) :
    ∀ y ∈ T.G1 u X, DomBy (T.G1 u (T.card_times ι (T.one_del t))) y := by
  intro y hy
  by_cases hz : K = 0 ∧ X = T.Z
  · obtain ⟨rfl, rfl⟩ := hz
    cases hy
  · exact card_summand_dom ι u K X huK huι _ (one_del_NF t ht) (IsSummand_one_del K X t hs hz) y hy

theorem one_del_card_summand_high_dom (ι u : Nat) (t X : T) (ht : T.isNF1 t)
    (hs : IsSummand u X t) (huι : u < ι) (hne : (T.part u X).1 ≠ T.Z) :
    DomBy (T.G1 u (T.card_times ι (T.one_del t))) (T.part u X).1 := by
  have hz : ¬ (u = 0 ∧ X = T.Z) := by
    rintro ⟨_, rfl⟩
    exact hne rfl
  exact card_summand_high_dom ι u X huι _ (one_del_NF t ht) (IsSummand_one_del u X t hs hz) hne

end LegacyTranslation
