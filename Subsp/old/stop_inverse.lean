import Subsp.old.stop_nf_order

/-! Legacy inverse-construction machinery.
The grouping follows the role of `Subsp.new.stop_inverse`.
-/

-- Merged from Subsp/old/stop_reverse_target.lean
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

-- Merged from Subsp/old/stop_reverse.lean
/-! Reverse transfer: Buchholz goodness of a translation implies indexed goodness of the
source term. -/

namespace LegacyTranslation

open T

/-! Coordinates of index `u` reached through coordinates of larger index. -/

inductive Reach {lam : Nat} (u : Nat) : new.T lam → new.T lam → Prop where
  | here (w : new.Vec (new.T lam) lam) (b : new.T lam) (i : Fin lam) (hi : i.val = u) :
      Reach u (new.T.P w b) (w.idx i)
  | tail (w : new.Vec (new.T lam) lam) (b c : new.T lam) :
      Reach u b c → Reach u (new.T.P w b) c
  | deep (w : new.Vec (new.T lam) lam) (b c : new.T lam) (i : Fin lam) (hi : u + 1 ≤ i.val) :
      Reach u (w.idx i) c → Reach u (new.T.P w b) c

theorem Gi_split {lam : Nat} (u : Nat) : ∀ x z : new.T lam, z ∈ new.T.Gi u x →
    z ∈ new.T.Gi (u + 1) x ∨ ∃ c, Reach u x c ∧ (z = c ∨ z ∈ new.T.Gi u c) := by
  intro x
  induction x using (measure new.T.size).wf.induction with
  | h x ih =>
      intro z hz
      cases x with
      | Z => cases hz
      | P w b =>
          rcases (new.T.mem_Gi_P u w b z).mp hz with ⟨i, hui, hzi⟩ | hzb
          · rcases Nat.eq_or_lt_of_le hui with hiu | hiu
            · exact Or.inr ⟨w.idx i, .here w b i hiu.symm, hzi⟩
            · rcases hzi with rfl | hzi
              · exact Or.inl ((new.T.mem_Gi_P (u + 1) w b _).mpr (Or.inl ⟨i, hiu, Or.inl rfl⟩))
              · rcases ih (w.idx i) (new.T.idx_size_lt_P w b i) z hzi with h | ⟨c, hc, hzc⟩
                · exact Or.inl ((new.T.mem_Gi_P (u + 1) w b _).mpr (Or.inl ⟨i, hiu, Or.inr h⟩))
                · exact Or.inr ⟨c, .deep w b c i hiu hc, hzc⟩
          · rcases ih b (new.T.add_size_lt_P w b) z hzb with h | ⟨c, hc, hzc⟩
            · exact Or.inl ((new.T.mem_Gi_P (u + 1) w b _).mpr (Or.inr h))
            · exact Or.inr ⟨c, .tail w b c hc, hzc⟩

theorem Reach_comp {lam : Nat} (u : Nat) {x c : new.T lam} (h : Reach u x c) :
    new.T.isNF x → new.T.isNFComp u c ∧ new.T.size c < new.T.size x := by
  induction h with
  | here w b i hi =>
      intro hx
      refine ⟨?_, new.T.idx_size_lt_P w b i⟩
      have := (new.T.isNF_P_inv w b hx).1 i
      rwa [hi] at this
  | tail w b c _ ih =>
      intro hx
      obtain ⟨hc, hs⟩ := ih (new.T.isNF_P_inv w b hx).2.1
      exact ⟨hc, Nat.lt_trans hs (new.T.add_size_lt_P w b)⟩
  | deep w b c i _ _ ih =>
      intro hx
      obtain ⟨hc, hs⟩ := ih ((new.T.isNF_P_inv w b hx).1 i).1
      exact ⟨hc, Nat.lt_trans hs (new.T.idx_size_lt_P w b i)⟩

theorem Reach_ne_Z {lam : Nat} (u : Nat) {x c : new.T lam} (h : Reach u x c) : x ≠ new.T.Z := by
  cases h <;> intro he <;> cases he

/-! Structure of principal translations. -/

theorem aux_above_zero {lam : Nat} : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    ∀ p a, (transAux v).1 = T.P p a T.Z → ∀ i : Fin k, p < i.val → v.idx i = new.T.Z
  | _, .nil, _, _, _, i, _ => i.elim0
  | _, .snoc k v a, p, b, he, i, hi => by
      cases k with
      | zero =>
          cases v
          rw [aux_single] at he
          cases he
          have : i.val = 0 := by have := i.isLt; omega
          omega
      | succ k =>
          by_cases haz : a = new.T.Z
          · subst a
            rw [aux_zero_tail] at he
            by_cases hik : i.val < k + 1
            · simp only [new.Vec.idx, hik, dite_true]
              exact aux_above_zero v p b he ⟨i.val, hik⟩ hi
            · simp [new.Vec.idx, hik]
          · rw [aux_head_snoc v a haz] at he
            cases he
            have := i.isLt
            omega

def Contr {lam : Nat} (i : Nat) (x : new.T lam) : T :=
  if i = 0 then T.early_collapse 0 (trans x) else T.card_times i (T.early_collapse i (trans x))

def TopContr {lam : Nat} (i : Nat) (x : new.T lam) : T :=
  if i = 0 then trans x else T.card_times i (T.one_del (trans x))

theorem aux_contr_G1 {lam : Nat} (u : Nat) : ∀ {k : Nat} (v : new.Vec (new.T lam) k),
    (∀ i : Fin k, ∀ y ∈ T.G1 u (Contr i.val (v.idx i)), y ∈ T.G1 u (transAux v).2) ∧
    ∀ p a, (transAux v).1 = T.P p a T.Z →
      (∀ i : Fin k, i.val < p → ∀ y ∈ T.G1 u (Contr i.val (v.idx i)), y ∈ T.G1 u a) ∧
      (∀ i : Fin k, i.val = p → ∀ y ∈ T.G1 u (TopContr p (v.idx i)), y ∈ T.G1 u a) ∧
      (∀ i : Fin k, i.val = p → 0 < p → TopContr p (v.idx i) ≤ a)
  | _, .nil => ⟨fun i => i.elim0, fun _ _ _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩⟩
  | _, .snoc k v a => by
      cases k with
      | zero =>
          cases v
          rw [aux_single]
          refine ⟨?_, ?_⟩
          · intro i y hy
            have : i = Fin.last 0 := Fin.eq_of_val_eq (by have := i.isLt; omega)
            subst this
            simpa [Contr, new.Vec.idx] using hy
          · intro p b he
            cases he
            refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), ?_, fun _ _ h => absurd h (Nat.lt_irrefl 0)⟩
            intro i _ y hy
            have : i = Fin.last 0 := Fin.eq_of_val_eq (by have := i.isLt; omega)
            subst this
            simpa [TopContr, new.Vec.idx] using hy
      | succ k =>
          have ih := aux_contr_G1 u v
          have hlast (i : Fin (k + 1 + 1)) (hi : ¬ i.val < k + 1) :
              (new.Vec.snoc (k + 1) v a).idx i = a := by simp [new.Vec.idx, hi]
          have hcast (i : Fin (k + 1 + 1)) (hi : i.val < k + 1) :
              (new.Vec.snoc (k + 1) v a).idx i = v.idx ⟨i.val, hi⟩ := by simp [new.Vec.idx, hi]
          refine ⟨?_, ?_⟩
          · intro i y hy
            rw [aux_lower_snoc, G1_add, List.mem_append]
            by_cases hi : i.val < k + 1
            · rw [hcast i hi] at hy
              exact Or.inr (ih.1 ⟨i.val, hi⟩ y hy)
            · rw [hlast i hi] at hy
              have hiv : i.val = k + 1 := by have := i.isLt; omega
              rw [hiv] at hy
              exact Or.inl (by simpa [Contr] using hy)
          · intro p b he
            by_cases haz : a = new.T.Z
            · subst a
              rw [aux_zero_tail] at he
              have hp := aux_top_le v p b he
              have hv := ih.2 p b he
              refine ⟨fun i hi y hy => ?_, fun i hi y hy => ?_, fun i hi hp0 => ?_⟩
              · have hik : i.val < k + 1 := by omega
                rw [hcast i hik] at hy
                exact hv.1 ⟨i.val, hik⟩ hi y hy
              · have hik : i.val < k + 1 := by omega
                rw [hcast i hik] at hy
                exact hv.2.1 ⟨i.val, hik⟩ hi y hy
              · have hik : i.val < k + 1 := by omega
                rw [hcast i hik]
                exact hv.2.2 ⟨i.val, hik⟩ hi hp0
            · rw [aux_head_snoc v a haz] at he
              cases he
              refine ⟨fun i hi y hy => ?_, fun i hi y hy => ?_, fun i hi _ => ?_⟩
              · rw [hcast i hi] at hy
                rw [G1_add, List.mem_append]
                exact Or.inr (ih.1 ⟨i.val, hi⟩ y hy)
              · have hik : ¬ i.val < k + 1 := by omega
                rw [hlast i hik] at hy
                rw [G1_add, List.mem_append]
                exact Or.inl (by simpa [TopContr] using hy)
              · have hik : ¬ i.val < k + 1 := by omega
                rw [hlast i hik]
                simpa [TopContr] using add_self_le _ _

theorem aux_head_countable {lam : Nat} {k : Nat} (v : new.Vec (new.T lam) (k + 1))
    (a : T) (he : (transAux v).1 = T.P 0 a T.Z) :
    a = trans (v.idx ⟨0, Nat.zero_lt_succ k⟩) := by
  rw [transAux_countable_head_exact v (aux_above_zero v 0 a he)] at he
  cases he
  rfl

/-! Splitting a source term by the index of its principal summands. -/

def headIdx {lam : Nat} (w : new.Vec (new.T lam) lam) : Nat :=
  match (transAux w).1 with
  | .P p _ _ => p
  | .Z => 0

theorem headIdx_eq {lam : Nat} (w : new.Vec (new.T lam) lam) (p : Nat) (a : T)
    (he : (transAux w).1 = T.P p a T.Z) : headIdx w = p := by
  simp [headIdx, he]

def srcPart {lam : Nat} (j : Nat) : new.T lam → new.T lam × new.T lam
  | .Z => (.Z, .Z)
  | .P w b =>
      if j < headIdx w then (.P w (srcPart j b).1, (srcPart j b).2)
      else ((srcPart j b).1, .P w (srcPart j b).2)

theorem trans_P_headIdx {lam : Nat} (w : new.Vec (new.T lam) lam) (b : new.T lam) :
    ∃ X, (transAux w).1 = T.P (headIdx w) X T.Z ∧ trans (new.T.P w b) = T.P (headIdx w) X (trans b) := by
  obtain ⟨p, a, he, _⟩ := aux_principal w
  rw [headIdx_eq w p a he]
  exact ⟨a, he, by rw [trans_as_add, he, p_zero_add]⟩

theorem srcPart_trans {lam : Nat} (j : Nat) : ∀ s : new.T lam,
    trans (srcPart j s).1 = (T.part j (trans s)).1
  | .Z => rfl
  | .P w b => by
      obtain ⟨X, he, htr⟩ := trans_P_headIdx w b
      have ih := srcPart_trans j b
      rw [htr]
      by_cases hj : j < headIdx w
      · simp only [srcPart, hj, ite_true, T.part, show ¬ headIdx w ≤ j by omega, ite_false]
        obtain ⟨X', he', htr'⟩ := trans_P_headIdx w (srcPart j b).1
        rw [htr', ih]
        rw [he] at he'
        cases he'
        rfl
      · simp only [srcPart, hj, ite_false, T.part, show headIdx w ≤ j by omega, ite_true]
        exact ih

theorem srcPart_size {lam : Nat} (j : Nat) : ∀ s : new.T lam,
    new.T.size (srcPart j s).1 ≤ new.T.size s
  | .Z => Nat.le_refl _
  | .P w b => by
      have ih := srcPart_size j b
      by_cases hj : j < headIdx w
      · simp only [srcPart, hj, ite_true, new.T.size]; omega
      · simp only [srcPart, hj, ite_false, new.T.size]; omega

theorem headIdx_mono {lam : Nat} (w w' : new.Vec (new.T lam) lam)
    (hw : ∀ i : Fin lam, new.T.isNFComp i.val (w.idx i))
    (hw' : ∀ i : Fin lam, new.T.isNFComp i.val (w'.idx i))
    (h : new.T.P w' new.T.Z ≤ new.T.P w new.T.Z) : headIdx w' ≤ headIdx w := by
  have hn := new.T.isNF.p w new.T.Z (fun i => (hw i).1) new.T.isNF.z (fun i => (hw i).2) (new.T.Z_le _)
  have hn' := new.T.isNF.p w' new.T.Z (fun i => (hw' i).1) new.T.isNF.z (fun i => (hw' i).2) (new.T.Z_le _)
  obtain ⟨X, he, htr⟩ := trans_P_headIdx w new.T.Z
  obtain ⟨X', he', htr'⟩ := trans_P_headIdx w' new.T.Z
  have hle : trans (new.T.P w' new.T.Z) ≤ trans (new.T.P w new.T.Z) := by
    rcases h with h | h
    · exact Or.inl (trans_lt_of_lt _ _ hn' hn h)
    · rw [new.T_eq_sound _ _ h]; exact Or.inr rfl
  rw [htr, htr'] at hle
  exact head_le_index _ _ _ _ hle

theorem srcPart_NF {lam : Nat} (j : Nat) : ∀ s : new.T lam, new.T.isNF s →
    new.T.isNF (srcPart j s).1 ∧
      (∀ w b, s = new.T.P w b → headIdx w ≤ j → (srcPart j s).1 = new.T.Z)
  | .Z, _ => ⟨new.T.isNF.z, fun _ _ h => by cases h⟩
  | .P w b, hs => by
      obtain ⟨hw, hb, hh⟩ := new.T.isNF_P_inv w b hs
      have ih := srcPart_NF j b hb
      have hbz : ∀ w' b', b = new.T.P w' b' → headIdx w' ≤ headIdx w := by
        intro w' b' hbe
        subst hbe
        obtain ⟨hw', _, _⟩ := new.T.isNF_P_inv w' b' hb
        exact headIdx_mono w w' hw hw' hh
      refine ⟨?_, ?_⟩
      · by_cases hj : j < headIdx w
        · simp only [srcPart, hj, ite_true]
          refine new.T.isNF.p w _ (fun i => (hw i).1) ih.1 (fun i => (hw i).2) ?_
          cases hbe : b with
          | Z => simp only [srcPart]; exact new.T.Z_le _
          | P w' b' =>
              rw [hbe] at hh
              by_cases hj' : j < headIdx w'
              · simp only [srcPart, hj', ite_true]
                exact hh
              · rw [← hbe, ih.2 w' b' hbe (by omega)]
                exact new.T.Z_le _
        · simp only [srcPart, hj, ite_false]
          exact ih.1
      · intro w0 b0 he hj
        have hw0 : w0 = w := by injection he with h1 h2; exact h1.symm
        subst hw0
        simp only [srcPart, show ¬ j < headIdx w0 by omega, ite_false]
        cases hbe : b with
        | Z => rfl
        | P w' b' => rw [← hbe]; exact ih.2 w' b' hbe (Nat.le_trans (hbz w' b' hbe) hj)

end LegacyTranslation

-- Merged from Subsp/old/stop_reverse_main.lean
/-! Reverse transfer, assembled by downward induction on the support level. -/

namespace LegacyTranslation

open T

theorem G1_summand_mem (u p : Nat) (a : T) (hup : u ≤ p) : ∀ t : T, IsSummand p a t →
    a ∈ T.G1 u t
  | .Z, h => h.elim
  | .P q b r, h => by
      rcases h with ⟨rfl, rfl⟩ | h
      · simp [T.G1, hup]
      · have := G1_summand_mem u p a hup r h
        by_cases hq : u ≤ q <;> simp [T.G1, hq, this]

/-- Visibility invariant: arguments of principal summands are dominated by `V`. -/
def SInv {lam : Nat} (u : Nat) (V : List T) : new.T lam → Prop
  | .Z => True
  | .P w b =>
      (∀ p a, (transAux w).1 = T.P p a T.Z → u ≤ p →
        (∀ y ∈ T.G1 u a, DomBy V y) ∧
          (p = u → (T.part u a).1 ≠ T.Z → DomBy V (T.part u a).1)) ∧
      SInv u V b

theorem SInv_of_summands {lam : Nat} (u : Nat) (V : List T) : ∀ x : new.T lam,
    (∀ p a, IsSummand p a (trans x) → u ≤ p →
      (∀ y ∈ T.G1 u a, DomBy V y) ∧
        (p = u → (T.part u a).1 ≠ T.Z → DomBy V (T.part u a).1)) →
    SInv u V x
  | .Z, _ => trivial
  | .P w b, h => by
      obtain ⟨X, he, htr⟩ := trans_P_headIdx w b
      refine ⟨fun p a he' hup => ?_,
        SInv_of_summands u V b (fun p a hs hup => h p a (by rw [htr]; exact Or.inr hs) hup)⟩
      rw [he] at he'
      cases he'
      exact h _ _ (by rw [htr]; exact Or.inl ⟨rfl, rfl⟩) hup

theorem SInv_top {lam : Nat} (u : Nat) (A : new.T lam) (hA : new.T.isNF A) :
    SInv u (T.G1 u (trans A)) A := by
  have hAnf := trans_isNF1 A hA
  apply SInv_of_summands
  intro p a hs hup
  have hmem := G1_summand_mem u p a hup _ hs
  refine ⟨fun y hy => DomBy_of_mem _ _ (G1_summand_subset u p a hup _ hs y hy),
    fun _ _ => ⟨a, hmem, part_first_le u a (IsSummand_NF p a _ hAnf hs).1⟩⟩

theorem deepDom {lam : Nat} (u : Nat) (V : List T) {q c : new.T lam} (hr : Reach u q c) :
    new.T.isNF q → SInv u V q → (T.part u (trans c)).1 ≠ T.Z →
      DomBy V (T.part u (trans c)).1 := by
  induction hr with
  | here w b i hi =>
      intro hq hinv hne
      obtain ⟨hw, _, _⟩ := new.T.isNF_P_inv w b hq
      have hvg : VecGood w := fun i => trans_good i.val (w.idx i) (hw i)
      obtain ⟨p, a, he, _⟩ := aux_principal w
      have hci := hw i
      rw [hi] at hci
      have hcg := trans_good u (w.idx i) hci
      rcases Nat.lt_trichotomy p u with hp | hp | hp
      · have hz := aux_above_zero w p a he i (by omega)
        rw [hz] at hne
        exact False.elim (hne rfl)
      · subst hp
        have heq := aux_head_high_eq w hvg p a he i hi
        rw [← heq] at hne ⊢
        exact (hinv.1 p a he (Nat.le_refl _)).2 rfl hne
      · have hcon := (aux_contr_G1 u w).2 p a he
        have hd := high_dom_early_collapse u (trans (w.idx i)) hcg.1 hne
        have hdomA : DomBy (T.G1 u a) (T.part u (trans (w.idx i))).1 := by
          by_cases hu0 : u = 0
          · subst hu0
            exact DomBy_mono _ _ (fun v hv => hcon.1 i (by omega) v
              (by simpa [Contr, hi] using hv)) _ hd.1
          · exact DomBy_mono _ _ (fun v hv => hcon.1 i (by omega) v
              (by simpa [Contr, hi, hu0] using hv)) _ hd.2
        exact DomBy_trans _ _ (fun v hv => (hinv.1 p a he (by omega)).1 v hv) _ hdomA
  | tail w b c _ ih =>
      intro hq hinv hne
      exact ih (new.T.isNF_P_inv w b hq).2.1 hinv.2 hne
  | deep w b c i hi hr ih =>
      intro hq hinv hne
      obtain ⟨hw, _, _⟩ := new.T.isNF_P_inv w b hq
      obtain ⟨p, a, he, _⟩ := aux_principal w
      have hne' : w.idx i ≠ new.T.Z := Reach_ne_Z u hr
      have hip : i.val ≤ p := Nat.le_of_not_gt fun h => hne' (aux_above_zero w p a he i h)
      have hg := trans_good i.val (w.idx i) (hw i)
      have hcon := (aux_contr_G1 u w).2 p a he
      have hdomA := hinv.1 p a he (by omega)
      apply ih (hw i).1 _ hne
      apply SInv_of_summands u V (w.idx i)
      intro p' a' hs hup'
      have hi0 : i.val ≠ 0 := by omega
      rcases Nat.lt_or_ge i.val p with hlt | hge
      · have hsub : ∀ v ∈ T.G1 u (T.card_times i.val (T.early_collapse i.val (trans (w.idx i)))),
            v ∈ T.G1 u a := fun v hv => hcon.1 i hlt v (by simpa [Contr, hi0] using hv)
        refine ⟨fun y hy => ?_, fun hpu hne2 => ?_⟩
        · exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
            (early_card_summand_dom i.val u p' (trans (w.idx i)) a' hg.1 hg.2 hs hup'
              (by omega) y hy))
        · subst p'
          exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
            (early_card_summand_high_dom i.val u (trans (w.idx i)) a' hg.1 hs (by omega) hne2))
      · have hip' : i.val = p := by omega
        have hcon2 := hcon.2.1 i hip'
        rw [← hip'] at hcon2
        have hsub : ∀ v ∈ T.G1 u (T.card_times i.val (T.one_del (trans (w.idx i)))),
            v ∈ T.G1 u a := fun v hv => hcon2 v (by simpa [TopContr, hi0] using hv)
        refine ⟨fun y hy => ?_, fun hpu hne2 => ?_⟩
        · exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
            (one_del_card_summand_dom i.val u p' (trans (w.idx i)) a' hg.1 hs hup'
              (by omega) y hy))
        · subst p'
          exact DomBy_trans _ _ (fun v hv => hdomA.1 v hv) _ (DomBy_mono _ _ hsub _
            (one_del_card_summand_high_dom i.val u (trans (w.idx i)) a' hg.1 hs (by omega) hne2))

/-! Suffixes of a source sum. -/

inductive Suffix {lam : Nat} : new.T lam → new.T lam → Prop where
  | refl (x : new.T lam) : Suffix x x
  | step (w : new.Vec (new.T lam) lam) (b x : new.T lam) : Suffix x b → Suffix x (new.T.P w b)

theorem Suffix_tail {lam : Nat} {w : new.Vec (new.T lam) lam} {b A : new.T lam}
    (h : Suffix (new.T.P w b) A) : Suffix b A := by
  generalize hx : new.T.P w b = x at h
  induction h with
  | refl => subst hx; exact .step w b b (.refl b)
  | step w' b' x _ ih => exact .step w' b' b (ih hx)

theorem Suffix_summand {lam : Nat} {x A : new.T lam} (h : Suffix x A) :
    ∀ p a, IsSummand p a (trans x) → IsSummand p a (trans A) := by
  induction h with
  | refl => exact fun _ _ h => h
  | step w b x _ ih =>
      intro p a hs
      obtain ⟨X, _, htr⟩ := trans_P_headIdx w b
      rw [htr]
      exact Or.inr (ih p a hs)

theorem Suffix_srcPart_size {lam : Nat} (j : Nat) {x A : new.T lam} (h : Suffix x A) :
    new.T.size (srcPart j x).1 ≤ new.T.size (srcPart j A).1 := by
  induction h with
  | refl => exact Nat.le_refl _
  | step w b x _ ih =>
      by_cases hj : j < headIdx w
      · simp only [srcPart, hj, ite_true, new.T.size]; omega
      · simp only [srcPart, hj, ite_false]; exact ih

theorem Reach_size {lam : Nat} (u : Nat) {x c : new.T lam} (h : Reach u x c) :
    new.T.size c < new.T.size x := by
  induction h with
  | here w b i _ => exact new.T.idx_size_lt_P w b i
  | tail w b c _ ih => exact Nat.lt_trans ih (new.T.add_size_lt_P w b)
  | deep w b c i _ _ ih => exact Nat.lt_trans ih (new.T.idx_size_lt_P w b i)

theorem Z_lt_of_ne {lam : Nat} (s : new.T lam) (h : s ≠ new.T.Z) : new.T.Z < s := by
  cases s with
  | Z => exact False.elim (h rfl)
  | P w b => rfl

/-! The key comparison: reached index-`u` coordinates are below the ambient term. -/

theorem reach_lt {lam : Nat} (u : Nat) (A : new.T lam) (hA : new.T.isNF A)
    (hgood : ∀ y ∈ T.G1 u (trans A), y < trans A) (c : new.T lam) (hc : Reach u A c) :
    c < A := by
  have hAnf := trans_isNF1 A hA
  have hcnf : new.T.isNF c := (Reach_comp u hc hA).1.1
  have hcnf1 := trans_isNF1 c hcnf
  have hAne : new.T.Z < A := Z_lt_of_ne A (Reach_ne_Z u hc)
  have hdom : (T.part u (trans c)).1 ≠ T.Z → (T.part u (trans c)).1 < trans A := by
    intro hne
    obtain ⟨v, hv, hle⟩ := deepDom u _ hc hA (SInv_top u A hA) hne
    exact lt_of_le_of_lt_thm T _ _ _ hle (hgood v hv)
  have prefixArg : ∀ (x : new.T lam), Suffix x A → ∀ w b, x = new.T.P w b →
      u < headIdx w → new.T.size c < new.T.size (srcPart u x).1 → c < A := by
    intro x hsx w b hx hu hsz
    obtain ⟨X, _, htr⟩ := trans_P_headIdx w b
    have hsum : IsSummand (headIdx w) X (trans A) :=
      Suffix_summand hsx _ _ (by rw [hx, htr]; exact Or.inl ⟨rfl, rfl⟩)
    have hhead : T.P (headIdx w) X T.Z ≤ trans A :=
      partial_order.trans _ _ _ (summand_le_head _ _ _ hAnf hsum) (head_le_self _)
    have hsA := Suffix_srcPart_size u hsx
    have hsc := srcPart_size u c
    rcases new.T_total c A with h | h | h
    · exact h
    · exfalso
      have htr' := trans_lt_of_lt A c hA hcnf h
      by_cases hz : (T.part u (trans c)).1 = T.Z
      · have hcp : trans c = (T.part u (trans c)).2 := by
          have := part_add u _ hcnf1
          rw [hz, zero_add] at this
          exact this.symm
        have hidx := part_second_index u (trans c)
        rw [← hcp] at hidx
        have hlt : trans c < trans A :=
          lt_of_lt_of_le_thm T _ _ _ (index_Prop1_lt_succ u _ hidx)
            (partial_order.trans _ _ _ (head_base_le (u + 1) _ X hu) hhead)
        exact lt_asymm_thm hlt htr'
      · have hH := hdom hz
        rcases part_lt_cases u (trans A) (trans c) hAnf hcnf1 htr' with h1 | ⟨h1, _⟩
        · have hHnf := (part_NF u (trans c) hcnf1).1
          have : trans A < (T.part u (trans c)).1 :=
            lt_of_part_lt_cases u _ _ hAnf hHnf (Or.inl (by rw [part_first_fixed]; exact h1))
          exact lt_asymm_thm this hH
        · have hs1 : (srcPart u A).1 = (srcPart u c).1 := by
            apply trans_injective_NF _ _ (srcPart_NF u A hA).1 (srcPart_NF u c hcnf).1
            rw [srcPart_trans, srcPart_trans, h1]
          rw [hs1] at hsA
          omega
    · exfalso
      subst h
      omega
  have main : ∀ x c', Reach u x c' → c' = c → Suffix x A → c < A := by
    intro x c' hr
    induction hr with
    | here w b i hi =>
        intro hceq hsx
        subst hceq
        obtain ⟨p, a, he, _⟩ := aux_principal w
        have hhp := headIdx_eq w p a he
        rcases Nat.lt_trichotomy p u with hp | hp | hp
        · rw [aux_above_zero w p a he i (by omega)]
          exact hAne
        · subst hp
          obtain ⟨X, he', htr⟩ := trans_P_headIdx w b
          rw [he, hhp] at he'
          injection he' with _ hXa _
          subst a
          have hsum : IsSummand p X (trans A) :=
            Suffix_summand hsx _ _ (by rw [htr, hhp]; exact Or.inl ⟨rfl, rfl⟩)
          have hXA : X < trans A := hgood X (G1_summand_mem p p X (Nat.le_refl _) _ hsum)
          have hhead : T.P p X T.Z ≤ trans A :=
            partial_order.trans _ _ _ (summand_le_head _ _ _ hAnf hsum) (head_le_self _)
          apply (trans_lt_iff _ _ hcnf hA).mpr
          by_cases hp0 : p = 0
          · subst hp0
            cases lam with
            | zero => exact i.elim0
            | succ k =>
                have hX := aux_head_countable w X he
                have hi0 : i = ⟨0, Nat.zero_lt_succ k⟩ := Fin.eq_of_val_eq hi
                rw [hi0, ← hX]
                exact hXA
          · have hcon := ((aux_contr_G1 p w).2 p X he).2.2 i hi (Nat.pos_of_ne_zero hp0)
            simp only [TopContr, hp0, ite_false] at hcon
            have hle1 := partial_order.trans _ _ _
              (card_times_self_le p _ (one_del_NF _ hcnf1)) hcon
            cases htc : trans (w.idx i) with
            | Z => exact lt_of_le_of_lt_thm T _ _ _ (T.Z_le _) hXA
            | P q d e =>
                rw [htc] at hle1
                cases q with
                | zero =>
                    cases d with
                    | Z =>
                        exact lt_of_lt_of_le_thm T _ _ _
                          (T.Lt.p_head _ _ _ _ _ _ (Nat.pos_of_ne_zero hp0)) hhead
                    | P _ _ _ => exact lt_of_le_of_lt_thm T _ _ _ hle1 hXA
                | succ q => exact lt_of_le_of_lt_thm T _ _ _ hle1 hXA
        · have hj : u < headIdx w := by rw [hhp]; exact hp
          apply prefixArg (new.T.P w b) hsx w b rfl hj
          have hlt := new.Vec.idx_size_lt w i
          simp only [srcPart, hj, ite_true, new.T.size]
          omega
    | tail w b c'' _ ih =>
        intro hceq hsx
        exact ih hceq (Suffix_tail hsx)
    | deep w b c'' i hi hr _ =>
        intro hceq hsx
        subst hceq
        obtain ⟨p, a, he, _⟩ := aux_principal w
        have hhp := headIdx_eq w p a he
        have hne' : w.idx i ≠ new.T.Z := Reach_ne_Z u hr
        have hip : i.val ≤ p := Nat.le_of_not_gt fun h => hne' (aux_above_zero w p a he i h)
        have hsz := Reach_size u hr
        have hj : u < headIdx w := by rw [hhp]; omega
        apply prefixArg (new.T.P w b) hsx w b rfl hj
        have hlt := new.Vec.idx_size_lt w i
        simp only [srcPart, hj, ite_true, new.T.size]
        omega
  exact main A c hc rfl (.refl A)

/-- Buchholz goodness of the translation implies indexed goodness of the source. -/
theorem reverse_transfer {lam : Nat} (u : Nat) (A : new.T lam) (hA : new.T.isNF A)
    (hg : ∀ y ∈ T.G1 u (trans A), y < trans A) : new.T.isNFComp u A := by
  obtain ⟨k, hk⟩ : ∃ k, lam - u = k := ⟨_, rfl⟩
  induction k generalizing u with
  | zero => exact new.T.isNFComp_above_dim u (by omega) A hA
  | succ k ih =>
      have h1 := ih (u + 1) (fun y hy => hg y (G1_antitone u (u + 1) (Nat.le_succ u) _ y hy))
        (by omega)
      refine ⟨hA, fun z hz => ?_⟩
      rcases Gi_split u A z hz with h | ⟨c, hc, hzc⟩
      · exact h1.2 z h
      · have hclt := reach_lt u A hA hg c hc
        rcases hzc with rfl | hzc
        · exact hclt
        · exact strict_partial_order.trans _ _ _ ((Reach_comp u hc hA).1.2 z hzc) hclt

end LegacyTranslation

-- Merged from Subsp/old/stop_inverse_target.lean
/-! Target-side inverses of early collapse, cardinal multiplication and `one_del`. -/

namespace LegacyTranslation

open T

/-- Inverse of `early_collapse q` on terms of index at most `q`. -/
def UE (q : Nat) : T → T
  | .Z => .Z
  | .P p h t =>
      if p = q then
        if (T.part q h).1 = .Z then .P p h t
        else if (T.part q h).2 = .Z then T.add h t
        else T.add (T.part q h).1 (.P p h t)
      else .P p h t

/-- Inverse of `cardArg K` on a single argument. -/
def uncardArg (K : Nat) (g : T) : Nat × T :=
  if T.P K (T.P 0 .Z .Z) .Z ≤ g then (K, g) else
  match g with
  | .Z => (0, .Z)
  | .P q h t =>
      if q = K then (K, t)
      else if q = 0 then (0, UE 0 g)
      else if h = .Z then (q, UE q t)
      else (q, UE q g)

/-- Inverse of `card_times K` on terms of index at least `K`. -/
def UC (K : Nat) : T → T
  | .Z => .Z
  | .P q g r =>
      if K < q then .P q g (UC K r) else .P (uncardArg K g).1 (uncardArg K g).2 (UC K r)

/-- Inverse of `one_del`, avoiding a leading unit. -/
def lpInv : T → T
  | .Z => .P 0 .Z .Z
  | .P 0 .Z r => .P 0 .Z (.P 0 .Z r)
  | e => e

/-- All indices occurring anywhere in a target term are at most `l`. -/
def DeepIdx (l : Nat) : T → Prop
  | .Z => True
  | .P p a r => p ≤ l ∧ DeepIdx l a ∧ DeepIdx l r

/-- Nesting depth of a target term. -/
def degree : T → Nat
  | .Z => 0
  | .P _ a r => max (degree a + 1) (degree r)

theorem one_del_lpInv (e : T) : T.one_del (lpInv e) = e := by
  match e with
  | .Z | .P 0 .Z _ | .P 0 (.P _ _ _) _ | .P (_ + 1) _ _ => rfl

/-! Parts. -/

theorem part_snd_of_fst_Z (n : Nat) : ∀ b : T, (T.part n b).1 = T.Z → (T.part n b).2 = b
  | .Z, _ => rfl
  | .P p a r, h => by
      by_cases hp : p ≤ n
      · simp only [T.part, hp, ite_true] at h ⊢
        rw [part_snd_of_fst_Z n r h]
      · simp only [T.part, hp, ite_false] at h
        cases h

theorem part_add_split (n : Nat) (a b : T) (ha : T.part n a = (a, T.Z))
    (hb : (T.part n b).1 = T.Z) : T.part n (T.add a b) = (a, b) := by
  rw [part_add_distrib, ha, hb, part_snd_of_fst_Z n b hb, T.add_Z, zero_add]

theorem DeepIdx_add (l : Nat) (a b : T) (ha : DeepIdx l a) (hb : DeepIdx l b) :
    DeepIdx l (T.add a b) := by
  induction a with
  | Z => exact hb
  | P p x r _ ih => rw [T.P_add_eq]; exact ⟨ha.1, ha.2.1, ih ha.2.2⟩

theorem part_props (l n : Nat) : ∀ t : T,
    degree (T.part n t).1 ≤ degree t ∧ degree (T.part n t).2 ≤ degree t ∧
      (DeepIdx l t → DeepIdx l (T.part n t).1 ∧ DeepIdx l (T.part n t).2)
  | .Z => ⟨Nat.le_refl _, Nat.le_refl _, fun _ => ⟨trivial, trivial⟩⟩
  | .P p a r => by
      obtain ⟨ih1, ih2, ih3⟩ := part_props l n r
      by_cases hpn : p ≤ n
      · simp only [T.part, hpn, ite_true, degree]
        exact ⟨Nat.le_trans ih1 (Nat.le_max_right _ _),
          Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans ih2 (Nat.le_max_right _ _)⟩,
          fun ⟨hp, ha, hr⟩ => ⟨(ih3 hr).1, hp, ha, (ih3 hr).2⟩⟩
      · simp only [T.part, hpn, ite_false, degree]
        exact ⟨Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans ih1 (Nat.le_max_right _ _)⟩,
          Nat.le_trans ih2 (Nat.le_max_right _ _),
          fun ⟨hp, ha, hr⟩ => ⟨⟨hp, ha, (ih3 hr).1⟩, (ih3 hr).2⟩⟩

theorem degree_add (a b : T) : degree (T.add a b) = max (degree a) (degree b) := by
  induction a with
  | Z => simp [T.add, degree]
  | P p x r _ ih => rw [T.P_add_eq]; simp only [degree, ih, Nat.max_assoc]

theorem add_NF1_split (n : Nat) : ∀ a b : T, T.isNF1 a → T.isNF1 b →
    (∀ p c, IsSummand p c a → n < p) → T.index_Prop1 n b → T.isNF1 (T.add a b)
  | .Z, b, _, hb, _, _ => hb
  | .P p x r, b, ha, hb, hsum, hib => by
      obtain ⟨hx, hr, hg, hh⟩ := T.isNF1_P_inv p x r ha
      rw [T.P_add_eq]
      refine .p p x _ hx (add_NF1_split n r b hr hb (fun p' c hs => hsum p' c (Or.inr hs)) hib) hg ?_
      cases r with
      | Z =>
          simp only [zero_add]
          cases hib with
          | z => exact T.Z_le _
          | p q d e hq _ =>
              exact Or.inl (T.Lt.p_head _ _ _ _ _ _
                (Nat.lt_of_le_of_lt hq (hsum p x (Or.inl ⟨rfl, rfl⟩))))
      | P q d e => rw [T.head_add_ne_Z]; exact hh

theorem part_fst_summand_gt (q : Nat) : ∀ h : T, ∀ p c, IsSummand p c (T.part q h).1 → q < p
  | .Z, _, _, hs => hs.elim
  | .P p' a r, p, c, hs => by
      by_cases hp : p' ≤ q
      · simp only [T.part, hp, ite_true] at hs
        exact part_fst_summand_gt q r p c hs
      · simp only [T.part, hp, ite_false] at hs
        rcases hs with ⟨rfl, _⟩ | hs
        · omega
        · exact part_fst_summand_gt q r p c hs

theorem G1_below_head (q : Nat) (h : T) (hh : ∀ x ∈ T.G1 q h, x < h) : ∀ t : T, T.isNF1 t →
    T.head t ≤ T.P q h T.Z → T.index_Prop1 q t → ∀ x ∈ T.G1 q t, x ≤ h
  | .Z, _, _, _, x, hx => by cases hx
  | .P p g r, ht, hth, hti, x, hx => by
      obtain ⟨hg, hr, hgg, hrh⟩ := T.isNF1_P_inv p g r ht
      have hp : p ≤ q := by cases hti with | p _ _ _ h1 _ => exact h1
      have hri : T.index_Prop1 q r := by cases hti with | p _ _ _ _ h1 => exact h1
      have hrh2 : T.head r ≤ T.P q h T.Z := partial_order.trans _ _ _ hrh hth
      rcases Nat.eq_or_lt_of_le hp with rfl | hpq
      · have hgh : g ≤ h := by
          rcases hth with hlt | heq
          · cases hlt with
            | p_head _ _ _ _ _ _ h1 => exact False.elim (Nat.lt_irrefl _ h1)
            | p_mid _ _ _ _ _ h1 => exact Or.inl h1
            | p_tail _ _ _ _ h1 => cases h1
          · injection heq with _ h2 _; exact Or.inr h2
        simp only [T.G1, Nat.le_refl, ite_true, List.mem_append, List.mem_singleton] at hx
        rcases hx with (rfl | hx) | hx
        · exact hgh
        · exact Or.inl (lt_of_lt_of_le_thm T _ _ _ (hgg x hx) hgh)
        · exact G1_below_head p h hh r hr hrh2 hri x hx
      · simp only [T.G1, show ¬ q ≤ p by omega, ite_false] at hx
        exact G1_below_head q h hh r hr hrh2 hri x hx

/-! Uncollapse. -/

theorem UE_props (q : Nat) (e : T) (he : T.isNF1 e) (hi : T.index_Prop1 q e) :
    T.early_collapse q (UE q e) = e ∧ T.isNF1 (UE q e) ∧ (∀ x ∈ T.G1 q (UE q e), x < UE q e) ∧
      degree (UE q e) ≤ degree e ∧ ∀ l, DeepIdx l e → DeepIdx l (UE q e) := by
  cases e with
  | Z => exact ⟨rfl, .z, fun x hx => (by cases hx), Nat.le_refl _, fun _ h => h⟩
  | P p h t =>
      obtain ⟨hh, ht, hgh, hth⟩ := T.isNF1_P_inv p h t he
      have hp : p ≤ q := by cases hi with | p _ _ _ h1 _ => exact h1
      have hti : T.index_Prop1 q t := by cases hi with | p _ _ _ _ h1 => exact h1
      have htlow : (T.part q t).1 = T.Z := by rw [part_of_index q t hti]
      by_cases hpq : p = q
      · subst hpq
        have htb := G1_below_head p h hgh t ht hth hti
        have hpe := part_add p h hh
        by_cases hH : (T.part p h).1 = T.Z
        · simp only [UE, hH, ite_true]
          have hhi : T.index_Prop1 p h := by
            have := part_second_index p h
            rwa [part_snd_of_fst_Z p h hH] at this
          have hhlt : h < T.P p h t := good_index_lt_wrap p h t hhi hgh
          refine ⟨early_collapse_of_index p _ hi, he, fun x hx => ?_, Nat.le_refl _, fun _ h => h⟩
          simp only [T.G1, Nat.le_refl, ite_true, List.mem_append, List.mem_singleton] at hx
          rcases hx with (rfl | hx) | hx
          · exact hhlt
          · exact lt_trans_thm _ _ _ (hgh x hx) hhlt
          · exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) hhlt
        · have hd := part_props 0 p h
          by_cases hL : (T.part p h).2 = T.Z
          · simp only [UE, hH, hL, ite_true, ite_false]
            have hh1 : (T.part p h).1 = h := by rw [hL, T.add_Z] at hpe; exact hpe
            refine ⟨?_, add_NF1_split p h t hh ht (fun p' c hs =>
              part_fst_summand_gt p h p' c (by rw [hh1]; exact hs)) hti, fun x hx => ?_, ?_,
              fun l hl => DeepIdx_add l h t hl.2.1 hl.2.2⟩
            · have hhZ : h ≠ T.Z := by rw [← hh1]; exact hH
              simp only [T.early_collapse, part_add_split p h t (Prod.ext hh1 hL) htlow, hhZ,
                ite_false]
              rw [T.stand, stand_eq_self t ht]
              simp only [hth, ite_true]
            · rw [G1_add, List.mem_append] at hx
              rcases hx with hx | hx
              · exact lt_of_lt_of_le_thm T _ _ _ (hgh x hx) (add_self_le h t)
              · have htZ : t ≠ T.Z := by intro h1; subst h1; cases hx
                exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) (add_lt_add_of_ne_Z h t htZ)
            · rw [degree_add]
              simp only [degree]
              exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_succ _) (Nat.le_max_left _ _),
                Nat.le_max_right _ _⟩
          · simp only [UE, hH, hL, ite_true, ite_false]
            have hhlt : h < T.add (T.part p h).1 (T.P p h t) := by
              have := add_left_lt (T.part p h).1 _ _ (part_snd_lt_wrap p h t hh hgh)
              rwa [hpe] at this
            refine ⟨?_, add_NF1_split p _ _ (part_NF p h hh).1 he (part_fst_summand_gt p h) hi,
              fun x hx => ?_, ?_, fun l hl => DeepIdx_add l _ _ ((part_props l p h).2.2 hl.2.1).1 hl⟩
            · have hPlow : (T.part p (T.P p h t)).1 = T.Z := by
                simp only [T.part, Nat.le_refl, ite_true]; exact htlow
              simp only [T.early_collapse, part_add_split p _ _ (part_first_fixed p h) hPlow, hH,
                ite_false]
              rw [T.stand, stand_eq_self _ he]
              have hlt : (T.part p h).1 < h := by
                have hlt := add_lt_add_of_ne_Z (T.part p h).1 (T.part p h).2 hL
                rwa [hpe] at hlt
              have hnot : ¬ T.head (T.P p h t) ≤ T.P p (T.part p h).1 T.Z := fun hle =>
                lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _ (T.Lt.p_mid _ _ _ _ _ hlt) hle)
              simp only [hnot, ite_false]
            · rw [G1_add, List.mem_append] at hx
              rcases hx with hx | hx
              · exact lt_trans_thm _ _ _ (hgh x (G1_part_fst_subset p p h hh x hx)) hhlt
              · simp only [T.G1, Nat.le_refl, ite_true, List.mem_append, List.mem_singleton] at hx
                rcases hx with (rfl | hx) | hx
                · exact hhlt
                · exact lt_trans_thm _ _ _ (hgh x hx) hhlt
                · exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) hhlt
            · rw [degree_add]
              simp only [degree]
              exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_trans hd.1 (Nat.le_succ _))
                (Nat.le_max_left _ _), Nat.le_refl _⟩
      · simp only [UE, hpq, ite_false]
        refine ⟨early_collapse_of_index q _ hi, he, fun x hx => ?_, Nat.le_refl _, fun _ h => h⟩
        have htp : T.index_Prop1 p t := by
          cases t with
          | Z => exact .z
          | P p2 g2 r2 => exact isNF1_index p p2 g2 r2 ht (head_le_index p2 p g2 h hth)
        simp only [T.G1, show ¬ q ≤ p by omega, ite_false] at hx
        rw [index_Prop1_G1_empty p t htp q (by omega)] at hx
        cases hx

/-! Uncarding arguments. -/

theorem small_head_shape (K : Nat) (q : Nat) (h t : T)
    (hlt : T.P q h t < T.P K (T.P 0 T.Z T.Z) T.Z) : q < K ∨ (q = K ∧ h = T.Z) := by
  cases hlt with
  | p_head _ _ _ _ _ _ hq => exact Or.inl hq
  | p_mid _ _ _ _ _ hh => exact Or.inr ⟨rfl, lt_one_eq_Z h hh⟩
  | p_tail _ _ _ _ ht => cases ht

theorem uncard_props (K : Nat) (hK : 0 < K) (g : T) (hg : T.isNF1 g)
    (hgg : ∀ x ∈ T.G1 K g, x < g) :
    cardArg K (uncardArg K g).1 (uncardArg K g).2 = g ∧ (uncardArg K g).1 ≤ K ∧
      T.isNF1 (uncardArg K g).2 ∧
      (∀ x ∈ T.G1 (uncardArg K g).1 (uncardArg K g).2, x < (uncardArg K g).2) ∧
      degree (uncardArg K g).2 ≤ degree g ∧ (∀ l, DeepIdx l g → DeepIdx l (uncardArg K g).2) := by
  unfold uncardArg
  split
  · rename_i hle
    refine ⟨?_, Nat.le_refl _, hg, hgg, Nat.le_refl _, fun _ h => h⟩
    unfold cardArg
    rw [ite_eq_right (Nat.lt_irrefl K), ite_eq_right]
    intro ⟨_, hlt⟩
    rcases hle with hle | hle
    · exact lt_asymm_thm hlt hle
    · rw [hle] at hlt; exact lt_irrefl_thm _ hlt
  · rename_i hnle
    have hlt := lt_of_not_le _ _ hnle
    cases g with
    | Z =>
        exact ⟨by simp only [cardArg, hK, ite_true]; rfl, Nat.zero_le _, .z,
          fun x hx => (by simp [T.G1] at hx), Nat.le_refl _, fun _ _ => trivial⟩
    | P q h t =>
        obtain ⟨hh, ht, _, hth⟩ := T.isNF1_P_inv q h t hg
        rcases small_head_shape K q h t hlt with hqK | ⟨rfl, rfl⟩
        · have hgi : T.index_Prop1 q (T.P q h t) := isNF1_index q q h t hg (Nat.le_refl q)
          have hti : T.index_Prop1 q t := by cases hgi with | p _ _ _ _ h1 => exact h1
          simp only [show q ≠ K by omega, ite_false]
          by_cases hq0 : q = 0
          · subst hq0
            obtain ⟨h1, h2, h3, h4, h5⟩ := UE_props 0 _ hg hgi
            simp only [ite_true]
            exact ⟨by simp only [cardArg, hqK, ite_true]; exact h1, Nat.zero_le _, h2, h3, h4, h5⟩
          · by_cases hh0 : h = T.Z
            · subst hh0
              obtain ⟨h1, h2, h3, h4, h5⟩ := UE_props q t ht hti
              simp only [hq0, ite_true, ite_false]
              refine ⟨?_, Nat.le_of_lt hqK, h2, h3, Nat.le_trans h4 (Nat.le_max_right _ _),
                fun l hl => h5 l hl.2.2⟩
              simp only [cardArg, hqK, hq0, ite_true, ite_false]
              rw [h1, T.stand, stand_eq_self t ht]
              simp only [hth, ite_true]
            · obtain ⟨h1, h2, h3, h4, h5⟩ := UE_props q _ hg hgi
              simp only [hq0, hh0, ite_false]
              refine ⟨?_, Nat.le_of_lt hqK, h2, h3, h4, h5⟩
              simp only [cardArg, hqK, hq0, ite_true, ite_false]
              rw [h1, T.stand, stand_eq_self _ hg]
              have hnot : ¬ T.head (T.P q h t) ≤ T.P q T.Z T.Z := by
                intro hle
                have hZh : T.Z < h := by
                  cases h with
                  | Z => exact False.elim (hh0 rfl)
                  | P _ _ _ => exact T.Lt.Z_lt_P _ _ _
                exact lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _ (T.Lt.p_mid _ _ _ _ _ hZh) hle)
              simp only [hnot, ite_false]
        · have hlt1 : t < T.P q (T.P 0 T.Z T.Z) T.Z := by
            cases t with
            | Z => exact T.Lt.Z_lt_P _ _ _
            | P p2 g2 r2 =>
                rcases hth with hth | hth
                · cases hth with
                  | p_head _ _ _ _ _ _ h1 => exact T.Lt.p_head _ _ _ _ _ _ h1
                  | p_mid _ _ _ _ _ h1 => exact absurd h1 lt_Z_inv
                  | p_tail _ _ _ _ h1 => cases h1
                · injection hth with h1 h2 _
                  subst h1; subst h2
                  exact T.Lt.p_mid _ _ _ _ _ (T.Lt.Z_lt_P _ _ _)
          have hti : T.index_Prop1 q t := by
            cases t with
            | Z => exact .z
            | P p2 g2 r2 => exact isNF1_index q p2 g2 r2 ht (head_le_index p2 q g2 T.Z hth)
          have htZ : ∀ x ∈ T.G1 q t, x < t := by
            intro x hx
            rcases G1_below_head q T.Z (fun y hy => by cases hy) t ht hth hti x hx with h | rfl
            · exact absurd h lt_Z_inv
            · cases t with
              | Z => cases hx
              | P _ _ _ => exact T.Lt.Z_lt_P _ _ _
          simp only [ite_true]
          refine ⟨?_, Nat.le_refl _, ht, htZ, Nat.le_max_right _ _, fun _ hl => hl.2.2⟩
          simp only [cardArg, Nat.lt_irrefl, ite_false]
          simp only [hlt1, and_self, ite_true]

theorem uncard_mono (K : Nat) (hK : 0 < K) (g1 g2 : T) (hg1 : T.isNF1 g1)
    (hgg1 : ∀ x ∈ T.G1 K g1, x < g1) (hg2 : T.isNF1 g2) (hgg2 : ∀ x ∈ T.G1 K g2, x < g2)
    (h : g2 ≤ g1) : T.P (uncardArg K g2).1 (uncardArg K g2).2 T.Z ≤
      T.P (uncardArg K g1).1 (uncardArg K g1).2 T.Z := by
  obtain ⟨he1, hp1, hc1, hgc1, _⟩ := uncard_props K hK g1 hg1 hgg1
  obtain ⟨he2, hp2, hc2, hgc2, _⟩ := uncard_props K hK g2 hg2 hgg2
  rcases lt_total_thm (T.P (uncardArg K g2).1 (uncardArg K g2).2 T.Z)
      (T.P (uncardArg K g1).1 (uncardArg K g1).2 T.Z) with hlt | hlt | heq
  · exact Or.inl hlt
  · exfalso
    have hg12 : g1 < g2 := by
      rcases lt_inv _ _ _ _ _ _ hlt with hp | ⟨hp, hc⟩ | ⟨_, _, hz⟩
      · have := card_heads_lt K _ _ _ _ T.Z T.Z hp hc1 hgc1 hc2 hgc2
        rw [Nat.max_eq_right hp1, Nat.max_eq_right hp2, he1, he2] at this
        rcases lt_inv _ _ _ _ _ _ this with h1 | ⟨_, h1⟩ | ⟨_, _, h1⟩
        · exact absurd h1 (Nat.lt_irrefl _)
        · exact h1
        · exact absurd h1 lt_Z_inv
      · rw [← hp] at he2 hgc2
        have hc3 := cardArg_lt_same K (uncardArg K g1).1 _ _ hc1 hgc1 hc2 hgc2 hc
        rwa [he1, he2] at hc3
      · exact absurd hz lt_Z_inv
    rcases h with h | h
    · exact lt_asymm_thm h hg12
    · rw [h] at hg12; exact lt_irrefl_thm _ hg12
  · exact Or.inr heq

/-! Uncarding sums. -/

theorem UC_add (K : Nat) : ∀ H L : T, (∀ p c, IsSummand p c H → K < p) →
    UC K (T.add H L) = T.add H (UC K L)
  | .Z, L, _ => by simp [T.add]
  | .P q g r, L, hH => by
      rw [T.P_add_eq, T.P_add_eq]
      simp only [UC, hH q g (Or.inl ⟨rfl, rfl⟩), ite_true]
      rw [UC_add K r L (fun p c hs => hH p c (Or.inr hs))]

theorem UC_props (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    degree (UC K d) ≤ degree d ∧ ∀ l, K ≤ l → DeepIdx l d → DeepIdx l (UC K d)
  | .Z, _ => ⟨Nat.le_refl _, fun _ _ _ => trivial⟩
  | .P q g r, hd => by
      obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
      obtain ⟨ih1, ih2⟩ := UC_props K hK r hr
      simp only [UC]
      split
      · simp only [degree]
        exact ⟨Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans ih1 (Nat.le_max_right _ _)⟩,
          fun l hl ⟨hql, hgl, hrl⟩ => ⟨hql, hgl, ih2 l hl hrl⟩⟩
      · rename_i hq
        obtain ⟨-, hp, -, -, hdeg, hdi⟩ :=
          uncard_props K hK g hg fun x hx => hgg x (G1_antitone q K (by omega) g x hx)
        simp only [degree]
        exact ⟨Nat.max_le.mpr ⟨Nat.le_trans (Nat.succ_le_succ hdeg) (Nat.le_max_left _ _),
          Nat.le_trans ih1 (Nat.le_max_right _ _)⟩,
          fun l hl ⟨_, hgl, hrl⟩ => ⟨Nat.le_trans hp hl, hdi l hgl, ih2 l hl hrl⟩⟩

theorem UC_spec (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → K ≤ p) → T.card_times K (UC K d) = d
  | .Z, _, _ => rfl
  | .P q g r, hd, hidx => by
      obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
      have ih := UC_spec K hK r hr (fun p c hs => hidx p c (Or.inr hs))
      have hKq := hidx q g (Or.inl ⟨rfl, rfl⟩)
      simp only [UC]
      split
      · rename_i hq
        rw [card_times_P, Nat.max_eq_left (Nat.le_of_lt hq), ih]
        unfold cardArg
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · rename_i hq
        obtain rfl : q = K := by omega
        obtain ⟨he, hp, -⟩ := uncard_props q hK g hg hgg
        rw [card_times_P, Nat.max_eq_right hp, he, ih]

/-- The head summand produced by uncarding. -/
def ucHead (K q : Nat) (g : T) : Nat × T := if K < q then (q, g) else uncardArg K g

theorem UC_P (K q : Nat) (g r : T) :
    UC K (T.P q g r) = T.P (ucHead K q g).1 (ucHead K q g).2 (UC K r) := by
  simp only [UC, ucHead]
  split <;> rfl

theorem UC_NF (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → K ≤ p) → T.isNF1 (UC K d)
  | .Z, _, _ => .z
  | .P q g r, hd, hidx => by
      have hprops (q : Nat) (g : T) (hg : T.isNF1 g) (hgg : ∀ x ∈ T.G1 q g, x < g)
          (hKq : K ≤ q) : T.isNF1 (ucHead K q g).2 ∧
            ∀ x ∈ T.G1 (ucHead K q g).1 (ucHead K q g).2, x < (ucHead K q g).2 := by
        unfold ucHead
        split
        · exact ⟨hg, hgg⟩
        · obtain rfl : q = K := by omega
          obtain ⟨-, -, h1, h2, -⟩ := uncard_props q hK g hg hgg
          exact ⟨h1, h2⟩
      obtain ⟨hg, hr, hgg, hrh⟩ := T.isNF1_P_inv q g r hd
      have hKq := hidx q g (Or.inl ⟨rfl, rfl⟩)
      obtain ⟨hc, hgc⟩ := hprops q g hg hgg hKq
      rw [UC_P]
      refine .p _ _ _ hc (UC_NF K hK r hr (fun p c hs => hidx p c (Or.inr hs))) hgc ?_
      cases r with
      | Z => exact T.Z_le _
      | P q2 g2 r2 =>
          obtain ⟨hg2, _, hgg2, _⟩ := T.isNF1_P_inv q2 g2 r2 hr
          have hK2 := hidx q2 g2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
          rw [UC_P]
          have hq21 := head_le_index q2 q g2 g hrh
          unfold ucHead
          by_cases h2 : K < q2
          · rw [ite_eq_left h2, ite_eq_left (Nat.lt_of_lt_of_le h2 hq21)]
            exact hrh
          · rw [ite_eq_right h2]
            obtain rfl : q2 = K := by omega
            have hp2 := (uncard_props q2 hK g2 hg2 hgg2).2.1
            by_cases h1 : q2 < q
            · rw [ite_eq_left h1]
              exact Or.inl (T.Lt.p_head _ _ _ _ _ _ (Nat.lt_of_le_of_lt hp2 h1))
            · rw [ite_eq_right h1]
              obtain rfl : q = q2 := by omega
              apply uncard_mono q hK g g2 hg hgg hg2 hgg2
              rcases hrh with h | h
              · cases h with
                | p_head _ _ _ _ _ _ h' => exact absurd h' (Nat.lt_irrefl _)
                | p_mid _ _ _ _ _ h' => exact Or.inl h'
                | p_tail _ _ _ _ h' => cases h'
              · injection h with _ h' _; exact Or.inr h'

theorem UC_index (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → p = K) → T.index_Prop1 K (UC K d)
  | .Z, _, _ => .z
  | .P q g r, hd, hidx => by
      obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
      obtain rfl := hidx q g (Or.inl ⟨rfl, rfl⟩)
      simp only [UC, Nat.lt_irrefl, ite_false]
      exact .p _ _ _ (uncard_props q hK g hg hgg).2.1
        (UC_index q hK r hr (fun p c hs => hidx p c (Or.inr hs)))

/-! Nested parts. -/

theorem part_part (n m : Nat) (hnm : n ≤ m) : ∀ s : T,
    (T.part m (T.part n s).1).1 = (T.part m s).1 ∧ (T.part n (T.part m s).2).2 = (T.part n s).2 ∧
      (T.part m (T.part n s).1).2 = (T.part n (T.part m s).2).1
  | .Z => ⟨rfl, rfl, rfl⟩
  | .P p a r => by
      obtain ⟨ih1, ih2, ih3⟩ := part_part n m hnm r
      by_cases hpn : p ≤ n
      · simp only [T.part, hpn, Nat.le_trans hpn hnm, ite_true, ih1, ih2, ih3, and_self]
      · by_cases hpm : p ≤ m
        · simp only [T.part, hpn, hpm, ite_true, ite_false, ih1, ih2, ih3, and_self]
        · simp only [T.part, hpn, hpm, ite_false, ih1, ih2, ih3, and_self]

/-- Summands of index exactly `m`. -/
def idxPart (m : Nat) (c : T) : T := (T.part (m - 1) (T.part m c).2).1

theorem part_snd_split (m : Nat) (c : T) (hc : T.isNF1 c) :
    (T.part m c).2 = T.add (idxPart m c) (T.part (m - 1) c).2 := by
  have := part_add (m - 1) _ (part_NF m c hc).2
  rw [(part_part (m - 1) m (Nat.sub_le m 1) c).2.1] at this
  exact this.symm

/-! Goodness of the uncarded top piece. -/

theorem IsSummand_add_right (p : Nat) (c : T) : ∀ H L : T, IsSummand p c L →
    IsSummand p c (T.add H L)
  | .Z, L, h => h
  | .P q a r, L, h => by rw [T.P_add_eq]; exact Or.inr (IsSummand_add_right p c r L h)

theorem uncard_top_cases (K : Nat) (hK : 0 < K) (g : T) (hp : (uncardArg K g).1 = K) :
    ((uncardArg K g).2 = g ∧ T.P K (T.P 0 T.Z T.Z) T.Z ≤ g) ∨
      (∃ t, g = T.P K T.Z t ∧ (uncardArg K g).2 = t) := by
  unfold uncardArg at hp ⊢
  by_cases hle : T.P K (T.P 0 T.Z T.Z) T.Z ≤ g
  · rw [ite_eq_left hle]
    exact Or.inl ⟨rfl, hle⟩
  · rw [ite_eq_right hle] at hp ⊢
    cases g with
    | Z => exact absurd hp (Nat.ne_of_lt hK)
    | P q h t =>
        dsimp only at hp ⊢
        rcases small_head_shape K q h t (lt_of_not_le _ _ hle) with hqK | ⟨rfl, rfl⟩
        · exfalso
          rw [ite_eq_right (Nat.ne_of_lt hqK)] at hp
          split at hp <;> (try split at hp) <;> simp only at hp <;> omega
        · rw [ite_eq_left rfl]
          exact Or.inr ⟨t, rfl, rfl⟩

theorem summands_of_part_fst (n : Nat) : ∀ c : T, ∀ p a, IsSummand p a (T.part n c).1 →
    IsSummand p a c
  | .Z, _, _, h => h
  | .P q b r, p, a, h => by
      by_cases hq : q ≤ n
      · simp only [T.part, hq, ite_true] at h
        exact Or.inr (summands_of_part_fst n r p a h)
      · simp only [T.part, hq, ite_false] at h
        rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (summands_of_part_fst n r p a h)

theorem summands_of_part_snd (n : Nat) : ∀ c : T, ∀ p a, IsSummand p a (T.part n c).2 →
    IsSummand p a c ∧ p ≤ n
  | .Z, _, _, h => h.elim
  | .P q b r, p, a, h => by
      by_cases hq : q ≤ n
      · simp only [T.part, hq, ite_true] at h
        rcases h with ⟨rfl, rfl⟩ | h
        · exact ⟨Or.inl ⟨rfl, rfl⟩, hq⟩
        · exact (summands_of_part_snd n r p a h).imp_left Or.inr
      · simp only [T.part, hq, ite_false] at h
        exact (summands_of_part_snd n r p a h).imp_left Or.inr

theorem UC_summand_inv (K : Nat) : ∀ L : T, ∀ p c, IsSummand p c (UC K L) →
    ∃ q g, IsSummand q g L ∧ ucHead K q g = (p, c)
  | .Z, _, _, h => h.elim
  | .P q g r, p, c, h => by
      rw [UC_P] at h
      rcases h with ⟨h1, h2⟩ | h
      · exact ⟨q, g, Or.inl ⟨rfl, rfl⟩, by rw [← h1, ← h2]⟩
      · obtain ⟨q2, g2, hs, he⟩ := UC_summand_inv K r p c h
        exact ⟨q2, g2, Or.inr hs, he⟩

theorem UC_top_good_core (K : Nat) (hK : 0 < K) (c H Ld : T) (hc : T.isNF1 c)
    (hgc : ∀ x ∈ T.G1 K c, x < c)
    (hH : (T.part K c).1 = H) (hHNF : T.isNF1 H) (hHfix : T.part K H = (H, T.Z))
    (hce : T.add H (T.part K c).2 = c)
    (hLdidx : ∀ p a, IsSummand p a Ld → p = K) (hLdc : ∀ p a, IsSummand p a Ld → IsSummand p a c)
    (hUNF : T.isNF1 (UC K Ld)) (heNF : T.isNF1 (T.add H (UC K Ld))) :
    ∀ x ∈ T.G1 K (T.add H (UC K Ld)), x < T.add H (UC K Ld) := by
  have hHle : H ≤ T.add H (UC K Ld) := add_self_le _ _
  have hargs : SumAll (fun p c' => K ≤ p → c' < T.add H (UC K Ld) ∧
      ∀ y ∈ T.G1 K c', y < T.add H (UC K Ld)) (UC K Ld) := by
    apply SumAll_of_summand
    intro p c' hs hKp
    obtain ⟨q, g, hsq, hqg⟩ := UC_summand_inv K Ld p c' hs
    have hqK := hLdidx q g hsq
    subst hqK
    have hgc0 := hLdc q g hsq
    obtain ⟨hg, hgg⟩ := IsSummand_NF q g c hc hgc0
    have hggK : g ∈ T.G1 q c := G1_summand_mem q q g (Nat.le_refl q) c hgc0
    simp only [ucHead, Nat.lt_irrefl, ite_false] at hqg
    obtain ⟨-, hp, _, hgc', _⟩ := uncard_props q hK g hg hgg
    rw [hqg] at hp hgc'
    simp only at hp hgc'
    have hpq : p = q := by omega
    subst hpq
    have hsumE : IsSummand p c' (T.add H (UC p Ld)) := IsSummand_add_right _ _ H _ hs
    have hpq' : (uncardArg p g).1 = p := by rw [hqg]
    have hlt : c' < T.add H (UC p Ld) := by
      rcases uncard_top_cases p hK g hpq' with ⟨hcg, _⟩ | ⟨t, hgt, hct⟩
      · rw [hqg] at hcg
        simp only at hcg
        subst hcg
        rcases part_lt_cases p c' c hg hc (hgc c' hggK) with h1 | ⟨h1, _⟩
        · rw [hH] at h1
          have : c' < H :=
            lt_of_part_lt_cases p c' H hg hHNF (Or.inl (by rw [hHfix]; exact h1))
          exact lt_of_lt_of_le_thm T _ _ _ this hHle
        · rw [hH] at h1
          have hgsplit : c' = T.add H (T.part p c').2 := by
            have := part_add p c' hg
            rw [h1] at this
            exact this.symm
          have hle : T.P p c' T.Z ≤ UC p Ld :=
            partial_order.trans _ _ _ (summand_le_head p c' _ hUNF hs) (head_le_self _)
          have hlow : (T.part p c').2 < UC p Ld :=
            lt_of_lt_of_le_thm T _ _ _ (part_snd_lt_wrap p c' _ hg hgg) hle
          rw [hgsplit]
          exact add_left_lt H _ _ hlow
      · rw [hqg] at hct
        simp only at hct
        subst hct
        subst hgt
        obtain ⟨_, ht, _, hth⟩ := T.isNF1_P_inv p T.Z c' hg
        have hti : T.index_Prop1 p c' := by
          cases c' with
          | Z => exact .z
          | P p2 g2 r2 => exact isNF1_index p p2 g2 r2 ht (head_le_index p2 p g2 T.Z hth)
        exact lt_of_lt_of_le_thm T _ _ _ (good_index_lt_wrap p c' T.Z hti hgc')
          (partial_order.trans _ _ _ (summand_le_head p c' _ heNF hsumE) (head_le_self _))
    exact ⟨hlt, fun y hy => lt_trans_thm _ _ _ (hgc' y hy) hlt⟩
  intro x hx
  rw [G1_add, List.mem_append] at hx
  rcases hx with hx | hx
  · have hxc := hgc x (G1_part_fst_subset K K c hc x (by rw [hH]; exact hx))
    have hHne : H ≠ T.Z := by intro h; rw [h] at hx; cases hx
    have hxH := lt_prefix_of_size_lt H _ x hHne (G1_size_lt K H x hx) (by rw [hce]; exact hxc)
    exact lt_of_lt_of_le_thm T _ _ _ hxH hHle
  · exact G1_of_SumAll K _ _ hargs x hx

/-- The top uncarded piece is good at its index. -/
theorem UC_top_good (K : Nat) (hK : 0 < K) (c : T) (hc : T.isNF1 c)
    (hgc : ∀ x ∈ T.G1 K c, x < c) :
    ∀ x ∈ T.G1 K (UC K (T.part (K - 1) c).1), x < UC K (T.part (K - 1) c).1 := by
  have hKK : K - 1 ≤ K := Nat.sub_le K 1
  have hdNF := (part_NF (K - 1) c hc).1
  have hdidx : ∀ p a, IsSummand p a (T.part (K - 1) c).1 → K ≤ p := by
    intro p a hs
    have := part_fst_summand_gt (K - 1) c p a hs
    omega
  have hd := part_add K _ hdNF
  rw [(part_part (K - 1) K hKK c).1, (part_part (K - 1) K hKK c).2.2] at hd
  have hHgt : ∀ p a, IsSummand p a (T.part K c).1 → K < p := part_fst_summand_gt K c
  have heq : UC K (T.part (K - 1) c).1 =
      T.add (T.part K c).1 (UC K (T.part (K - 1) (T.part K c).2).1) := by
    rw [← hd, UC_add K _ _ hHgt]
  have heNF := UC_NF K hK _ hdNF hdidx
  rw [heq] at heNF ⊢
  have hLdNF := (part_NF (K - 1) _ (part_NF K c hc).2).1
  have hLdidx : ∀ p a, IsSummand p a (T.part (K - 1) (T.part K c).2).1 → p = K := by
    intro p a hs
    have h1 := part_fst_summand_gt (K - 1) _ p a hs
    have h2 := (summands_of_part_snd K c p a (summands_of_part_fst (K - 1) _ p a hs)).2
    omega
  have hLdc : ∀ p a, IsSummand p a (T.part (K - 1) (T.part K c).2).1 → IsSummand p a c := by
    intro p a hs
    exact (summands_of_part_snd K c p a (summands_of_part_fst (K - 1) _ p a hs)).1
  have hUNF := UC_NF K hK _ hLdNF (fun p a hs => (hLdidx p a hs).symm ▸ Nat.le_refl K)
  exact UC_top_good_core K hK c _ _ hc hgc rfl (part_NF K c hc).1 (part_first_fixed K c)
    (part_add K c hc) hLdidx hLdc hUNF heNF

end LegacyTranslation
