import Subsp.old.stop_inverse_target

/-! Goodness of the uncarded top piece. -/

namespace LegacyTranslation

open T

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
    have hlt := lt_of_not_le _ _ hle
    cases g with
    | Z => simp at hp; omega
    | P q h t =>
        rcases small_head_shape K q h t hlt with hqK | ⟨rfl, rfl⟩
        · simp only [show q ≠ K by omega, ite_false] at hp ⊢
          by_cases hq0 : q = 0
          · simp only [hq0, ite_true] at hp; omega
          · by_cases hh0 : h = T.Z
            · simp only [hq0, hh0, ite_true, ite_false] at hp; omega
            · simp only [hq0, hh0, ite_false] at hp; omega
        · simp only [ite_true]
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
    obtain ⟨hp, _, hgc', _⟩ := uncard_props q hK g hg hgg
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
            lt_of_lt_of_le_thm T _ _ _ (part_snd_lt_wrap p c' hgg) hle
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
  rw [part_part_fst (K - 1) K hKK, part_comm (K - 1) K hKK] at hd
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
