import Subsp.old.stop_reverse_main

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
