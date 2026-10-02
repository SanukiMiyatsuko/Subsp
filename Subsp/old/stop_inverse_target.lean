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

theorem one_del_lpInv (e : T) : T.one_del (lpInv e) = e := by
  cases e with
  | Z => rfl
  | P p h t =>
      cases p with
      | zero => cases h <;> rfl
      | succ p => rfl

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

theorem DeepIdx_part (l n : Nat) : ∀ t : T, DeepIdx l t →
    DeepIdx l (T.part n t).1 ∧ DeepIdx l (T.part n t).2
  | .Z, _ => ⟨trivial, trivial⟩
  | .P p a r, ⟨hp, ha, hr⟩ => by
      have ih := DeepIdx_part l n r hr
      by_cases hpn : p ≤ n
      · simp only [T.part, hpn, ite_true]; exact ⟨ih.1, hp, ha, ih.2⟩
      · simp only [T.part, hpn, ite_false]; exact ⟨⟨hp, ha, ih.1⟩, ih.2⟩

theorem size_add (a b : T) : T.size (T.add a b) = T.size a + T.size b := by
  induction a with
  | Z => simp [T.add, T.size]
  | P p x r _ ih => rw [T.P_add_eq]; simp only [T.size, ih]; omega

theorem size_part (n : Nat) : ∀ t : T,
    T.size (T.part n t).1 + T.size (T.part n t).2 = T.size t
  | .Z => rfl
  | .P p a r => by
      have ih := size_part n r
      by_cases hpn : p ≤ n
      · simp only [T.part, hpn, ite_true, T.size]; omega
      · simp only [T.part, hpn, ite_false, T.size]; omega

/-! Uncollapse. -/

theorem high_ne_Z_lt (q : Nat) (h : T) (hh : T.isNF1 h) (hlow : (T.part q h).2 ≠ T.Z) :
    (T.part q h).1 < h := by
  have he := part_add q h hh
  have hlt := add_lt_add_of_ne_Z (T.part q h).1 (T.part q h).2 hlow
  rwa [he] at hlt

theorem index_head_le_of_NF (q : Nat) (e : T) (he : T.isNF1 e) (hi : T.index_Prop1 q e)
    (p : Nat) (h t : T) (heq : e = T.P p h t) : p ≤ q := by
  subst heq
  cases hi with
  | p _ _ _ hp _ => exact hp

theorem UE_spec (q : Nat) (e : T) (he : T.isNF1 e) (hi : T.index_Prop1 q e) :
    T.early_collapse q (UE q e) = e := by
  cases e with
  | Z => rfl
  | P p h t =>
      obtain ⟨hh, ht, _, hth⟩ := T.isNF1_P_inv p h t he
      have hti : T.index_Prop1 q t := by cases hi with | p _ _ _ _ h' => exact h'
      have htlow : (T.part q t).1 = T.Z := by rw [part_of_index q t hti]
      by_cases hpq : p = q
      · subst hpq
        have hfix := part_first_fixed p h
        have hpe := part_add p h hh
        by_cases hH : (T.part p h).1 = T.Z
        · simp only [UE, hH, ite_true]
          exact early_collapse_of_index p _ hi
        · by_cases hL : (T.part p h).2 = T.Z
          · simp only [UE, hH, hL, ite_true, ite_false]
            have hh1 : (T.part p h).1 = h := by rw [hL, T.add_Z] at hpe; exact hpe
            have hhf : T.part p h = (h, T.Z) := Prod.ext hh1 hL
            have hhZ : h ≠ T.Z := by rw [← hh1]; exact hH
            simp only [T.early_collapse, part_add_split p h t hhf htlow, hhZ, ite_false]
            rw [T.stand, stand_eq_self t ht]
            simp only [hth, ite_true]
          · simp only [UE, hH, hL, ite_true, ite_false]
            have hPlow : (T.part p (T.P p h t)).1 = T.Z := by
              simp only [T.part, Nat.le_refl, ite_true]; exact htlow
            have hlt := high_ne_Z_lt p h hh hL
            simp only [T.early_collapse, part_add_split p _ _ hfix hPlow, hH, ite_false]
            rw [T.stand, stand_eq_self _ he]
            have hnot : ¬ T.head (T.P p h t) ≤ T.P p (T.part p h).1 T.Z := by
              intro hle
              exact lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _ (T.Lt.p_mid _ _ _ _ _ hlt) hle)
            simp only [hnot, ite_false]
      · simp only [UE, hpq, ite_false]
        exact early_collapse_of_index q _ hi

theorem part_fst_index_gt (q : Nat) : ∀ s : T, ∀ p a r, (T.part q s).1 = T.P p a r → q < p := by
  intro s p a r h
  exact part_first_head_gt q p s a r h

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
              exact Or.inl (T.Lt.p_head _ _ _ _ _ _ (Nat.lt_of_le_of_lt hq (hsum p x (Or.inl ⟨rfl, rfl⟩))))
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

theorem UE_NF (q : Nat) (e : T) (he : T.isNF1 e) (hi : T.index_Prop1 q e) :
    T.isNF1 (UE q e) := by
  cases e with
  | Z => exact .z
  | P p h t =>
      obtain ⟨hh, ht, _, _⟩ := T.isNF1_P_inv p h t he
      have hti : T.index_Prop1 q t := by cases hi with | p _ _ _ _ h' => exact h'
      simp only [UE]
      split
      · split
        · exact he
        · split
          · rename_i hL
            have hhf : (T.part q h).1 = h := by
              have := part_add q h hh
              rw [hL, T.add_Z] at this
              exact this
            apply add_NF1_split q h t hh ht _ hti
            intro p' c hs
            rw [← hhf] at hs
            exact part_fst_summand_gt q h p' c hs
          · exact add_NF1_split q _ _ (part_NF q h hh).1 he (part_fst_summand_gt q h) hi
      · exact he

/-- Nesting depth of a target term. -/
def degree : T → Nat
  | .Z => 0
  | .P _ a r => max (degree a + 1) (degree r)

theorem degree_add (a b : T) : degree (T.add a b) = max (degree a) (degree b) := by
  induction a with
  | Z => simp [T.add, degree]
  | P p x r _ ih => rw [T.P_add_eq]; simp only [degree, ih]; omega

theorem degree_part (n : Nat) : ∀ t : T,
    degree (T.part n t).1 ≤ degree t ∧ degree (T.part n t).2 ≤ degree t
  | .Z => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | .P p a r => by
      have ih := degree_part n r
      by_cases hpn : p ≤ n
      · simp only [T.part, hpn, ite_true, degree]; omega
      · simp only [T.part, hpn, ite_false, degree]; omega

theorem UE_degree (q : Nat) (e : T) : degree (UE q e) ≤ degree e := by
  cases e with
  | Z => exact Nat.le_refl _
  | P p h t =>
      have hd := degree_part q h
      simp only [UE]
      split
      · split
        · exact Nat.le_refl _
        · split
          · rw [degree_add]; simp only [degree]; omega
          · rw [degree_add]; simp only [degree]; omega
      · exact Nat.le_refl _

/-! Goodness of uncollapsed terms. -/

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

theorem UE_good (q : Nat) (e : T) (he : T.isNF1 e) (hi : T.index_Prop1 q e) :
    ∀ x ∈ T.G1 q (UE q e), x < UE q e := by
  cases e with
  | Z => intro x hx; cases hx
  | P p h t =>
      obtain ⟨hh, ht, hgh, hth⟩ := T.isNF1_P_inv p h t he
      have hp : p ≤ q := by cases hi with | p _ _ _ h1 _ => exact h1
      have hti : T.index_Prop1 q t := by cases hi with | p _ _ _ _ h1 => exact h1
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
          intro x hx
          simp only [T.G1, Nat.le_refl, ite_true, List.mem_append, List.mem_singleton] at hx
          rcases hx with (rfl | hx) | hx
          · exact hhlt
          · exact lt_trans_thm _ _ _ (hgh x hx) hhlt
          · exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) hhlt
        · by_cases hL : (T.part p h).2 = T.Z
          · simp only [UE, hH, hL, ite_true, ite_false]
            intro x hx
            rw [G1_add, List.mem_append] at hx
            rcases hx with hx | hx
            · exact lt_of_lt_of_le_thm T _ _ _ (hgh x hx) (add_self_le h t)
            · have htZ : t ≠ T.Z := by intro h1; subst h1; cases hx
              exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) (add_lt_add_of_ne_Z h t htZ)
          · simp only [UE, hH, hL, ite_true, ite_false]
            have hLlt : (T.part p h).2 < T.P p h t := by
              have hLi := part_second_index p h
              cases hLe : (T.part p h).2 with
              | Z => exact T.Lt.Z_lt_P _ _ _
              | P r m s =>
                  rw [hLe] at hLi
                  cases hLi with
                  | p _ _ _ hr _ =>
                      rcases Nat.eq_or_lt_of_le hr with rfl | hr
                      · apply T.Lt.p_mid
                        apply hgh m
                        rw [← hpe, G1_add, hLe]
                        exact List.mem_append_right _ (by simp [T.G1])
                      · exact T.Lt.p_head _ _ _ _ _ _ hr
            have hhlt : h < T.add (T.part p h).1 (T.P p h t) := by
              have := add_left_lt (T.part p h).1 _ _ hLlt
              rwa [hpe] at this
            intro x hx
            rw [G1_add, List.mem_append] at hx
            rcases hx with hx | hx
            · exact lt_trans_thm _ _ _ (hgh x (G1_part_fst_subset p p h hh x hx)) hhlt
            · simp only [T.G1, Nat.le_refl, ite_true, List.mem_append, List.mem_singleton] at hx
              rcases hx with (rfl | hx) | hx
              · exact hhlt
              · exact lt_trans_thm _ _ _ (hgh x hx) hhlt
              · exact lt_of_le_of_lt_thm T _ _ _ (htb x hx) hhlt
      · simp only [UE, hpq, ite_false]
        have hpq2 : p < q := by omega
        have htp : T.index_Prop1 p t := by
          cases t with
          | Z => exact .z
          | P p2 g2 r2 =>
              exact isNF1_index p p2 g2 r2 ht (head_le_index p2 p g2 h hth)
        intro x hx
        simp only [T.G1, show ¬ q ≤ p by omega, ite_false] at hx
        rw [index_Prop1_G1_empty p t htp q hpq2] at hx
        cases hx

/-! Uncarding arguments. -/

theorem lt_one_eq_Z (x : T) (h : x < T.P 0 T.Z T.Z) : x = T.Z := by
  cases h with
  | Z_lt_P => rfl
  | p_head _ _ _ _ _ _ h => exact False.elim (Nat.not_lt_zero _ h)
  | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h

theorem small_head_shape (K : Nat) (q : Nat) (h t : T)
    (hlt : T.P q h t < T.P K (T.P 0 T.Z T.Z) T.Z) : q < K ∨ (q = K ∧ h = T.Z) := by
  cases hlt with
  | p_head _ _ _ _ _ _ hq => exact Or.inl hq
  | p_mid _ _ _ _ _ hh => exact Or.inr ⟨rfl, lt_one_eq_Z h hh⟩
  | p_tail _ _ _ _ ht => cases ht

theorem tail_lt_card_one (K : Nat) (t : T) (hth : T.head t ≤ T.P K T.Z T.Z) :
    t < T.P K (T.P 0 T.Z T.Z) T.Z := by
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

theorem cardArg_uncard (K : Nat) (hK : 0 < K) (g : T) (hg : T.isNF1 g) :
    cardArg K (uncardArg K g).1 (uncardArg K g).2 = g := by
  unfold uncardArg
  split
  · rename_i hle
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
        simp only [cardArg, hK, ite_true]
        rfl
    | P q h t =>
        obtain ⟨hh, ht, _, hth⟩ := T.isNF1_P_inv q h t hg
        rcases small_head_shape K q h t hlt with hqK | ⟨rfl, rfl⟩
        · have hgi : T.index_Prop1 q (T.P q h t) := isNF1_index q q h t hg (Nat.le_refl q)
          have hti : T.index_Prop1 q t := by cases hgi with | p _ _ _ _ h1 => exact h1
          simp only [show q ≠ K by omega, ite_false]
          by_cases hq0 : q = 0
          · subst hq0
            simp only [ite_true, cardArg, hqK]
            exact UE_spec 0 _ hg hgi
          · by_cases hh0 : h = T.Z
            · subst hh0
              simp only [hq0, ite_true, ite_false, cardArg, hqK]
              rw [UE_spec q t ht hti, T.stand, stand_eq_self t ht]
              simp only [hth, ite_true]
            · simp only [hq0, hh0, ite_false, cardArg, hqK, ite_true]
              rw [UE_spec q _ hg hgi, T.stand, stand_eq_self _ hg]
              have hnot : ¬ T.head (T.P q h t) ≤ T.P q T.Z T.Z := by
                intro hle
                have hZh : T.Z < h := by
                  cases h with
                  | Z => exact False.elim (hh0 rfl)
                  | P _ _ _ => exact T.Lt.Z_lt_P _ _ _
                exact lt_irrefl_thm _ (lt_of_lt_of_le_thm T _ _ _ (T.Lt.p_mid _ _ _ _ _ hZh) hle)
              simp only [hnot, ite_false]
        · simp only [ite_true, cardArg, Nat.lt_irrefl, ite_false]
          simp only [tail_lt_card_one q t hth, and_self, ite_true]

theorem DeepIdx_UE (l q : Nat) (e : T) (he : DeepIdx l e) : DeepIdx l (UE q e) := by
  cases e with
  | Z => exact he
  | P p h t =>
      have hp := DeepIdx_part l q h he.2.1
      simp only [UE]
      split
      · split
        · exact he
        · split
          · exact DeepIdx_add l h t he.2.1 he.2.2
          · exact DeepIdx_add l _ _ hp.1 he
      · exact he

theorem G1_le_Z_of_head (K : Nat) (t : T) (ht : T.isNF1 t) (hth : T.head t ≤ T.P K T.Z T.Z) :
    ∀ x ∈ T.G1 K t, x < t := by
  intro x hx
  have hti : T.index_Prop1 K t := by
    cases t with
    | Z => exact .z
    | P p2 g2 r2 => exact isNF1_index K p2 g2 r2 ht (head_le_index p2 K g2 T.Z hth)
  have hxZ := G1_below_head K T.Z (fun y hy => by cases hy) t ht hth hti x hx
  have htZ : t ≠ T.Z := by intro h; subst h; cases hx
  rcases hxZ with h | h
  · exact absurd h lt_Z_inv
  · subst h
    cases t with
    | Z => exact False.elim (htZ rfl)
    | P _ _ _ => exact T.Lt.Z_lt_P _ _ _

theorem uncard_props (K : Nat) (hK : 0 < K) (g : T) (hg : T.isNF1 g)
    (hgg : ∀ x ∈ T.G1 K g, x < g) :
    (uncardArg K g).1 ≤ K ∧ T.isNF1 (uncardArg K g).2 ∧
      (∀ x ∈ T.G1 (uncardArg K g).1 (uncardArg K g).2, x < (uncardArg K g).2) ∧
      degree (uncardArg K g).2 ≤ degree g ∧
      (∀ l, DeepIdx l g → DeepIdx l (uncardArg K g).2) := by
  unfold uncardArg
  split
  · exact ⟨Nat.le_refl _, hg, hgg, Nat.le_refl _, fun _ h => h⟩
  · rename_i hnle
    have hlt := lt_of_not_le _ _ hnle
    cases g with
    | Z => exact ⟨Nat.zero_le _, .z, fun x hx => (by simp [T.G1] at hx), Nat.le_refl _, fun _ _ => trivial⟩
    | P q h t =>
        obtain ⟨hh, ht, _, hth⟩ := T.isNF1_P_inv q h t hg
        rcases small_head_shape K q h t hlt with hqK | ⟨rfl, rfl⟩
        · have hgi : T.index_Prop1 q (T.P q h t) := isNF1_index q q h t hg (Nat.le_refl q)
          have hti : T.index_Prop1 q t := by cases hgi with | p _ _ _ _ h1 => exact h1
          simp only [show q ≠ K by omega, ite_false]
          by_cases hq0 : q = 0
          · subst hq0
            simp only [ite_true]
            exact ⟨Nat.zero_le _, UE_NF 0 _ hg hgi, UE_good 0 _ hg hgi, UE_degree 0 _,
              fun l hl => DeepIdx_UE l 0 _ hl⟩
          · by_cases hh0 : h = T.Z
            · subst hh0
              simp only [hq0, ite_true, ite_false]
              refine ⟨Nat.le_of_lt hqK, UE_NF q t ht hti, UE_good q t ht hti,
                Nat.le_trans (UE_degree q t) (by simp only [degree]; omega),
                fun l hl => DeepIdx_UE l q t hl.2.2⟩
            · simp only [hq0, hh0, ite_false]
              exact ⟨Nat.le_of_lt hqK, UE_NF q _ hg hgi, UE_good q _ hg hgi, UE_degree q _,
                fun l hl => DeepIdx_UE l q _ hl⟩
        · simp only [ite_true]
          exact ⟨Nat.le_refl _, ht, G1_le_Z_of_head q t ht hth,
            by simp only [degree]; omega, fun _ hl => hl.2.2⟩

theorem uncard_mono (K : Nat) (hK : 0 < K) (g1 g2 : T) (hg1 : T.isNF1 g1)
    (hgg1 : ∀ x ∈ T.G1 K g1, x < g1) (hg2 : T.isNF1 g2) (hgg2 : ∀ x ∈ T.G1 K g2, x < g2)
    (h : g2 ≤ g1) :
    T.P (uncardArg K g2).1 (uncardArg K g2).2 T.Z ≤ T.P (uncardArg K g1).1 (uncardArg K g1).2 T.Z := by
  obtain ⟨hp1, hc1, hgc1, _⟩ := uncard_props K hK g1 hg1 hgg1
  obtain ⟨hp2, hc2, hgc2, _⟩ := uncard_props K hK g2 hg2 hgg2
  have he1 := cardArg_uncard K hK g1 hg1
  have he2 := cardArg_uncard K hK g2 hg2
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
      · have hgc2b : ∀ x ∈ T.G1 (uncardArg K g1).1 (uncardArg K g2).2, x < (uncardArg K g2).2 := by
          rw [hp]; exact hgc2
        have he2b := he2
        rw [← hp] at he2b
        have hc3 := cardArg_lt_same K (uncardArg K g1).1 _ _ hc1 hgc1 hc2 hgc2b hc
        rw [he1, he2b] at hc3
        exact hc3
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

theorem UC_degree (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d → degree (UC K d) ≤ degree d
  | .Z, _ => Nat.le_refl _
  | .P q g r, hd => by
      obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
      have ih := UC_degree K hK r hr
      simp only [UC]
      split
      · simp only [degree]; omega
      · rename_i hq
        have hgg' : ∀ x ∈ T.G1 K g, x < g :=
          fun x hx => hgg x (G1_antitone q K (by omega) g x hx)
        have hdeg := (uncard_props K hK g hg hgg').2.2.2.1
        simp only [degree]; omega

theorem UC_DeepIdx (K l : Nat) (hK : 0 < K) (hKl : K ≤ l) : ∀ d : T, T.isNF1 d →
    DeepIdx l d → DeepIdx l (UC K d)
  | .Z, _, _ => trivial
  | .P q g r, hd, ⟨hql, hgl, hrl⟩ => by
      obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
      have ih := UC_DeepIdx K l hK hKl r hr hrl
      simp only [UC]
      split
      · exact ⟨hql, hgl, ih⟩
      · rename_i hq
        have hgg' : ∀ x ∈ T.G1 K g, x < g :=
          fun x hx => hgg x (G1_antitone q K (by omega) g x hx)
        obtain ⟨hp, _, _, _, hdi⟩ := uncard_props K hK g hg hgg'
        exact ⟨Nat.le_trans hp hKl, hdi l hgl, ih⟩

theorem UC_spec (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → K ≤ p) → T.card_times K (UC K d) = d
  | .Z, _, _ => rfl
  | .P q g r, hd, hidx => by
      obtain ⟨hg, hr, _, _⟩ := T.isNF1_P_inv q g r hd
      have ih := UC_spec K hK r hr (fun p c hs => hidx p c (Or.inr hs))
      have hKq := hidx q g (Or.inl ⟨rfl, rfl⟩)
      simp only [UC]
      split
      · rename_i hq
        rw [card_times_P, Nat.max_eq_left (Nat.le_of_lt hq), ih]
        unfold cardArg
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · rename_i hq
        have hqK : q = K := by omega
        subst hqK
        have hp := (uncard_props q hK g hg (T.isNF1_P_inv q g r hd).2.2.1).1
        rw [card_times_P, Nat.max_eq_right hp, cardArg_uncard q hK g hg, ih]

/-- The head summand produced by uncarding. -/
def ucHead (K q : Nat) (g : T) : Nat × T := if K < q then (q, g) else uncardArg K g

theorem UC_P (K q : Nat) (g r : T) :
    UC K (T.P q g r) = T.P (ucHead K q g).1 (ucHead K q g).2 (UC K r) := by
  simp only [UC, ucHead]
  split <;> rfl

theorem ucHead_props (K : Nat) (hK : 0 < K) (q : Nat) (g : T) (hg : T.isNF1 g)
    (hgg : ∀ x ∈ T.G1 q g, x < g) (hKq : K ≤ q) :
    T.isNF1 (ucHead K q g).2 ∧ (∀ x ∈ T.G1 (ucHead K q g).1 (ucHead K q g).2, x < (ucHead K q g).2) := by
  unfold ucHead
  split
  · exact ⟨hg, hgg⟩
  · have hqK : q = K := by omega
    subst hqK
    obtain ⟨_, h1, h2, _⟩ := uncard_props q hK g hg hgg
    exact ⟨h1, h2⟩

theorem ucHead_mono (K : Nat) (hK : 0 < K) (q1 q2 : Nat) (g1 g2 : T)
    (hg1 : T.isNF1 g1) (hgg1 : ∀ x ∈ T.G1 q1 g1, x < g1) (hK1 : K ≤ q1)
    (hg2 : T.isNF1 g2) (hgg2 : ∀ x ∈ T.G1 q2 g2, x < g2) (hK2 : K ≤ q2)
    (h : T.P q2 g2 T.Z ≤ T.P q1 g1 T.Z) :
    T.P (ucHead K q2 g2).1 (ucHead K q2 g2).2 T.Z ≤ T.P (ucHead K q1 g1).1 (ucHead K q1 g1).2 T.Z := by
  have hq21 := head_le_index q2 q1 g2 g1 h
  unfold ucHead
  by_cases h2 : K < q2
  · rw [ite_eq_left h2, ite_eq_left (Nat.lt_of_lt_of_le h2 hq21)]
    exact h
  · rw [ite_eq_right h2]
    have hq2 : q2 = K := by omega
    subst hq2
    have hp2 := (uncard_props q2 hK g2 hg2 hgg2).1
    by_cases h1 : q2 < q1
    · rw [ite_eq_left h1]
      exact Or.inl (T.Lt.p_head _ _ _ _ _ _ (Nat.lt_of_le_of_lt hp2 h1))
    · rw [ite_eq_right h1]
      have hq1 : q1 = q2 := by omega
      subst hq1
      apply uncard_mono q1 hK g1 g2 hg1 hgg1 hg2 hgg2
      rcases h with h | h
      · cases h with
        | p_head _ _ _ _ _ _ h' => exact absurd h' (Nat.lt_irrefl _)
        | p_mid _ _ _ _ _ h' => exact Or.inl h'
        | p_tail _ _ _ _ h' => cases h'
      · injection h with _ h' _; exact Or.inr h'

theorem UC_NF (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → K ≤ p) → T.isNF1 (UC K d)
  | .Z, _, _ => .z
  | .P q g r, hd, hidx => by
      obtain ⟨hg, hr, hgg, hrh⟩ := T.isNF1_P_inv q g r hd
      have hKq := hidx q g (Or.inl ⟨rfl, rfl⟩)
      have ih := UC_NF K hK r hr (fun p c hs => hidx p c (Or.inr hs))
      obtain ⟨hc, hgc⟩ := ucHead_props K hK q g hg hgg hKq
      rw [UC_P]
      refine .p _ _ _ hc ih hgc ?_
      cases r with
      | Z => exact T.Z_le _
      | P q2 g2 r2 =>
          obtain ⟨hg2, _, hgg2, _⟩ := T.isNF1_P_inv q2 g2 r2 hr
          rw [UC_P]
          exact ucHead_mono K hK q q2 g g2 hg hgg hKq hg2 hgg2
            (hidx q2 g2 (Or.inr (Or.inl ⟨rfl, rfl⟩))) hrh

theorem UC_index (K : Nat) (hK : 0 < K) : ∀ d : T, T.isNF1 d →
    (∀ p c, IsSummand p c d → p = K) → T.index_Prop1 K (UC K d)
  | .Z, _, _ => .z
  | .P q g r, hd, hidx => by
      obtain ⟨hg, hr, hgg, _⟩ := T.isNF1_P_inv q g r hd
      have hqK := hidx q g (Or.inl ⟨rfl, rfl⟩)
      subst hqK
      simp only [UC, Nat.lt_irrefl, ite_false]
      exact .p _ _ _ (uncard_props q hK g hg hgg).1
        (UC_index q hK r hr (fun p c hs => hidx p c (Or.inr hs)))

/-! Nested parts. -/

theorem part_part_fst (n m : Nat) (hnm : n ≤ m) : ∀ s : T,
    (T.part m (T.part n s).1).1 = (T.part m s).1
  | .Z => rfl
  | .P p a r => by
      have ih := part_part_fst n m hnm r
      by_cases hpn : p ≤ n
      · have hpm : p ≤ m := Nat.le_trans hpn hnm
        simp only [T.part, hpn, hpm, ite_true, ih]
      · by_cases hpm : p ≤ m
        · simp only [T.part, hpn, hpm, ite_true, ite_false, ih]
        · simp only [T.part, hpn, hpm, ite_false, ih]

theorem part_part_snd (n m : Nat) (hnm : n ≤ m) : ∀ s : T,
    (T.part n (T.part m s).2).2 = (T.part n s).2
  | .Z => rfl
  | .P p a r => by
      have ih := part_part_snd n m hnm r
      by_cases hpn : p ≤ n
      · have hpm : p ≤ m := Nat.le_trans hpn hnm
        simp only [T.part, hpn, hpm, ite_true, ih]
      · by_cases hpm : p ≤ m
        · simp only [T.part, hpn, hpm, ite_true, ite_false, ih]
        · simp only [T.part, hpn, hpm, ite_false, ih]

theorem part_comm (n m : Nat) (hnm : n ≤ m) : ∀ s : T,
    (T.part m (T.part n s).1).2 = (T.part n (T.part m s).2).1
  | .Z => rfl
  | .P p a r => by
      have ih := part_comm n m hnm r
      by_cases hpn : p ≤ n
      · have hpm : p ≤ m := Nat.le_trans hpn hnm
        simp only [T.part, hpn, hpm, ite_true, ih]
      · by_cases hpm : p ≤ m
        · simp only [T.part, hpn, hpm, ite_true, ite_false, ih]
        · simp only [T.part, hpn, hpm, ite_false, ih]

/-- Summands of index exactly `m`. -/
def idxPart (m : Nat) (c : T) : T := (T.part (m - 1) (T.part m c).2).1

theorem part_snd_split (m : Nat) (c : T) (hc : T.isNF1 c) :
    (T.part m c).2 = T.add (idxPart m c) (T.part (m - 1) c).2 := by
  have hL := (part_NF m c hc).2
  have := part_add (m - 1) _ hL
  rw [part_part_snd (m - 1) m (Nat.sub_le m 1)] at this
  exact this.symm

end LegacyTranslation
